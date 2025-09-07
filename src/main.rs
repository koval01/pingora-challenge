use std::collections::HashSet;
use std::path::PathBuf;
use std::sync::Arc;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use askama::Template;
use async_trait::async_trait;
use base64::{engine::general_purpose, Engine as _};
use chrono::Utc;
use dashmap::DashMap;
use hostname;
use once_cell::sync::Lazy;
use pingora::prelude::*;
use pingora::cache::eviction::simple_lru::Manager;
use pingora::cache::lock::{CacheKeyLockImpl, CacheLock};
use pingora::cache::predictor::Predictor;
use pingora::cache::MemCache;
use pingora::Error;
use pingora::http::ResponseHeader;
use pingora::cache::{CacheMeta, CacheOptionOverrides, CachePhase, ForcedInvalidationKind, HitHandler, NoCacheReason, RespCacheable, VarianceBuilder};
use pingora::cache::cache_control::CacheControl;
use pingora::cache::filters::resp_cacheable;
use pingora::cache::key::HashBinary;
use pingora::protocols::http::error_resp::gen_error_response;
use pingora::protocols::l4::socket::SocketAddr;
use pingora::proxy::FailToProxy;
use serde_json::json;
use sha1::{Digest, Sha1};
use sha1;
use base64;
use hex;

use altcha_lib_rs::{create_challenge, ChallengeOptions, verify_json_solution};
use altcha_lib_rs::algorithm::AltchaAlgorithm;
use http::header::VARY;
use pingora_cache::CacheMetaDefaults;
use tokio::io::AsyncReadExt;

pub struct LB(Arc<LoadBalancer<RoundRobin>>);

fn generate_instance_id() -> String {
    let hostname = hostname::get()
        .ok()
        .and_then(|h| h.into_string().ok())
        .unwrap_or_else(|| "unknown".to_string());
    let mut hasher = Sha1::new();
    hasher.update(hostname.as_bytes());
    let result = hasher.finalize();
    hex::encode(&result[..4])
}

fn generate_request_id(client_ip: Option<&SocketAddr>, instance_id: &str) -> String {
    let now = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default();
    let timestamp = now.as_nanos();

    let client_hash = client_ip
        .and_then(|s| s.as_inet())
        .map(|inet| {
            let mut hasher = Sha1::new();
            hasher.update(inet.ip().to_string().as_bytes());
            let hexed = hex::encode(hasher.finalize());
            hexed[..8].to_string()
        })
        .unwrap_or_else(|| "00000000".to_string());

    format!("{:x}-{}-{}", timestamp, client_hash, instance_id)
}

fn format_duration_us(micros: u128) -> String {
    if micros < 1_000 {
        format!("{}us", micros)
    } else {
        let ms = micros as f64 / 1_000.0;
        format!("{:.1}ms", ms)
    }
}

static INSTANCE_ID: Lazy<String> = Lazy::new(|| generate_instance_id());

static HMAC_SECRET: Lazy<String> = Lazy::new(|| String::from("0a961724ddf8cb544a64319b19c5d7bf"));

static STATIC_CACHE: Lazy<DashMap<String, Vec<u8>>> = Lazy::new(DashMap::new);
static CACHE_BACKEND: Lazy<MemCache> = Lazy::new(MemCache::new);
const CACHE_DEFAULT: CacheMetaDefaults = CacheMetaDefaults::new(|_| Some(Duration::from_secs(900)), 60, 60);
static CACHE_PREDICTOR: Lazy<Predictor<32>> = Lazy::new(|| Predictor::new(10, None));
static EVICTION_MANAGER: Lazy<Manager> = Lazy::new(|| Manager::new(536_870_912));
static CACHE_LOCK: Lazy<Box<CacheKeyLockImpl>> = Lazy::new(|| CacheLock::new_boxed(Duration::from_secs(3)));
static CACHE_VARY_ALLOWED_HEADERS: Lazy<Option<HashSet<&'static str>>> = Lazy::new(|| {
    Some(vec!["accept", "accept-encoding"].into_iter().collect())
});

pub struct CacheCTX {
    upstream_status: Option<u16>,
    request_id: Option<String>,
    pub origin_start: Option<Instant>,
    pub origin_duration: Option<u128>,
    pub cache_start: Option<Instant>,
    pub cache_duration: Option<u128>,
}

#[derive(Template)]
#[template(path = "challenge.html")]
struct ChallengeTemplate<'a> {
    domain: &'a str,
    request_id: &'a str,
    client_ip: &'a str,
}

async fn render_challenge(session: &mut Session, ctx: &mut CacheCTX) -> Result<()> {
    let client_ip_string = session
        .client_addr()
        .and_then(|s| s.as_inet().map(|i| i.ip().to_string()))
        .unwrap_or_else(|| "0.0.0.0".to_string());
    let client_ip = client_ip_string.as_str();

    if ctx.request_id.is_none() {
        ctx.request_id = Some(generate_request_id(session.client_addr(), &INSTANCE_ID));
    }
    let request_id_ref = ctx.request_id.as_ref().map(|s| s.as_str()).unwrap_or("");
    let domain = match session.get_header("host") {
        Some(h) => h.to_str().unwrap_or("unknown"),
        None => "unknown",
    };

    let tpl = ChallengeTemplate { domain, request_id: request_id_ref, client_ip };

    let body = tpl.render().map_err(|e| {
        Error::explain(CustomCode("Template error", 500), format!("Askama render error: {}", e))
    })?;

    let mut resp = ResponseHeader::build(200, Some(0))?;
    resp.insert_header("content-type", "text/html; charset=utf-8")?;
    resp.insert_header("cache-control", "no-store")?;
    inject_standard_headers(
        &mut resp,
        request_id_ref,
        session.cache.lock_duration().map(|d| d.as_millis()),
        ctx.upstream_status,
        if session.cache.enabled() { "MISS" } else { "NO-CACHE" },
        ctx.origin_duration.unwrap_or(0),
        0,
    )?;

    let cache_start = Instant::now();
    ctx.cache_start = Some(cache_start);
    ctx.cache_duration = Some(cache_start.elapsed().as_micros());

    let server_timing_value = format!(
        "cache;dur={};origin;dur={}",
        format_duration_us(ctx.cache_duration.unwrap_or(0)),
        format_duration_us(ctx.origin_duration.unwrap_or(0))
    );
    resp.insert_header("server-timing", server_timing_value)?;

    resp.set_content_length(body.as_bytes().len())?;
    session.write_response_header(Box::new(resp), false).await?;
    session.write_response_body(Some(body.into()), true).await?;
    Ok(())
}

fn check_challenge_cookie(session: &Session) -> bool {
    let cookie_hdr = session.get_header_bytes("cookie");
    if cookie_hdr.is_empty() {
        return false;
    }

    if let Ok(cookie_str) = std::str::from_utf8(cookie_hdr) {
        for part in cookie_str.split(';') {
            let trimmed = part.trim();
            if let Some(rest) = trimmed.strip_prefix("pingora_challenge=") {
                return validate_challenge(rest);
            }
        }
    }

    false
}

fn validate_challenge(value: &str) -> bool {
    if value.is_empty() {
        return false;
    }

    let decoded_bytes = match general_purpose::STANDARD.decode(value) {
        Ok(b) => b,
        Err(_) => return false,
    };

    let decoded_str = match String::from_utf8(decoded_bytes) {
        Ok(s) => s,
        Err(_) => return false,
    };

    match verify_json_solution(&decoded_str, &**HMAC_SECRET, true) {
        Ok(_) => true,
        Err(_) => false,
    }
}

async fn handle_challenge(session: &mut Session, ctx: &mut CacheCTX) -> Result<()> {
    let origin_start = Instant::now();
    ctx.origin_start = Some(origin_start);

    let challenge = create_challenge(ChallengeOptions {
        algorithm: Option::from(AltchaAlgorithm::Sha512),
        hmac_key: &**HMAC_SECRET,
        expires: Some(Utc::now() + chrono::Duration::minutes(1)),
        ..Default::default()
    }).map_err(|e| Error::explain(CustomCode("Challenge error", 500), format!("{:?}", e)))?;

    let body = json!(challenge).to_string();

    let mut resp = ResponseHeader::build(200, Some(0))?;
    ctx.origin_duration = Some(origin_start.elapsed().as_micros());
    resp.insert_header("content-type", "application/json; charset=utf-8")?;
    resp.insert_header("cache-control", "no-store")?;
    inject_standard_headers(
        &mut resp,
        ctx.request_id.as_ref().map(|s| s.as_str()).unwrap_or("unknown"),
        session.cache.lock_duration().map(|d| d.as_millis()),
        ctx.upstream_status,
        "MISS",
        ctx.origin_duration.unwrap_or(0),
        0,
    )?;
    resp.set_content_length(body.as_bytes().len())?;

    session.write_response_header(Box::new(resp), false).await?;
    session.write_response_body(Some(body.into()), true).await?;
    Ok(())
}

async fn serve_static_cached(session: &mut Session, ctx: &mut CacheCTX) -> Result<Option<(ResponseHeader, Vec<u8>)>> {
    let path = session.req_header().uri.path();
    if !path.starts_with("/__pingora/static/") {
        return Ok(None);
    }

    let key = path["/__pingora/static/".len()..].to_string();
    let cache_start = Instant::now();
    ctx.cache_start = Some(cache_start);

    if let Some(cached) = STATIC_CACHE.get(&key) {
        let mut resp = ResponseHeader::build(200, Some(0))?;
        let content_type = match path.rsplit('.').next() {
            Some("js") => "application/javascript",
            Some("css") => "text/css",
            Some("html") => "text/html",
            _ => "application/octet-stream",
        };
        ctx.cache_duration = Some(cache_start.elapsed().as_micros());
        resp.insert_header("content-type", content_type)?;
        resp.insert_header("cache-control", "max-age=31536000")?;
        inject_standard_headers(
            &mut resp,
            ctx.request_id.as_ref().map(|s| s.as_str()).unwrap_or("unknown"),
            session.cache.lock_duration().map(|d| d.as_millis()),
            ctx.upstream_status,
            "HIT",
            ctx.origin_duration.unwrap_or(0),
            ctx.cache_duration.unwrap_or(0),
        )?;
        resp.set_content_length(cached.len())?;
        return Ok(Some((resp, cached.clone())));
    }

    let file_path = PathBuf::from("static").join(&key);
    if !file_path.exists() {
        return Ok(None);
    }

    let mut file = tokio::fs::File::open(&file_path).await
        .map_err(|e| Error::explain(CustomCode("IO Error", 500), format!("Failed to open file: {}", e)))?;
    let mut content = Vec::new();
    file.read_to_end(&mut content).await
        .map_err(|e| Error::explain(CustomCode("IO Error", 500), format!("Failed to read file: {}", e)))?;

    STATIC_CACHE.insert(key, content.clone());
    ctx.cache_duration = Some(cache_start.elapsed().as_micros());

    let mut resp = ResponseHeader::build(200, Some(0))?;
    let content_type = match path.rsplit('.').next() {
        Some("js") => "application/javascript",
        Some("css") => "text/css",
        Some("html") => "text/html",
        _ => "application/octet-stream",
    };
    resp.insert_header("content-type", content_type)?;
    resp.insert_header("cache-control", "max-age=31536000")?;
    resp.set_content_length(content.len())?;

    inject_standard_headers(
        &mut resp,
        ctx.request_id.as_ref().map(|s| s.as_str()).unwrap_or("unknown"),
        session.cache.lock_duration().map(|d| d.as_millis()),
        ctx.upstream_status,
        "HIT",
        ctx.origin_duration.unwrap_or(0),
        ctx.cache_duration.unwrap_or(0),
    )?;

    Ok(Some((resp, content)))
}

fn inject_standard_headers(
    resp: &mut ResponseHeader,
    request_id: &str,
    cache_lock_ms: Option<u128>,
    upstream_status: Option<u16>,
    cache_phase: &str,
    origin_duration: u128,
    cache_duration: u128,
) -> Result<()> {
    resp.insert_header("server", "pingora")?;
    resp.insert_header("x-pingora-ray", request_id)?;
    resp.insert_header("x-pingora-cache", cache_phase)?;
    if let Some(ms) = cache_lock_ms {
        resp.insert_header("x-cache-lock-time-ms", format!("{}", ms))?;
    }
    if let Some(status) = upstream_status {
        resp.insert_header("x-upstream-status", status.to_string())?;
    }
    let server_timing_value = format!(
        "cache;dur={};origin;dur={}",
        format_duration_us(cache_duration),
        format_duration_us(origin_duration)
    );
    resp.insert_header("server-timing", server_timing_value)?;
    Ok(())
}

#[async_trait]
impl ProxyHttp for LB {
    type CTX = CacheCTX;

    fn new_ctx(&self) -> Self::CTX {
        CacheCTX {
            upstream_status: None,
            request_id: None,
            origin_start: None,
            origin_duration: None,
            cache_start: None,
            cache_duration: None,
        }
    }

    async fn upstream_peer(&self, _session: &mut Session, ctx: &mut Self::CTX) -> Result<Box<HttpPeer>> {
        ctx.origin_start = Some(Instant::now());

        let upstream = self.0.select(b"", 256).unwrap();
        let peer = Box::new(HttpPeer::new(upstream, true, "opensource.diia.gov.ua".to_string()));

        Ok(peer)
    }

    fn request_cache_filter(&self, session: &mut Session, _ctx: &mut Self::CTX) -> Result<()> {
        if session.get_header_bytes("x-bypass-cache") != b"" {
            return Ok(());
        }

        let eviction = session.req_header().headers.get("x-eviction").map(|_| {
            &*EVICTION_MANAGER as &'static (dyn pingora_cache::eviction::EvictionManager + Sync)
        });
        let lock = session.req_header().headers.get("x-lock").map(|_| CACHE_LOCK.as_ref());

        let mut overrides = CacheOptionOverrides::default();
        overrides.wait_timeout = Some(Duration::from_secs(2));
        session.cache.enable(
            &*CACHE_BACKEND,
            eviction,
            Some(&*CACHE_PREDICTOR),
            lock,
            Some(overrides),
        );

        if let Some(max_file_size_hdr) = session.req_header().headers.get("x-cache-max-file-size-bytes") {
            if let Some(bytes) = max_file_size_hdr.to_str().ok().and_then(|s| s.parse::<usize>().ok()) {
                session.cache.set_max_file_size_bytes(bytes);
            }
        }

        Ok(())
    }

    async fn cache_hit_filter(
        &self,
        session: &mut Session,
        _meta: &CacheMeta,
        _hit_handler: &mut HitHandler,
        is_fresh: bool,
        _ctx: &mut Self::CTX,
    ) -> Result<Option<ForcedInvalidationKind>> {
        if !check_challenge_cookie(session) {
            render_challenge(session, _ctx).await?;
            return Ok(Some(ForcedInvalidationKind::ForceMiss));
        }

        if session.get_header_bytes("x-force-miss") != b"" {
            return Ok(Some(ForcedInvalidationKind::ForceMiss));
        }

        if !is_fresh {
            return Ok(None);
        }

        if session.get_header_bytes("x-force-expire") != b"" {
            return Ok(Some(ForcedInvalidationKind::ForceExpired));
        }
        Ok(None)
    }

    fn response_cache_filter(
        &self,
        _session: &Session,
        resp: &ResponseHeader,
        _ctx: &mut Self::CTX,
    ) -> Result<RespCacheable> {
        let cc = CacheControl::from_resp_headers(resp);
        Ok(resp_cacheable(cc.as_ref(), resp.clone(), false, &CACHE_DEFAULT))
    }

    fn cache_vary_filter(
        &self,
        meta: &CacheMeta,
        _ctx: &mut Self::CTX,
        req: &RequestHeader,
    ) -> Option<HashBinary> {
        let mut key = VarianceBuilder::new();

        let vary_headers_lowercased: Vec<String> = meta
            .headers()
            .get_all(VARY)
            .iter()
            .flat_map(|vary_header| vary_header.to_str().ok())
            .flat_map(|vary_header| vary_header.split(','))
            .map(|s| s.trim().to_lowercase())
            .filter(|header_name| {
                CACHE_VARY_ALLOWED_HEADERS
                    .as_ref()
                    .map(|al| al.contains(header_name.as_str()))
                    .unwrap_or(true)
            })
            .collect();

        for header_name in vary_headers_lowercased.iter() {
            key.add_value(
                header_name,
                req.headers
                    .get(header_name)
                    .map(|v| v.as_bytes())
                    .unwrap_or(&[]),
            );
        }

        key.finalize()
    }

    async fn upstream_request_filter(
        &self,
        session: &mut Session,
        upstream_request: &mut RequestHeader,
        ctx: &mut Self::CTX,
    ) -> Result<()> {
        if ctx.request_id.is_none() {
            ctx.request_id = Some(generate_request_id(session.client_addr(), &INSTANCE_ID));
        }

        if let Some((resp, body)) = serve_static_cached(session, ctx).await? {
            session.write_response_header(Box::new(resp), false).await?;
            session.write_response_body(Some(body.into()), true).await?;
            return Err(Error::explain(CustomCode("OK", 200), "served static file"));
        }

        let path = upstream_request.uri.path();

        if path == "/__pingora/challenge" {
            handle_challenge(session, ctx).await?;
            return Err(Error::explain(CustomCode("OK", 200), "custom challenge route"));
        }

        if !check_challenge_cookie(session) {
            render_challenge(session, ctx).await?;
            return Err(Error::explain(CustomCode("Forbidden", 403), "challenge sent"));
        }

        ctx.origin_start = Some(Instant::now());
        upstream_request.insert_header("host", "opensource.diia.gov.ua")?;
        Ok(())
    }

    async fn response_filter(
        &self,
        session: &mut Session,
        upstream_response: &mut ResponseHeader,
        ctx: &mut Self::CTX,
    ) -> Result<()>
    where
        Self::CTX: Send + Sync,
    {
        upstream_response.remove_header("server");

        if ctx.request_id.is_none() {
            ctx.request_id = Some(generate_request_id(session.client_addr(), &INSTANCE_ID));
        }

        if let Some(start) = ctx.origin_start {
            ctx.origin_duration = Some(start.elapsed().as_micros());
        }

        let cache_phase = if session.cache.enabled() {
            match session.cache.phase() {
                CachePhase::Hit => "HIT",
                CachePhase::Miss => "MISS",
                CachePhase::Stale => "STALE",
                CachePhase::StaleUpdating => "STALE-UPDATING",
                CachePhase::Expired => "EXPIRED",
                CachePhase::Revalidated | CachePhase::RevalidatedNoCache(_) => "REVALIDATED",
                _ => "INVALID",
            }
        } else {
            match session.cache.phase() {
                CachePhase::Disabled(NoCacheReason::Deferred) => "DEFERRED",
                _ => "NO-CACHE",
            }
        };

        inject_standard_headers(
            upstream_response,
            ctx.request_id.as_ref().map(|s| s.as_str()).unwrap_or("unknown"),
            session.cache.lock_duration().map(|d| d.as_millis()),
            ctx.upstream_status,
            cache_phase,
            ctx.origin_duration.unwrap_or(0),
            ctx.cache_duration.unwrap_or(0),
        )?;

        Ok(())
    }

    async fn fail_to_proxy(
        &self,
        session: &mut Session,
        e: &Error,
        ctx: &mut Self::CTX,
    ) -> FailToProxy
    where
        Self::CTX: Send + Sync,
    {
        let code = match e.etype() {
            HTTPStatus(code) => *code,
            _ => match e.esource() {
                ErrorSource::Upstream => 502,
                ErrorSource::Downstream => match e.etype() {
                    WriteError | ReadError | ConnectionClosed => 0,
                    _ => 400,
                },
                ErrorSource::Internal | ErrorSource::Unset => 500,
            },
        };

        if code > 0 {
            let mut resp = gen_error_response(code);

            let request_id = ctx.request_id.as_deref().unwrap_or("unknown");
            let cache_lock_ms = session.cache.lock_duration().map(|d| d.as_millis());
            let origin_duration = ctx.origin_duration.unwrap_or(0);
            let upstream_status = ctx.upstream_status;

            let _ = inject_standard_headers(
                &mut resp,
                request_id,
                cache_lock_ms,
                upstream_status,
                "NO-CACHE",
                origin_duration,
                0,
            );

            let _ = session
                .write_response_header(Box::new(resp), true)
                .await
                .map_err(|e| {
                    println!("failed to send error response to downstream: {e}");
                    e
                });
        }

        FailToProxy {
            error_code: code,
            can_reuse_downstream: false,
        }
    }

    fn should_serve_stale(
        &self,
        _session: &mut Session,
        _ctx: &mut Self::CTX,
        error: Option<&Error>,
    ) -> bool {
        error.map_or(true, |e| e.esource() == &ErrorSource::Upstream)
    }

    fn is_purge(&self, session: &Session, _ctx: &CacheCTX) -> bool {
        session.req_header().method == "PURGE"
    }
}

fn main() {
    let mut my_server = Server::new(None).unwrap();
    my_server.bootstrap();

    let mut upstreams =
        LoadBalancer::try_from_iter(["195.189.240.104:443", "195.189.240.105:443"]).unwrap();

    let hc = TcpHealthCheck::new();
    upstreams.set_health_check(hc);
    upstreams.health_check_frequency = Some(Duration::from_secs(1));

    let background = background_service("health check", upstreams);
    let upstreams = background.task();

    let mut lb = http_proxy_service(&my_server.configuration, LB(upstreams));
    lb.add_tcp("0.0.0.0:6188");

    my_server.add_service(background);
    my_server.add_service(lb);
    my_server.run_forever();
}
