#[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
pub(crate) use std::time::{Duration, Instant};

#[cfg(all(target_arch = "wasm32", target_os = "unknown"))]
pub(crate) use std::time::Duration;

#[cfg(all(target_arch = "wasm32", target_os = "unknown"))]
#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) struct Instant(f64);

#[cfg(all(target_arch = "wasm32", target_os = "unknown"))]
impl Instant {
    pub(crate) fn now() -> Self {
        Self(js_sys::Date::now())
    }

    pub(crate) fn elapsed(self) -> Duration {
        Duration::from_secs_f64(((js_sys::Date::now() - self.0) / 1_000.0).max(0.0))
    }
}
