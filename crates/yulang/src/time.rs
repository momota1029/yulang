#[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
pub(crate) use std::time::{Duration, Instant};

#[cfg(all(target_arch = "wasm32", target_os = "unknown"))]
pub(crate) use std::time::Duration;

#[cfg(all(target_arch = "wasm32", target_os = "unknown"))]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Instant;

#[cfg(all(target_arch = "wasm32", target_os = "unknown"))]
impl Instant {
    pub(crate) fn now() -> Self {
        Self
    }

    pub(crate) fn elapsed(self) -> Duration {
        Duration::ZERO
    }
}
