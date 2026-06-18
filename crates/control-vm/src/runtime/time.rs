#[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
pub(super) use std::time::{Duration, Instant};

#[cfg(all(target_arch = "wasm32", target_os = "unknown"))]
pub(super) use std::time::Duration;

#[cfg(all(target_arch = "wasm32", target_os = "unknown"))]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct Instant;

#[cfg(all(target_arch = "wasm32", target_os = "unknown"))]
impl Instant {
    pub(super) fn now() -> Self {
        Self
    }

    pub(super) fn elapsed(self) -> Duration {
        Duration::ZERO
    }
}
