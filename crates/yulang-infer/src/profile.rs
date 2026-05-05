use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Duration;
#[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
use std::time::Instant;

static PROFILE_ENABLED: AtomicBool = AtomicBool::new(false);

pub fn with_profile_enabled<T>(enabled: bool, f: impl FnOnce() -> T) -> T {
    let previous = PROFILE_ENABLED.swap(enabled, Ordering::Relaxed);
    let result = f();
    PROFILE_ENABLED.store(previous, Ordering::Relaxed);
    result
}

pub(crate) struct ProfileClock {
    #[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
    instant: Option<Instant>,
}

impl ProfileClock {
    pub(crate) fn now() -> Self {
        Self {
            #[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
            instant: PROFILE_ENABLED.load(Ordering::Relaxed).then(Instant::now),
        }
    }

    pub(crate) fn elapsed(&self) -> Duration {
        #[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
        {
            return self
                .instant
                .map(|instant| instant.elapsed())
                .unwrap_or_default();
        }

        #[cfg(all(target_arch = "wasm32", target_os = "unknown"))]
        {
            Duration::ZERO
        }
    }
}
