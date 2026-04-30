use std::time::Duration;
#[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
use std::time::Instant;

pub(crate) struct ProfileClock {
    #[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
    instant: Instant,
}

impl ProfileClock {
    pub(crate) fn now() -> Self {
        Self {
            #[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
            instant: Instant::now(),
        }
    }

    pub(crate) fn elapsed(&self) -> Duration {
        #[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
        {
            return self.instant.elapsed();
        }

        #[cfg(all(target_arch = "wasm32", target_os = "unknown"))]
        {
            Duration::ZERO
        }
    }
}
