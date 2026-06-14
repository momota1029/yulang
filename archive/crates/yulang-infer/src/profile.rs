use std::cell::Cell;
use std::time::Duration;
#[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
use std::time::Instant;

thread_local! {
    static PROFILE_ENABLED: Cell<bool> = const { Cell::new(false) };
}

pub fn with_profile_enabled<T>(enabled: bool, f: impl FnOnce() -> T) -> T {
    let previous = PROFILE_ENABLED.replace(enabled);
    let result = f();
    PROFILE_ENABLED.set(previous);
    result
}

pub(crate) fn profile_enabled() -> bool {
    PROFILE_ENABLED.get()
}

pub(crate) struct ProfileClock {
    #[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
    instant: Option<Instant>,
}

impl ProfileClock {
    pub(crate) fn now() -> Self {
        Self {
            #[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
            instant: PROFILE_ENABLED.get().then(Instant::now),
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn profile_enabled_scope_is_thread_local() {
        let barrier = std::sync::Arc::new(std::sync::Barrier::new(2));
        let worker_barrier = barrier.clone();

        let worker = std::thread::spawn(move || {
            with_profile_enabled(true, || {
                worker_barrier.wait();
                worker_barrier.wait();
                assert!(profile_enabled());
            });
            assert!(!profile_enabled());
        });

        barrier.wait();
        assert!(!profile_enabled());
        barrier.wait();
        worker.join().unwrap();
        assert!(!profile_enabled());
    }
}
