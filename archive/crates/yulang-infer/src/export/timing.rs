use std::time::Duration;
#[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
use std::time::Instant;

use yulang_typed_ir as typed_ir;

pub(crate) struct ExportClock {
    #[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
    instant: Option<Instant>,
}

impl ExportClock {
    pub(crate) fn now(enabled: bool) -> Self {
        Self {
            #[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
            instant: enabled.then(Instant::now),
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

pub(crate) fn format_core_path_for_export_timing(path: &typed_ir::Path) -> String {
    if path.segments.is_empty() {
        return "<root>".to_string();
    }
    path.segments
        .iter()
        .map(|segment| segment.0.as_str())
        .collect::<Vec<_>>()
        .join("::")
}
