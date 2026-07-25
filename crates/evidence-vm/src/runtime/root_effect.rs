#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum RuntimeRootEffectResolution {
    DiscardPayloadAndResumeUnit,
}

#[derive(Debug, Clone, Copy, Default)]
pub(super) struct RuntimeRootEffectRegistry;

impl RuntimeRootEffectRegistry {
    pub(super) fn resolve(&self, path: &[String]) -> Option<RuntimeRootEffectResolution> {
        if is_test_assertion_operation(path) {
            Some(RuntimeRootEffectResolution::DiscardPayloadAndResumeUnit)
        } else {
            None
        }
    }
}

fn is_test_assertion_operation(path: &[String]) -> bool {
    path == ["std", "test", "test", "assert"]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn registry_discards_test_assertion_operation() {
        let registry = RuntimeRootEffectRegistry;

        assert_eq!(
            registry.resolve(&["std", "test", "test", "assert"].map(str::to_string)),
            Some(RuntimeRootEffectResolution::DiscardPayloadAndResumeUnit)
        );
    }

    #[test]
    fn registry_does_not_claim_other_effect_operations() {
        let registry = RuntimeRootEffectRegistry;

        assert_eq!(
            registry.resolve(&["std", "io", "console", "out", "write"].map(str::to_string)),
            None
        );
    }
}
