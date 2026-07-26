#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum RuntimeRootEffectResolution {
    Assertion(RuntimeAssertionKind),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum RuntimeAssertionKind {
    Condition,
    Equality,
}

#[derive(Debug, Clone, Copy, Default)]
pub(super) struct RuntimeRootEffectRegistry;

impl RuntimeRootEffectRegistry {
    pub(super) fn resolve(&self, path: &[String]) -> Option<RuntimeRootEffectResolution> {
        match path {
            [std, testing, assertion, operation]
                if std == "std" && testing == "testing" && assertion == "assertion" =>
            {
                match operation.as_str() {
                    "assert" => Some(RuntimeRootEffectResolution::Assertion(
                        RuntimeAssertionKind::Condition,
                    )),
                    "assert_eq" => Some(RuntimeRootEffectResolution::Assertion(
                        RuntimeAssertionKind::Equality,
                    )),
                    _ => None,
                }
            }
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn registry_resolves_default_assertion_operations() {
        let registry = RuntimeRootEffectRegistry;

        assert_eq!(
            registry.resolve(&["std", "testing", "assertion", "assert"].map(str::to_string)),
            Some(RuntimeRootEffectResolution::Assertion(
                RuntimeAssertionKind::Condition
            ))
        );
        assert_eq!(
            registry.resolve(&["std", "testing", "assertion", "assert_eq"].map(str::to_string)),
            Some(RuntimeRootEffectResolution::Assertion(
                RuntimeAssertionKind::Equality
            ))
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
