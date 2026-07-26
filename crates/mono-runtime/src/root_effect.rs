use crate::Value;

pub(super) fn discard_default_root_effect(path: &[String]) -> Option<Value> {
    match path {
        [std, testing, assertion, operation]
            if std == "std"
                && testing == "testing"
                && assertion == "assertion"
                && matches!(operation.as_str(), "assert" | "assert_eq") =>
        {
            Some(Value::Unit)
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn discards_default_assertion_operations() {
        for operation in ["assert", "assert_eq"] {
            assert_eq!(
                discard_default_root_effect(
                    &["std", "testing", "assertion", operation].map(str::to_string)
                ),
                Some(Value::Unit)
            );
        }
    }

    #[test]
    fn leaves_other_effect_operations_unhandled() {
        assert_eq!(
            discard_default_root_effect(
                &["std", "io", "console", "out", "write"].map(str::to_string)
            ),
            None
        );
    }
}
