use crate::Value;

pub(super) fn discard_default_root_effect(path: &[String]) -> Option<Value> {
    if path == ["std", "testing", "assertion", "assert"] {
        Some(Value::Unit)
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn discards_default_assertion_operation() {
        assert_eq!(
            discard_default_root_effect(
                &["std", "testing", "assertion", "assert"].map(str::to_string)
            ),
            Some(Value::Unit)
        );
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
