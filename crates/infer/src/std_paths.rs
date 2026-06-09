//! Standard-library paths that lowering and analysis need as structured symbols.
//!
//! These are not inference shortcuts. They are the names of library-defined types
//! that surface syntax desugars to, so the compiler must agree on their resolved
//! constructor paths.

pub(crate) fn control_var_ref_type() -> Vec<String> {
    path(&["std", "control", "var", "ref"])
}

pub(crate) fn control_var_var_member(member: &str) -> Vec<String> {
    path(&["std", "control", "var", "var", member])
}

#[cfg(test)]
pub(crate) fn control_var_ref_update_effect() -> Vec<String> {
    path(&["std", "control", "var", "ref_update"])
}

pub(crate) fn is_control_var_ref_type(path: &[String]) -> bool {
    path_matches(path, &["std", "control", "var", "ref"])
}

fn path(segments: &[&str]) -> Vec<String> {
    segments
        .iter()
        .map(|segment| (*segment).to_string())
        .collect()
}

fn path_matches(path: &[String], expected: &[&str]) -> bool {
    path.len() == expected.len()
        && path
            .iter()
            .zip(expected.iter())
            .all(|(segment, expected)| segment == expected)
}
