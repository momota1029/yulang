//! Standard-library paths that lowering and analysis need as structured symbols.
//!
//! These are not inference shortcuts. They are the names of library-defined types
//! that surface syntax desugars to, so the compiler must agree on their resolved
//! constructor paths.

pub(crate) fn control_var_ref_type() -> Vec<String> {
    path(&["std", "control", "var", "ref"])
}

pub(crate) fn text_str_type() -> Vec<String> {
    path(&["std", "text", "str", "str"])
}

pub(crate) fn text_parse_value(name: &str) -> Vec<String> {
    let mut path = path(&["std", "text", "parse"]);
    path.push(name.to_string());
    path
}

pub(crate) fn control_junction_value() -> Vec<String> {
    path(&["std", "control", "junction", "junction", "junction"])
}

pub(crate) fn control_flow_loop_for_in_value() -> Vec<String> {
    path(&["std", "control", "flow", "loop", "for_in"])
}

pub(crate) fn control_var_var_act() -> Vec<String> {
    path(&["std", "control", "var", "var"])
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
