use crate::symbols::{Name, Path};

pub(crate) fn standard_loop_path() -> Path {
    Path {
        segments: path_segments(["std", "flow", "loop"]),
    }
}

pub(crate) fn standard_loop_for_in_path() -> Vec<Name> {
    standard_flow_member_path(standard_loop_path(), Name("for_in".to_string()))
}

pub(crate) fn standard_label_loop_path() -> Path {
    Path {
        segments: path_segments(["std", "flow", "label_loop"]),
    }
}

pub(crate) fn standard_label_sub_path() -> Path {
    Path {
        segments: path_segments(["std", "flow", "label_sub"]),
    }
}

pub(crate) fn standard_sub_path() -> Path {
    Path {
        segments: path_segments(["std", "flow", "sub"]),
    }
}

pub(crate) fn standard_sub_member_path(member: Name) -> Vec<Name> {
    standard_flow_member_path(standard_sub_path(), member)
}

pub(crate) fn standard_sub_call_path() -> Vec<Name> {
    standard_sub_member_path(Name("sub".to_string()))
}

fn standard_flow_member_path(path: Path, member: Name) -> Vec<Name> {
    let mut segments = path.segments;
    segments.push(member);
    segments
}

fn path_segments<const N: usize>(segments: [&str; N]) -> Vec<Name> {
    segments
        .into_iter()
        .map(|segment| Name(segment.to_string()))
        .collect()
}
