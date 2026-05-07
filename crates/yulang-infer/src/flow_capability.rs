use crate::symbols::{Name, Path};

pub(crate) fn standard_loop_for_in_path() -> Vec<Name> {
    path_segments_with(["std", "flow", "loop"], Name("for_in".to_string()))
}

pub(crate) fn standard_label_loop_path() -> Path {
    Path {
        segments: path_segments(["std", "flow", "label_loop"]),
    }
}

pub(crate) fn standard_sub_path() -> Path {
    Path {
        segments: path_segments(["std", "flow", "sub"]),
    }
}

pub(crate) fn standard_sub_member_path(member: Name) -> Vec<Name> {
    path_segments_with(["std", "flow", "sub"], member)
}

pub(crate) fn standard_sub_call_path() -> Vec<Name> {
    standard_sub_member_path(Name("sub".to_string()))
}

fn path_segments<const N: usize>(segments: [&str; N]) -> Vec<Name> {
    segments
        .into_iter()
        .map(|segment| Name(segment.to_string()))
        .collect()
}

fn path_segments_with<const N: usize>(segments: [&str; N], member: Name) -> Vec<Name> {
    let mut path = path_segments(segments);
    path.push(member);
    path
}
