use crate::symbols::{Name, Path};

pub(crate) fn standard_ref_type_path() -> Path {
    Path {
        segments: vec![
            Name("std".to_string()),
            Name("var".to_string()),
            Name("ref".to_string()),
        ],
    }
}

pub(crate) fn standard_ref_member_path(member: Name) -> Vec<Name> {
    let mut path = standard_ref_type_path().segments;
    path.push(member);
    path
}

pub(crate) fn standard_var_act_path() -> Path {
    Path {
        segments: vec![
            Name("std".to_string()),
            Name("var".to_string()),
            Name("var".to_string()),
        ],
    }
}

pub(crate) fn core_standard_ref_type_path() -> yulang_typed_ir::Path {
    yulang_typed_ir::Path::new(vec![
        yulang_typed_ir::Name("std".to_string()),
        yulang_typed_ir::Name("var".to_string()),
        yulang_typed_ir::Name("ref".to_string()),
    ])
}

pub(crate) fn core_standard_ref_member_path(member: &str) -> yulang_typed_ir::Path {
    let mut path = core_standard_ref_type_path();
    path.segments
        .push(yulang_typed_ir::Name(member.to_string()));
    path
}

pub(crate) fn core_standard_ref_update_member_path(member: &str) -> yulang_typed_ir::Path {
    yulang_typed_ir::Path::new(vec![
        yulang_typed_ir::Name("std".to_string()),
        yulang_typed_ir::Name("var".to_string()),
        yulang_typed_ir::Name("ref_update".to_string()),
        yulang_typed_ir::Name(member.to_string()),
    ])
}
