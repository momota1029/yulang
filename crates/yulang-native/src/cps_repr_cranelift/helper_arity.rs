/// Per-arity runtime helper symbol tables. Native CPS emits a fixed set
/// of `_0..=_4` specializations plus a generic `_many` fallback so the
/// JIT can pick the cheapest variant without parsing the helper name at
/// codegen time.
pub(super) struct FixedManyHelpers {
    pub(super) fixed: [&'static str; 5],
    pub(super) many: &'static str,
}

impl FixedManyHelpers {
    pub(super) fn fixed(&self, len: usize) -> &'static str {
        self.fixed
            .get(len)
            .copied()
            .expect("fixed helper arity must be 0..=4")
    }

    pub(super) fn select(&self, len: usize) -> &'static str {
        self.fixed.get(len).copied().unwrap_or(self.many)
    }
}

pub(super) const MAKE_RESUMPTION_HELPERS: FixedManyHelpers = FixedManyHelpers {
    fixed: [
        "yulang_cps_make_resumption_i64_0",
        "yulang_cps_make_resumption_i64_1",
        "yulang_cps_make_resumption_i64_2",
        "yulang_cps_make_resumption_i64_3",
        "yulang_cps_make_resumption_i64_4",
    ],
    many: "yulang_cps_make_resumption_i64_many",
};

pub(super) const MAKE_THUNK_HELPERS: FixedManyHelpers = FixedManyHelpers {
    fixed: [
        "yulang_cps_make_thunk_i64_0",
        "yulang_cps_make_thunk_i64_1",
        "yulang_cps_make_thunk_i64_2",
        "yulang_cps_make_thunk_i64_3",
        "yulang_cps_make_thunk_i64_4",
    ],
    many: "yulang_cps_make_thunk_i64_many",
};

pub(super) const MMTK_MAKE_THUNK_HELPERS: FixedManyHelpers = FixedManyHelpers {
    fixed: [
        "yulang_mmtk_cps_control_make_thunk_i64_0",
        "yulang_mmtk_cps_control_make_thunk_i64_1",
        "yulang_mmtk_cps_control_make_thunk_i64_2",
        "yulang_mmtk_cps_control_make_thunk_i64_3",
        "yulang_mmtk_cps_control_make_thunk_i64_4",
    ],
    many: "yulang_mmtk_cps_control_make_thunk_i64_many",
};

pub(super) const MAKE_CLOSURE_HELPERS: FixedManyHelpers = FixedManyHelpers {
    fixed: [
        "yulang_cps_make_closure_i64_0",
        "yulang_cps_make_closure_i64_1",
        "yulang_cps_make_closure_i64_2",
        "yulang_cps_make_closure_i64_3",
        "yulang_cps_make_closure_i64_4",
    ],
    many: "yulang_cps_make_closure_i64_many",
};

pub(super) const MMTK_MAKE_CLOSURE_HELPERS: FixedManyHelpers = FixedManyHelpers {
    fixed: [
        "yulang_mmtk_cps_control_make_closure_i64_0",
        "yulang_mmtk_cps_control_make_closure_i64_1",
        "yulang_mmtk_cps_control_make_closure_i64_2",
        "yulang_mmtk_cps_control_make_closure_i64_3",
        "yulang_mmtk_cps_control_make_closure_i64_4",
    ],
    many: "yulang_mmtk_cps_control_make_closure_i64_many",
};

pub(super) const MAKE_RECURSIVE_CLOSURE_HELPERS: FixedManyHelpers = FixedManyHelpers {
    fixed: [
        "yulang_cps_make_recursive_closure_i64_0",
        "yulang_cps_make_recursive_closure_i64_1",
        "yulang_cps_make_recursive_closure_i64_2",
        "yulang_cps_make_recursive_closure_i64_3",
        "yulang_cps_make_recursive_closure_i64_4",
    ],
    many: "yulang_cps_make_recursive_closure_i64_many",
};

pub(super) const MAKE_ENV_HELPERS: FixedManyHelpers = FixedManyHelpers {
    fixed: [
        "yulang_cps_make_env_i64_0",
        "yulang_cps_make_env_i64_1",
        "yulang_cps_make_env_i64_2",
        "yulang_cps_make_env_i64_3",
        "yulang_cps_make_env_i64_4",
    ],
    many: "yulang_cps_make_env_i64_many",
};

pub(super) const TUPLE_HELPERS: FixedManyHelpers = FixedManyHelpers {
    fixed: [
        "yulang_cps_tuple_i64_0",
        "yulang_cps_tuple_i64_1",
        "yulang_cps_tuple_i64_2",
        "yulang_cps_tuple_i64_3",
        "yulang_cps_tuple_i64_4",
    ],
    many: "yulang_cps_tuple_i64_many",
};

pub(super) const PUSH_RETURN_FRAME_HELPERS: FixedManyHelpers = FixedManyHelpers {
    fixed: [
        "yulang_cps_push_return_frame_i64_0",
        "yulang_cps_push_return_frame_i64_1",
        "yulang_cps_push_return_frame_i64_2",
        "yulang_cps_push_return_frame_i64_3",
        "yulang_cps_push_return_frame_i64_4",
    ],
    many: "yulang_cps_push_return_frame_i64_many",
};

pub(super) const INSTALL_HANDLER_FULL_HELPERS: FixedManyHelpers = FixedManyHelpers {
    fixed: [
        "yulang_cps_install_handler_full_i64_0",
        "yulang_cps_install_handler_full_i64_1",
        "yulang_cps_install_handler_full_i64_2",
        "yulang_cps_install_handler_full_i64_3",
        "yulang_cps_install_handler_full_i64_4",
    ],
    many: "yulang_cps_install_handler_full_i64_many",
};

pub(super) const EFFECTFUL_APPLY_RESUMPTION_HELPERS: FixedManyHelpers = FixedManyHelpers {
    fixed: [
        "yulang_cps_effectful_apply_resumption_i64_0",
        "yulang_cps_effectful_apply_resumption_i64_1",
        "yulang_cps_effectful_apply_resumption_i64_2",
        "yulang_cps_effectful_apply_resumption_i64_3",
        "yulang_cps_effectful_apply_resumption_i64_4",
    ],
    many: "yulang_cps_effectful_apply_resumption_i64_many",
};
