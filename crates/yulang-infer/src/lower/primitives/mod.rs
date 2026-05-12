use yulang_typed_ir as typed_ir;

use crate::lower::LowerState;
use crate::symbols::ModuleId;

mod list;
mod scalar;
mod support;

use list::{
    install_list_empty_primitive, install_list_index_primitive, install_list_index_range_primitive,
    install_list_index_range_raw_primitive, install_list_len_primitive,
    install_list_merge_primitive, install_list_singleton_primitive, install_list_splice_primitive,
    install_list_splice_raw_primitive, install_list_view_raw_primitive,
};
use scalar::{
    install_bool_binary_predicate_primitive, install_bool_unary_primitive,
    install_float_binary_predicate_primitive, install_float_binary_primitive,
    install_int_binary_predicate_primitive, install_int_binary_primitive,
    install_string_binary_primitive, install_string_index_primitive,
    install_string_index_range_primitive, install_string_index_range_raw_primitive,
    install_string_len_primitive, install_string_splice_primitive,
    install_string_splice_raw_primitive, install_to_string_primitive,
};
use support::{ensure_builtin_type, ensure_child_module};

pub fn install_builtin_primitives(state: &mut LowerState) {
    let std_module = ensure_child_module(state, ModuleId(0), "std");
    let bool_module = ensure_child_module(state, std_module, "bool");
    let list_module = ensure_child_module(state, std_module, "list");
    let int_module = ensure_child_module(state, std_module, "int");
    let float_module = ensure_child_module(state, std_module, "float");
    let str_module = ensure_child_module(state, std_module, "str");
    ensure_builtin_type(state, list_module, "list");
    ensure_builtin_type(state, str_module, "str");

    install_bool_unary_primitive(state, bool_module, "not", typed_ir::PrimitiveOp::BoolNot);
    install_bool_binary_predicate_primitive(
        state,
        bool_module,
        "eq",
        typed_ir::PrimitiveOp::BoolEq,
    );
    install_list_empty_primitive(
        state,
        list_module,
        "empty",
        typed_ir::PrimitiveOp::ListEmpty,
    );
    install_list_singleton_primitive(
        state,
        list_module,
        "singleton",
        typed_ir::PrimitiveOp::ListSingleton,
    );
    install_list_len_primitive(state, list_module, "len", typed_ir::PrimitiveOp::ListLen);
    install_list_merge_primitive(
        state,
        list_module,
        "merge",
        typed_ir::PrimitiveOp::ListMerge,
    );
    install_list_index_primitive(
        state,
        list_module,
        "index_raw",
        typed_ir::PrimitiveOp::ListIndex,
    );
    install_list_index_range_primitive(
        state,
        list_module,
        "index_range",
        typed_ir::PrimitiveOp::ListIndexRange,
    );
    install_list_splice_primitive(
        state,
        list_module,
        "splice",
        typed_ir::PrimitiveOp::ListSplice,
    );
    install_list_index_range_raw_primitive(
        state,
        list_module,
        "index_range_raw",
        typed_ir::PrimitiveOp::ListIndexRangeRaw,
    );
    install_list_splice_raw_primitive(
        state,
        list_module,
        "splice_raw",
        typed_ir::PrimitiveOp::ListSpliceRaw,
    );
    install_list_view_raw_primitive(
        state,
        list_module,
        "view_raw",
        typed_ir::PrimitiveOp::ListViewRaw,
    );

    install_int_binary_primitive(state, int_module, "add", typed_ir::PrimitiveOp::IntAdd);
    install_int_binary_primitive(state, int_module, "sub", typed_ir::PrimitiveOp::IntSub);
    install_int_binary_primitive(state, int_module, "mul", typed_ir::PrimitiveOp::IntMul);
    install_int_binary_primitive(state, int_module, "div", typed_ir::PrimitiveOp::IntDiv);
    install_int_binary_predicate_primitive(state, int_module, "eq", typed_ir::PrimitiveOp::IntEq);
    install_int_binary_predicate_primitive(state, int_module, "lt", typed_ir::PrimitiveOp::IntLt);
    install_int_binary_predicate_primitive(state, int_module, "le", typed_ir::PrimitiveOp::IntLe);
    install_int_binary_predicate_primitive(state, int_module, "gt", typed_ir::PrimitiveOp::IntGt);
    install_int_binary_predicate_primitive(state, int_module, "ge", typed_ir::PrimitiveOp::IntGe);
    install_to_string_primitive(
        state,
        int_module,
        "to_string",
        typed_ir::PrimitiveOp::IntToString,
        "int",
    );
    install_to_string_primitive(
        state,
        int_module,
        "to_hex",
        typed_ir::PrimitiveOp::IntToHex,
        "int",
    );
    install_to_string_primitive(
        state,
        int_module,
        "to_upper_hex",
        typed_ir::PrimitiveOp::IntToUpperHex,
        "int",
    );

    install_float_binary_primitive(state, float_module, "add", typed_ir::PrimitiveOp::FloatAdd);
    install_float_binary_primitive(state, float_module, "sub", typed_ir::PrimitiveOp::FloatSub);
    install_float_binary_primitive(state, float_module, "mul", typed_ir::PrimitiveOp::FloatMul);
    install_float_binary_primitive(state, float_module, "div", typed_ir::PrimitiveOp::FloatDiv);
    install_float_binary_predicate_primitive(
        state,
        float_module,
        "eq",
        typed_ir::PrimitiveOp::FloatEq,
    );
    install_float_binary_predicate_primitive(
        state,
        float_module,
        "lt",
        typed_ir::PrimitiveOp::FloatLt,
    );
    install_float_binary_predicate_primitive(
        state,
        float_module,
        "le",
        typed_ir::PrimitiveOp::FloatLe,
    );
    install_float_binary_predicate_primitive(
        state,
        float_module,
        "gt",
        typed_ir::PrimitiveOp::FloatGt,
    );
    install_float_binary_predicate_primitive(
        state,
        float_module,
        "ge",
        typed_ir::PrimitiveOp::FloatGe,
    );
    install_to_string_primitive(
        state,
        float_module,
        "to_string",
        typed_ir::PrimitiveOp::FloatToString,
        "float",
    );

    install_string_binary_primitive(
        state,
        str_module,
        "concat",
        typed_ir::PrimitiveOp::StringConcat,
    );
    install_string_len_primitive(state, str_module, "len", typed_ir::PrimitiveOp::StringLen);
    install_string_index_primitive(
        state,
        str_module,
        "index_raw",
        typed_ir::PrimitiveOp::StringIndex,
    );
    install_string_index_range_primitive(
        state,
        str_module,
        "index_range",
        typed_ir::PrimitiveOp::StringIndexRange,
    );
    install_string_splice_primitive(
        state,
        str_module,
        "splice",
        typed_ir::PrimitiveOp::StringSplice,
    );
    install_string_index_range_raw_primitive(
        state,
        str_module,
        "index_range_raw",
        typed_ir::PrimitiveOp::StringIndexRangeRaw,
    );
    install_string_splice_raw_primitive(
        state,
        str_module,
        "splice_raw",
        typed_ir::PrimitiveOp::StringSpliceRaw,
    );
    install_to_string_primitive(
        state,
        bool_module,
        "to_string",
        typed_ir::PrimitiveOp::BoolToString,
        "bool",
    );
}
