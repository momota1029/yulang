//! `builtin_op::...` namespace の registry。
//!
//! std source から見える builtin operation はここで構造化された kind と signature へ解決する。
//! lowering や inference の途中で std path 文字列を見ないため、この表を compiler builtin
//! namespace の境界にする。

use poly::expr::PrimitiveOp;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct BuiltinOp {
    pub(crate) op: PrimitiveOp,
    pub(crate) sig: BuiltinOpSig,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BuiltinOpSig {
    Nullary {
        ret: &'static str,
    },
    Unary {
        param: &'static str,
        ret: &'static str,
    },
    Binary {
        param: &'static str,
        ret: &'static str,
    },
    BinaryPredicate {
        param: &'static str,
    },
    Mixed {
        params: &'static [&'static str],
        ret: &'static str,
    },
    BytesToUtf8Raw,
    /// 多相 builtin の signature。量化変数は番号で表し、同じ番号は同じ型変数を共有する。
    Poly {
        params: &'static [SigTy],
        ret: SigTy,
    },
}

/// signature 中の型式。`Var(n)` は量化変数（同番号は同一変数）、`Con(name, args)` は
/// 型適用。名前は lexical type lookup で解決し、型引数は invariant に渡す。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SigTy {
    Var(u8),
    Con(&'static str, &'static [SigTy]),
}

const A: SigTy = SigTy::Var(0);
const LIST_A: SigTy = SigTy::Con("list", &[A]);
const VIEW_A: SigTy = SigTy::Con("list_view", &[A]);
const INT: SigTy = SigTy::Con("int", &[]);
const RANGE: SigTy = SigTy::Con("range", &[]);

pub(crate) fn resolve_builtin_op(name: &str) -> Option<BuiltinOp> {
    use BuiltinOpSig::*;
    use PrimitiveOp::*;

    let op = match name {
        "yada_yada" => BuiltinOp {
            op: YadaYada,
            sig: Nullary { ret: "never" },
        },
        "list_view_raw" => BuiltinOp {
            op: ListViewRaw,
            sig: Poly {
                params: &[LIST_A],
                ret: VIEW_A,
            },
        },
        "list_merge" => BuiltinOp {
            op: ListMerge,
            sig: Poly {
                params: &[LIST_A, LIST_A],
                ret: LIST_A,
            },
        },
        "list_len" => BuiltinOp {
            op: ListLen,
            sig: Poly {
                params: &[LIST_A],
                ret: INT,
            },
        },
        "list_index" => BuiltinOp {
            op: ListIndex,
            sig: Poly {
                params: &[LIST_A, INT],
                ret: A,
            },
        },
        "list_index_range" => BuiltinOp {
            op: ListIndexRange,
            sig: Poly {
                params: &[LIST_A, RANGE],
                ret: LIST_A,
            },
        },
        "list_index_range_raw" => BuiltinOp {
            op: ListIndexRangeRaw,
            sig: Poly {
                params: &[LIST_A, INT, INT],
                ret: LIST_A,
            },
        },
        "list_splice" => BuiltinOp {
            op: ListSplice,
            sig: Poly {
                params: &[LIST_A, RANGE, LIST_A],
                ret: LIST_A,
            },
        },
        "list_splice_raw" => BuiltinOp {
            op: ListSpliceRaw,
            sig: Poly {
                params: &[LIST_A, INT, INT, LIST_A],
                ret: LIST_A,
            },
        },
        "bool_not" => BuiltinOp {
            op: BoolNot,
            sig: Unary {
                param: "bool",
                ret: "bool",
            },
        },
        "bool_eq" => BuiltinOp {
            op: BoolEq,
            sig: BinaryPredicate { param: "bool" },
        },
        "int_add" => BuiltinOp {
            op: IntAdd,
            sig: Binary {
                param: "int",
                ret: "int",
            },
        },
        "int_sub" => BuiltinOp {
            op: IntSub,
            sig: Binary {
                param: "int",
                ret: "int",
            },
        },
        "int_mul" => BuiltinOp {
            op: IntMul,
            sig: Binary {
                param: "int",
                ret: "int",
            },
        },
        "int_div" => BuiltinOp {
            op: IntDiv,
            sig: Binary {
                param: "int",
                ret: "int",
            },
        },
        "int_mod" => BuiltinOp {
            op: IntMod,
            sig: Binary {
                param: "int",
                ret: "int",
            },
        },
        "int_eq" => BuiltinOp {
            op: IntEq,
            sig: BinaryPredicate { param: "int" },
        },
        "int_lt" => BuiltinOp {
            op: IntLt,
            sig: BinaryPredicate { param: "int" },
        },
        "int_le" => BuiltinOp {
            op: IntLe,
            sig: BinaryPredicate { param: "int" },
        },
        "int_gt" => BuiltinOp {
            op: IntGt,
            sig: BinaryPredicate { param: "int" },
        },
        "int_ge" => BuiltinOp {
            op: IntGe,
            sig: BinaryPredicate { param: "int" },
        },
        "int_to_string" => BuiltinOp {
            op: IntToString,
            sig: Unary {
                param: "int",
                ret: "str",
            },
        },
        "int_to_hex" => BuiltinOp {
            op: IntToHex,
            sig: Unary {
                param: "int",
                ret: "str",
            },
        },
        "int_to_upper_hex" => BuiltinOp {
            op: IntToUpperHex,
            sig: Unary {
                param: "int",
                ret: "str",
            },
        },
        "int_to_float" => BuiltinOp {
            op: IntToFloat,
            sig: Unary {
                param: "int",
                ret: "float",
            },
        },
        "float_add" => BuiltinOp {
            op: FloatAdd,
            sig: Binary {
                param: "float",
                ret: "float",
            },
        },
        "float_sub" => BuiltinOp {
            op: FloatSub,
            sig: Binary {
                param: "float",
                ret: "float",
            },
        },
        "float_mul" => BuiltinOp {
            op: FloatMul,
            sig: Binary {
                param: "float",
                ret: "float",
            },
        },
        "float_div" => BuiltinOp {
            op: FloatDiv,
            sig: Binary {
                param: "float",
                ret: "float",
            },
        },
        "float_eq" => BuiltinOp {
            op: FloatEq,
            sig: BinaryPredicate { param: "float" },
        },
        "float_lt" => BuiltinOp {
            op: FloatLt,
            sig: BinaryPredicate { param: "float" },
        },
        "float_le" => BuiltinOp {
            op: FloatLe,
            sig: BinaryPredicate { param: "float" },
        },
        "float_gt" => BuiltinOp {
            op: FloatGt,
            sig: BinaryPredicate { param: "float" },
        },
        "float_ge" => BuiltinOp {
            op: FloatGe,
            sig: BinaryPredicate { param: "float" },
        },
        "float_to_string" => BuiltinOp {
            op: FloatToString,
            sig: Unary {
                param: "float",
                ret: "str",
            },
        },
        "string_concat" => BuiltinOp {
            op: StringConcat,
            sig: Binary {
                param: "str",
                ret: "str",
            },
        },
        "string_eq" => BuiltinOp {
            op: StringEq,
            sig: BinaryPredicate { param: "str" },
        },
        "string_len" => BuiltinOp {
            op: StringLen,
            sig: Unary {
                param: "str",
                ret: "int",
            },
        },
        "string_line_count" => BuiltinOp {
            op: StringLineCount,
            sig: Unary {
                param: "str",
                ret: "int",
            },
        },
        "string_index" => BuiltinOp {
            op: StringIndex,
            sig: Mixed {
                params: &["str", "int"],
                ret: "char",
            },
        },
        "string_index_range" => BuiltinOp {
            op: StringIndexRange,
            sig: Mixed {
                params: &["str", "range"],
                ret: "str",
            },
        },
        "string_line_range" => BuiltinOp {
            op: StringLineRange,
            sig: Mixed {
                params: &["str", "int"],
                ret: "range",
            },
        },
        "string_index_range_raw" => BuiltinOp {
            op: StringIndexRangeRaw,
            sig: Mixed {
                params: &["str", "int", "int"],
                ret: "str",
            },
        },
        "string_splice" => BuiltinOp {
            op: StringSplice,
            sig: Mixed {
                params: &["str", "range", "str"],
                ret: "str",
            },
        },
        "string_splice_raw" => BuiltinOp {
            op: StringSpliceRaw,
            sig: Mixed {
                params: &["str", "int", "int", "str"],
                ret: "str",
            },
        },
        "string_to_bytes" => BuiltinOp {
            op: StringToBytes,
            sig: Unary {
                param: "str",
                ret: "bytes",
            },
        },
        "bool_to_string" => BuiltinOp {
            op: BoolToString,
            sig: Unary {
                param: "bool",
                ret: "str",
            },
        },
        "char_eq" => BuiltinOp {
            op: CharEq,
            sig: BinaryPredicate { param: "char" },
        },
        "char_to_string" => BuiltinOp {
            op: CharToString,
            sig: Unary {
                param: "char",
                ret: "str",
            },
        },
        "char_is_whitespace" => BuiltinOp {
            op: CharIsWhitespace,
            sig: Unary {
                param: "char",
                ret: "bool",
            },
        },
        "char_is_punctuation" => BuiltinOp {
            op: CharIsPunctuation,
            sig: Unary {
                param: "char",
                ret: "bool",
            },
        },
        "char_is_word" => BuiltinOp {
            op: CharIsWord,
            sig: Unary {
                param: "char",
                ret: "bool",
            },
        },
        "bytes_len" => BuiltinOp {
            op: BytesLen,
            sig: Unary {
                param: "bytes",
                ret: "int",
            },
        },
        "bytes_eq" => BuiltinOp {
            op: BytesEq,
            sig: BinaryPredicate { param: "bytes" },
        },
        "bytes_concat" => BuiltinOp {
            op: BytesConcat,
            sig: Binary {
                param: "bytes",
                ret: "bytes",
            },
        },
        "bytes_index" => BuiltinOp {
            op: BytesIndex,
            sig: Mixed {
                params: &["bytes", "int"],
                ret: "int",
            },
        },
        "bytes_index_range" => BuiltinOp {
            op: BytesIndexRange,
            sig: Mixed {
                params: &["bytes", "range"],
                ret: "bytes",
            },
        },
        "bytes_to_utf8_raw" => BuiltinOp {
            op: PrimitiveOp::BytesToUtf8Raw,
            sig: BuiltinOpSig::BytesToUtf8Raw,
        },
        "bytes_to_path" => BuiltinOp {
            op: BytesToPath,
            sig: Unary {
                param: "bytes",
                ret: "path",
            },
        },
        "path_to_bytes" => BuiltinOp {
            op: PathToBytes,
            sig: Unary {
                param: "path",
                ret: "bytes",
            },
        },
        _ => return None,
    };
    Some(op)
}
