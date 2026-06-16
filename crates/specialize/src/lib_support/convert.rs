use super::*;

pub(crate) fn convert_lit(lit: &poly_expr::Lit) -> Lit {
    match lit {
        poly_expr::Lit::Int(value) => Lit::Int(*value),
        poly_expr::Lit::BigInt(value) => Lit::BigInt(value.clone()),
        poly_expr::Lit::Float(value) => Lit::Float(*value),
        poly_expr::Lit::Str(value) => Lit::Str(value.clone()),
        poly_expr::Lit::Bool(value) => Lit::Bool(*value),
        poly_expr::Lit::Unit => Lit::Unit,
    }
}

pub(crate) fn convert_primitive_op(op: poly_expr::PrimitiveOp) -> PrimitiveOp {
    match op {
        poly_expr::PrimitiveOp::YadaYada => PrimitiveOp::YadaYada,
        poly_expr::PrimitiveOp::BoolNot => PrimitiveOp::BoolNot,
        poly_expr::PrimitiveOp::BoolEq => PrimitiveOp::BoolEq,
        poly_expr::PrimitiveOp::ListEmpty => PrimitiveOp::ListEmpty,
        poly_expr::PrimitiveOp::ListSingleton => PrimitiveOp::ListSingleton,
        poly_expr::PrimitiveOp::ListLen => PrimitiveOp::ListLen,
        poly_expr::PrimitiveOp::ListMerge => PrimitiveOp::ListMerge,
        poly_expr::PrimitiveOp::ListIndex => PrimitiveOp::ListIndex,
        poly_expr::PrimitiveOp::ListIndexRange => PrimitiveOp::ListIndexRange,
        poly_expr::PrimitiveOp::ListSplice => PrimitiveOp::ListSplice,
        poly_expr::PrimitiveOp::ListIndexRangeRaw => PrimitiveOp::ListIndexRangeRaw,
        poly_expr::PrimitiveOp::ListSpliceRaw => PrimitiveOp::ListSpliceRaw,
        poly_expr::PrimitiveOp::ListViewRaw => PrimitiveOp::ListViewRaw,
        poly_expr::PrimitiveOp::StringLen => PrimitiveOp::StringLen,
        poly_expr::PrimitiveOp::StringIndex => PrimitiveOp::StringIndex,
        poly_expr::PrimitiveOp::StringIndexRange => PrimitiveOp::StringIndexRange,
        poly_expr::PrimitiveOp::StringSplice => PrimitiveOp::StringSplice,
        poly_expr::PrimitiveOp::StringIndexRangeRaw => PrimitiveOp::StringIndexRangeRaw,
        poly_expr::PrimitiveOp::StringSpliceRaw => PrimitiveOp::StringSpliceRaw,
        poly_expr::PrimitiveOp::StringLineCount => PrimitiveOp::StringLineCount,
        poly_expr::PrimitiveOp::StringLineRange => PrimitiveOp::StringLineRange,
        poly_expr::PrimitiveOp::IntAdd => PrimitiveOp::IntAdd,
        poly_expr::PrimitiveOp::IntSub => PrimitiveOp::IntSub,
        poly_expr::PrimitiveOp::IntMul => PrimitiveOp::IntMul,
        poly_expr::PrimitiveOp::IntDiv => PrimitiveOp::IntDiv,
        poly_expr::PrimitiveOp::IntMod => PrimitiveOp::IntMod,
        poly_expr::PrimitiveOp::IntEq => PrimitiveOp::IntEq,
        poly_expr::PrimitiveOp::IntLt => PrimitiveOp::IntLt,
        poly_expr::PrimitiveOp::IntLe => PrimitiveOp::IntLe,
        poly_expr::PrimitiveOp::IntGt => PrimitiveOp::IntGt,
        poly_expr::PrimitiveOp::IntGe => PrimitiveOp::IntGe,
        poly_expr::PrimitiveOp::FloatAdd => PrimitiveOp::FloatAdd,
        poly_expr::PrimitiveOp::FloatSub => PrimitiveOp::FloatSub,
        poly_expr::PrimitiveOp::FloatMul => PrimitiveOp::FloatMul,
        poly_expr::PrimitiveOp::FloatDiv => PrimitiveOp::FloatDiv,
        poly_expr::PrimitiveOp::FloatEq => PrimitiveOp::FloatEq,
        poly_expr::PrimitiveOp::FloatLt => PrimitiveOp::FloatLt,
        poly_expr::PrimitiveOp::FloatLe => PrimitiveOp::FloatLe,
        poly_expr::PrimitiveOp::FloatGt => PrimitiveOp::FloatGt,
        poly_expr::PrimitiveOp::FloatGe => PrimitiveOp::FloatGe,
        poly_expr::PrimitiveOp::StringEq => PrimitiveOp::StringEq,
        poly_expr::PrimitiveOp::StringConcat => PrimitiveOp::StringConcat,
        poly_expr::PrimitiveOp::StringToBytes => PrimitiveOp::StringToBytes,
        poly_expr::PrimitiveOp::CharEq => PrimitiveOp::CharEq,
        poly_expr::PrimitiveOp::CharToString => PrimitiveOp::CharToString,
        poly_expr::PrimitiveOp::CharIsWhitespace => PrimitiveOp::CharIsWhitespace,
        poly_expr::PrimitiveOp::CharIsPunctuation => PrimitiveOp::CharIsPunctuation,
        poly_expr::PrimitiveOp::CharIsWord => PrimitiveOp::CharIsWord,
        poly_expr::PrimitiveOp::BytesLen => PrimitiveOp::BytesLen,
        poly_expr::PrimitiveOp::BytesEq => PrimitiveOp::BytesEq,
        poly_expr::PrimitiveOp::BytesConcat => PrimitiveOp::BytesConcat,
        poly_expr::PrimitiveOp::BytesIndex => PrimitiveOp::BytesIndex,
        poly_expr::PrimitiveOp::BytesIndexRange => PrimitiveOp::BytesIndexRange,
        poly_expr::PrimitiveOp::BytesToUtf8Raw => PrimitiveOp::BytesToUtf8Raw,
        poly_expr::PrimitiveOp::BytesToPath => PrimitiveOp::BytesToPath,
        poly_expr::PrimitiveOp::PathToBytes => PrimitiveOp::PathToBytes,
        poly_expr::PrimitiveOp::IntToString => PrimitiveOp::IntToString,
        poly_expr::PrimitiveOp::IntToHex => PrimitiveOp::IntToHex,
        poly_expr::PrimitiveOp::IntToUpperHex => PrimitiveOp::IntToUpperHex,
        poly_expr::PrimitiveOp::IntToFloat => PrimitiveOp::IntToFloat,
        poly_expr::PrimitiveOp::FloatToString => PrimitiveOp::FloatToString,
        poly_expr::PrimitiveOp::BoolToString => PrimitiveOp::BoolToString,
    }
}

pub(crate) fn primitive_context(
    arena: &poly_expr::Arena,
    op: poly_expr::PrimitiveOp,
    ty: Option<&Type>,
) -> PrimitiveContext {
    match op {
        poly_expr::PrimitiveOp::ListViewRaw => PrimitiveContext {
            list_view: ty.and_then(|ty| list_view_constructors(arena, ty)),
        },
        _ => PrimitiveContext::default(),
    }
}

pub(crate) fn list_view_constructors(
    arena: &poly_expr::Arena,
    primitive_ty: &Type,
) -> Option<ListViewConstructors> {
    let Type::Fun { ret, .. } = primitive_ty else {
        return None;
    };
    let Type::Con { path, .. } = ret.as_ref() else {
        return None;
    };
    let constructor = |name: &str| {
        arena
            .constructors
            .iter()
            .find(|(_, constructor)| {
                constructor.owner_path.as_slice() == path.as_slice() && constructor.name == name
            })
            .map(|(def, _)| convert_def(*def))
    };
    Some(ListViewConstructors {
        empty: constructor("empty")?,
        leaf: constructor("leaf")?,
        node: constructor("node")?,
    })
}

pub(crate) fn lit_type(lit: &poly_expr::Lit) -> Type {
    let name = match lit {
        poly_expr::Lit::Int(_) | poly_expr::Lit::BigInt(_) => "int",
        poly_expr::Lit::Float(_) => "float",
        poly_expr::Lit::Str(_) => return std_types::str_type(),
        poly_expr::Lit::Bool(_) => "bool",
        poly_expr::Lit::Unit => "unit",
    };
    Type::Con {
        path: vec![name.to_string()],
        args: Vec::new(),
    }
}

pub(crate) fn convert_vis(vis: poly_expr::Vis) -> Vis {
    match vis {
        poly_expr::Vis::Pub => Vis::Pub,
        poly_expr::Vis::Our => Vis::Our,
        poly_expr::Vis::My => Vis::My,
    }
}

pub(crate) fn convert_def(def: poly_expr::DefId) -> DefId {
    DefId(def.0)
}

pub(crate) fn convert_def_spread(
    spread: &poly_expr::RecordSpread<poly_expr::DefId>,
) -> RecordSpread<DefId> {
    match spread {
        poly_expr::RecordSpread::Head(def) => RecordSpread::Head(convert_def(*def)),
        poly_expr::RecordSpread::Tail(def) => RecordSpread::Tail(convert_def(*def)),
        poly_expr::RecordSpread::None => RecordSpread::None,
    }
}

pub(crate) fn def_kind(def: &poly_expr::Def) -> DefKind {
    match def {
        poly_expr::Def::Mod { .. } => DefKind::Module,
        poly_expr::Def::Let { .. } => DefKind::Let,
        poly_expr::Def::Arg => DefKind::Arg,
    }
}
