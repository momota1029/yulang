//! Canonical std constructor paths used by compiler primitives.
//!
//! Lowering resolves `builtin_op::...` signatures through lexical lookup before storing them in
//! `poly`. Direct primitive expressions such as list literals only keep the primitive kind, so
//! specialize must use the same canonical constructors when reconstructing their mono type.

use mono::Type;

pub(crate) fn str_type() -> Type {
    con(&["std", "text", "str", "str"], Vec::new())
}

pub(crate) fn char_type() -> Type {
    con(&["std", "text", "char", "char"], Vec::new())
}

pub(crate) fn bytes_type() -> Type {
    con(&["std", "text", "bytes", "bytes"], Vec::new())
}

pub(crate) fn path_type() -> Type {
    con(&["std", "text", "path", "path"], Vec::new())
}

pub(crate) fn range_type() -> Type {
    con(&["std", "data", "range", "range"], Vec::new())
}

pub(crate) fn list_type(item: Type) -> Type {
    con(&["std", "data", "list", "list"], vec![item])
}

pub(crate) fn list_view_type(item: Type) -> Type {
    con(&["std", "data", "list", "list_view"], vec![item])
}

fn con(path: &[&str], args: Vec<Type>) -> Type {
    Type::Con {
        path: path.iter().map(|segment| (*segment).to_string()).collect(),
        args,
    }
}
