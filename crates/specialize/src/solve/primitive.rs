use super::*;

pub(super) fn function_type(args: Vec<Type>, ret: Type) -> Type {
    args.into_iter()
        .rev()
        .fold(ret, |ret, arg| types::pure_function_type(arg, ret))
}

pub(super) fn unary_type(arg: Type, ret: Type) -> Type {
    function_type(vec![arg], ret)
}

pub(super) fn binary_type(arg: Type, ret: Type) -> Type {
    function_type(vec![arg.clone(), arg], ret)
}

pub(super) fn con_type(name: &str) -> Type {
    Type::Con {
        path: vec![name.to_string()],
        args: Vec::new(),
    }
}

pub(super) fn int_type() -> Type {
    con_type("int")
}

pub(super) fn float_type() -> Type {
    con_type("float")
}

pub(super) fn bool_type() -> Type {
    con_type("bool")
}

pub(super) fn str_type() -> Type {
    std_types::str_type()
}

pub(super) fn char_type() -> Type {
    std_types::char_type()
}

pub(super) fn list_type(item: Type) -> Type {
    std_types::list_type(item)
}

pub(super) fn list_view_type(item: Type) -> Type {
    std_types::list_view_type(item)
}

pub(super) fn bytes_type() -> Type {
    std_types::bytes_type()
}

pub(super) fn path_type() -> Type {
    std_types::path_type()
}

pub(super) fn range_type() -> Type {
    std_types::range_type()
}
