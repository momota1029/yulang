use super::*;

pub(super) fn pattern_bindings(pattern: &Pattern) -> Vec<(core_ir::Path, RuntimeType)> {
    let mut bindings = Vec::new();
    collect_pattern_bindings(pattern, &mut bindings);
    bindings
}

pub(super) fn push_bindings(
    locals: &mut HashMap<core_ir::Path, RuntimeType>,
    bindings: &[(core_ir::Path, RuntimeType)],
) -> Vec<(core_ir::Path, Option<RuntimeType>)> {
    bindings
        .iter()
        .map(|(path, ty)| (path.clone(), locals.insert(path.clone(), ty.clone())))
        .collect()
}

pub(super) fn push_binding(
    locals: &mut HashMap<core_ir::Path, RuntimeType>,
    path: core_ir::Path,
    ty: RuntimeType,
) -> Vec<(core_ir::Path, Option<RuntimeType>)> {
    vec![(path.clone(), locals.insert(path, ty))]
}

pub(super) fn pop_bindings(
    locals: &mut HashMap<core_ir::Path, RuntimeType>,
    previous: Vec<(core_ir::Path, Option<RuntimeType>)>,
) {
    for (path, ty) in previous.into_iter().rev() {
        match ty {
            Some(ty) => {
                locals.insert(path, ty);
            }
            None => {
                locals.remove(&path);
            }
        }
    }
}

pub(super) fn push_stmt_bindings(locals: &mut HashMap<core_ir::Path, RuntimeType>, stmt: &Stmt) {
    match stmt {
        Stmt::Let { pattern, .. } => {
            for (path, ty) in pattern_bindings(pattern) {
                locals.insert(path, ty);
            }
        }
        Stmt::Module { def, body } => {
            locals.insert(def.clone(), body.ty.clone());
        }
        Stmt::Expr(_) => {}
    }
}

fn collect_pattern_bindings(pattern: &Pattern, bindings: &mut Vec<(core_ir::Path, RuntimeType)>) {
    match pattern {
        Pattern::Bind { name, ty } => {
            bindings.push((core_ir::Path::from_name(name.clone()), ty.clone()));
        }
        Pattern::As { pattern, name, ty } => {
            collect_pattern_bindings(pattern, bindings);
            bindings.push((core_ir::Path::from_name(name.clone()), ty.clone()));
        }
        Pattern::Tuple { items, .. } | Pattern::List { prefix: items, .. } => {
            for item in items {
                collect_pattern_bindings(item, bindings);
            }
            if let Pattern::List { spread, suffix, .. } = pattern {
                if let Some(spread) = spread {
                    collect_pattern_bindings(spread, bindings);
                }
                for item in suffix {
                    collect_pattern_bindings(item, bindings);
                }
            }
        }
        Pattern::Record { fields, spread, .. } => {
            for field in fields {
                collect_pattern_bindings(&field.pattern, bindings);
            }
            if let Some(spread) = spread {
                match spread {
                    RecordSpreadPattern::Head(pattern) | RecordSpreadPattern::Tail(pattern) => {
                        collect_pattern_bindings(pattern, bindings);
                    }
                }
            }
        }
        Pattern::Variant { value, .. } => {
            if let Some(value) = value {
                collect_pattern_bindings(value, bindings);
            }
        }
        Pattern::Or { left, right, .. } => {
            collect_pattern_bindings(left, bindings);
            collect_pattern_bindings(right, bindings);
        }
        Pattern::Wildcard { .. } | Pattern::Lit { .. } => {}
    }
}
