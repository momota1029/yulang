//! Extracted body lowering methods.

use super::super::*;

pub(in crate::lowering) fn register_declared_type_methods(
    session: &mut AnalysisSession,
    modules: &ModuleTable,
) {
    for method in modules.all_type_methods() {
        if method.vis == poly::expr::Vis::My {
            continue;
        }
        let Some(owner) = modules.type_decl_by_id(method.owner) else {
            continue;
        };
        let receiver = modules
            .type_decl_path(&owner)
            .segments
            .into_iter()
            .map(|name| name.0)
            .collect::<Vec<_>>();
        match method.receiver_kind {
            TypeMethodReceiver::Value => {
                session.register_value_type_method(receiver, method.name.0.clone(), method.def);
            }
            TypeMethodReceiver::Ref => {
                session.register_ref_type_method(receiver, method.name.0.clone(), method.def);
            }
        }
    }
}

pub(in crate::lowering) fn register_declared_type_field_methods(
    session: &mut AnalysisSession,
    modules: &ModuleTable,
) {
    for method in modules.all_type_field_methods() {
        if method.vis == poly::expr::Vis::My
            || visible_explicit_type_method_exists(
                modules,
                method.owner,
                &method.name,
                method.receiver_kind,
            )
        {
            continue;
        }
        let Some(owner) = modules.type_decl_by_id(method.owner) else {
            continue;
        };
        let receiver = modules
            .type_decl_path(&owner)
            .segments
            .into_iter()
            .map(|name| name.0)
            .collect::<Vec<_>>();
        match method.receiver_kind {
            TypeMethodReceiver::Value => {
                session.register_value_type_method(receiver, method.name.0.clone(), method.def);
            }
            TypeMethodReceiver::Ref => {
                session.register_ref_type_method(receiver, method.name.0.clone(), method.def);
            }
        }
    }
}

pub(in crate::lowering) fn visible_explicit_type_method_exists(
    modules: &ModuleTable,
    owner: TypeDeclId,
    name: &Name,
    receiver_kind: TypeMethodReceiver,
) -> bool {
    modules.type_methods(owner).iter().any(|method| {
        method.vis != poly::expr::Vis::My
            && method.name == *name
            && method.receiver_kind == receiver_kind
    })
}

pub(in crate::lowering) fn register_declared_act_methods(
    session: &mut AnalysisSession,
    modules: &ModuleTable,
) {
    for method in modules.all_act_methods() {
        if method.vis == poly::expr::Vis::My {
            continue;
        }
        let Some(owner) = modules.type_decl_by_id(method.owner) else {
            continue;
        };
        let effect = modules
            .type_decl_path(&owner)
            .segments
            .into_iter()
            .map(|name| name.0)
            .collect::<Vec<_>>();
        session.register_effect_method(effect, method.name.0.clone(), method.def);
    }
}

pub(in crate::lowering) fn register_declared_companion_local_methods(
    session: &mut AnalysisSession,
    modules: &ModuleTable,
) {
    for method in modules.all_type_methods() {
        let Some(scope) = modules.type_companion(method.owner) else {
            continue;
        };
        let Some(owner) = modules.type_decl_by_id(method.owner) else {
            continue;
        };
        let receiver = modules
            .type_decl_path(&owner)
            .segments
            .into_iter()
            .map(|name| name.0)
            .collect::<Vec<_>>();
        match method.receiver_kind {
            TypeMethodReceiver::Value => {
                session.register_local_value_type_method(
                    scope,
                    receiver,
                    method.name.0.clone(),
                    method.def,
                );
            }
            TypeMethodReceiver::Ref => {
                session.register_local_ref_type_method(
                    scope,
                    receiver,
                    method.name.0.clone(),
                    method.def,
                );
            }
        }
    }

    for method in modules.all_act_methods() {
        let Some(scope) = modules.type_companion(method.owner) else {
            continue;
        };
        let Some(owner) = modules.type_decl_by_id(method.owner) else {
            continue;
        };
        let effect = modules
            .type_decl_path(&owner)
            .segments
            .into_iter()
            .map(|name| name.0)
            .collect::<Vec<_>>();
        session.register_local_effect_method(scope, effect, method.name.0.clone(), method.def);
    }

    for method in modules.all_role_methods() {
        let Some(scope) = modules.type_companion(method.owner) else {
            continue;
        };
        let Some(owner) = modules.type_decl_by_id(method.owner) else {
            continue;
        };
        let role = modules
            .type_decl_path(&owner)
            .segments
            .into_iter()
            .map(|name| name.0)
            .collect::<Vec<_>>();
        session.register_local_role_method(scope, role, method.name.0.clone(), method.def);
    }
}

pub(in crate::lowering) fn register_declared_role_methods(
    session: &mut AnalysisSession,
    modules: &ModuleTable,
) {
    for method in modules.all_role_methods() {
        if method.vis == poly::expr::Vis::My {
            continue;
        }
        let Some(owner) = modules.type_decl_by_id(method.owner) else {
            continue;
        };
        let role = modules
            .type_decl_path(&owner)
            .segments
            .into_iter()
            .map(|name| name.0)
            .collect::<Vec<_>>();
        session.register_role_method(role, method.name.0.clone(), method.def);
    }
}
