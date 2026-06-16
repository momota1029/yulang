//! Extracted body lowering methods.

use super::super::*;
use super::*;

impl BodyLowerer {
    pub(super) fn lower_role_decl_body(&mut self, node: &Cst, module: ModuleId) {
        let Some(name) = crate::type_decl_name(node) else {
            return;
        };
        let Some(decl) = self.next_type_decl(module, &name) else {
            return;
        };
        let Some(body) = crate::role_decl_body(node) else {
            return;
        };
        let Some(companion) = self.modules.type_companion(decl.id) else {
            return;
        };
        let role_inputs = self.modules.role_inputs(decl.id).to_vec();
        let role_associated = self.modules.role_associated(decl.id).to_vec();
        let mut method_cursor = 0usize;
        let previous_scope = self.local_method_scope.replace(companion);
        for child in body.children() {
            match child.kind() {
                SyntaxKind::Binding if crate::role_method_binding(&child).is_some() => {
                    let method = self
                        .modules
                        .role_methods(decl.id)
                        .get(method_cursor)
                        .cloned();
                    method_cursor += usize::from(method.is_some());
                    if let Some(method) = method {
                        if binding_body_expr(&child).is_some() {
                            self.lower_role_method_binding(
                                &child,
                                companion,
                                &decl,
                                &method,
                                &role_inputs,
                                &role_associated,
                            );
                        } else {
                            self.lower_role_method_signature(
                                &child,
                                companion,
                                &decl,
                                &method,
                                &role_inputs,
                                &role_associated,
                            );
                        }
                    }
                }
                SyntaxKind::Binding => {
                    self.lower_binding(&child, companion);
                }
                SyntaxKind::ModDecl => self.lower_mod_decl(&child, companion),
                SyntaxKind::CastDecl => self.lower_cast_decl(&child, companion),
                _ => {}
            }
        }
        self.local_method_scope = previous_scope;
    }

    pub(super) fn collect_declared_role_requirements(&mut self) {
        let methods = self.modules.all_role_methods().cloned().collect::<Vec<_>>();
        for method in methods {
            match self.build_role_method_requirement(&method) {
                Ok(Some(requirement)) => {
                    self.role_requirements.insert(method.def, requirement);
                }
                Ok(None) => {}
                Err(error) => self.errors.push(BodyLoweringError::Expr {
                    def: method.def,
                    name: method.name,
                    error,
                }),
            }
        }
    }

    pub(super) fn collect_declared_role_input_variances(&mut self) {
        let mut role_owners = self
            .modules
            .all_role_methods()
            .map(|method| method.owner)
            .collect::<Vec<_>>();
        role_owners.sort_by_key(|owner| owner.0);
        role_owners.dedup();

        for owner in role_owners {
            let role_inputs = self.modules.role_inputs(owner);
            if role_inputs.is_empty() {
                continue;
            }
            let variances = role_input_variances_from_requirements(
                role_inputs,
                self.modules.role_methods(owner),
                &self.role_requirements,
            );
            let Some(role) = self.modules.type_decl_by_id(owner) else {
                continue;
            };
            let path = self
                .modules
                .type_decl_path(&role)
                .segments
                .into_iter()
                .map(|name| name.0)
                .collect::<Vec<_>>();
            self.session.register_role_input_variances(path, variances);
        }
    }

    pub(super) fn build_role_method_requirement(
        &self,
        method: &RoleMethodDecl,
    ) -> Result<Option<RoleMethodRequirement>, LoweringError> {
        let Some(type_expr) = method.signature.clone() else {
            return Ok(None);
        };
        let Some(companion) = self.modules.type_companion(method.owner) else {
            return Ok(None);
        };
        let role_inputs = self.modules.role_inputs(method.owner);
        let role_associated = self.modules.role_associated(method.owner);
        let mut builder = ann_type_builder(&self.modules, companion, method.order, None);
        for name in role_inputs.iter().chain(role_associated.iter()) {
            builder.add_bare_type_var(name.clone());
        }
        if let Some(first) = role_inputs.first() {
            builder.add_bare_type_var_alias("self", first.clone());
        }
        let signature = build_signature_type_expr(&mut builder, &type_expr)
            .map_err(|error| LoweringError::AnnotationBuild { error })?;
        let signature = role_method_signature_with_receiver(
            method.receiver.as_ref(),
            role_inputs.first(),
            signature,
        );
        Ok(Some(RoleMethodRequirement { signature }))
    }
}
