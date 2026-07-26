//! Shared lowering boundary for compiler-synthesized role implementations.
//!
//! Synthetic declarations do not have an `ImplDecl` CST node or a module-map
//! registration.  They still enter the ordinary candidate and method-lowering
//! path so their method mappings and generalization residuals are preserved.

use super::super::*;
use super::*;

pub(super) struct SyntheticRoleImpl<'a> {
    pub(super) role: TypeDeclId,
    pub(super) module: ModuleId,
    pub(super) site: ModuleOrder,
    pub(super) target_ann: AnnType,
    pub(super) input_anns: Vec<AnnType>,
    pub(super) associated_anns: Vec<(String, AnnType)>,
    pub(super) type_var_bindings: Vec<(String, AnnTypeVarId)>,
    pub(super) methods: Vec<SyntheticRoleImplMethod<'a>>,
}

pub(super) struct SyntheticRoleImplMethod<'a> {
    pub(super) name: Name,
    pub(super) receiver: Option<Name>,
    pub(super) vis: Vis,
    pub(super) label: String,
    pub(super) binding: Result<&'a Cst, LoweringError>,
}

#[cfg_attr(not(test), allow(dead_code))]
pub(super) struct SyntheticRoleImplResult {
    pub(super) impl_def: DefId,
    pub(super) method_defs: Vec<DefId>,
}

impl BodyLowerer {
    pub(super) fn lower_synthetic_role_impl(
        &mut self,
        synthetic: SyntheticRoleImpl<'_>,
    ) -> Result<SyntheticRoleImplResult, LoweringError> {
        let impl_def = self.session.poly.defs.fresh();
        let method_defs = (0..synthetic.methods.len())
            .map(|_| self.session.poly.defs.fresh())
            .collect::<Vec<_>>();
        self.session.poly.defs.set(
            impl_def,
            Def::Mod {
                vis: Vis::My,
                children: method_defs.clone(),
            },
        );
        for (method, method_def) in synthetic.methods.iter().zip(&method_defs) {
            self.session.poly.defs.set(
                *method_def,
                Def::Let {
                    vis: method.vis,
                    scheme: None,
                    body: None,
                    children: Vec::new(),
                },
            );
            self.labels.set_def_label(*method_def, method.label.clone());
        }

        for (method, method_def) in synthetic.methods.iter().zip(&method_defs) {
            if let Err(error) = &method.binding {
                self.push_registered_expr_error(*method_def, method.name.clone(), error.clone());
                return Ok(SyntheticRoleImplResult {
                    impl_def,
                    method_defs,
                });
            }
        }

        let role_path = self
            .modules
            .type_decl_by_id(synthetic.role)
            .map(|role| {
                self.modules
                    .type_decl_path(&role)
                    .segments
                    .into_iter()
                    .map(|name| name.0)
                    .collect::<Vec<_>>()
            })
            .ok_or(LoweringError::UnsupportedSyntax {
                kind: SyntaxKind::ImplDecl,
            })?;
        let input_names = self.modules.role_inputs(synthetic.role).to_vec();
        let input_signatures = synthetic
            .input_anns
            .iter()
            .map(signature_from_ann_type)
            .collect::<Vec<_>>();
        let associated_signatures = synthetic
            .associated_anns
            .iter()
            .map(|(name, ann)| (name.clone(), signature_from_ann_type(ann)))
            .collect::<Vec<_>>();
        let (inputs, associated, ann_solver_vars) =
            self.lower_role_impl_args(&synthetic.input_anns, &synthetic.associated_anns)?;
        let mut context = self.register_prepared_role_impl_candidate(
            RoleImplCandidate {
                impl_def: Some(impl_def),
                role: role_path,
                inputs,
                associated,
                prerequisites: Vec::new(),
                methods: Vec::new(),
            },
            RoleImplLoweringContext {
                conformance_contract: None,
                conformance_shadow_targets: FxHashMap::default(),
                role: synthetic.role,
                target_ann: synthetic.target_ann,
                input_names,
                input_signatures,
                associated_signatures,
                type_var_bindings: synthetic.type_var_bindings,
                ann_solver_vars,
            },
        );

        for (method, method_def) in synthetic.methods.iter().zip(&method_defs) {
            let binding = method
                .binding
                .as_ref()
                .expect("synthetic method binding errors return before registration");
            let requirement = self.role_impl_method_requirement(&context, method.name.clone());
            self.lower_role_impl_method_binding(
                binding,
                impl_def,
                synthetic.module,
                &RoleImplMethodDecl {
                    name: method.name.clone(),
                    receiver: method.receiver.clone(),
                    def: *method_def,
                    vis: method.vis,
                    order: synthetic.site,
                },
                &context.target_ann,
                &context.type_var_bindings,
                &mut context.ann_solver_vars,
                requirement,
                None,
            );
        }

        Ok(SyntheticRoleImplResult {
            impl_def,
            method_defs,
        })
    }
}
