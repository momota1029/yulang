//! Immutable source contract captured before role-impl annotations enter inference.
//!
//! This module owns source binder identity and explicit/inferred associated provenance only.
//! Method correspondence, validation, and `BodyLowering` lifecycle handoff belong to later stages.

use poly::expr::DefId;
use sources::SourceRange;

use crate::annotation::{AnnEffectAtom, AnnEffectRow, AnnType, AnnTypeVar, AnnTypeVarId};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RoleImplConformanceContract {
    pub(crate) impl_def: DefId,
    pub(crate) role: Vec<String>,
    pub(crate) source: SourceRange,
    pub(crate) universal_binders: Vec<ImplUniversalBinder>,
    pub(crate) inputs: Vec<DeclaredType>,
    pub(crate) associated: Vec<AssociatedAssignment>,
}

impl RoleImplConformanceContract {
    pub(crate) fn capture(
        impl_def: DefId,
        role: Vec<String>,
        source: SourceRange,
        inputs: Vec<AnnType>,
        associated: Vec<AssociatedAssignment>,
    ) -> Self {
        let inputs = inputs
            .into_iter()
            .map(DeclaredType::new)
            .collect::<Vec<_>>();
        let mut source_binders = Vec::new();
        for input in &inputs {
            input.collect_source_binders(&mut source_binders);
        }
        for assignment in &associated {
            if let AssociatedAssignment::Explicit { ty, .. } = assignment {
                ty.collect_source_binders(&mut source_binders);
            }
        }
        source_binders.sort_by_key(|binder| binder.id.0);
        source_binders.dedup_by_key(|binder| binder.id);
        let universal_binders = source_binders
            .into_iter()
            .enumerate()
            .map(|(index, binder)| ImplUniversalBinder {
                id: ImplUniversalBinderId(index as u32),
                annotation_var: binder.id,
                source_name: binder.name,
            })
            .collect();

        Self {
            impl_def,
            role,
            source,
            universal_binders,
            inputs,
            associated,
        }
    }

    #[cfg(test)]
    pub(crate) fn binder_dump(&self) -> String {
        let universals = self
            .universal_binders
            .iter()
            .map(|binder| format!("U{}", binder.id.0))
            .collect::<Vec<_>>()
            .join(",");
        let inputs = self
            .inputs
            .iter()
            .map(|input| self.declared_type_binder_dump(input))
            .collect::<Vec<_>>()
            .join(",");
        let associated = self
            .associated
            .iter()
            .map(|assignment| match assignment {
                AssociatedAssignment::Explicit { name, ty, .. } => {
                    format!("{name}=explicit{}", self.declared_type_binder_dump(ty))
                }
                AssociatedAssignment::Inferred { name, binder } => {
                    let overlap = self
                        .universal_binder_for(binder.annotation_var)
                        .map(|binder| format!(";annotation-overlap=U{}", binder.0))
                        .unwrap_or_default();
                    format!("{name}=inferred(A{}{overlap})", binder.id.0)
                }
            })
            .collect::<Vec<_>>()
            .join(",");
        format!(
            "role={} universals=[{universals}] inputs=[{inputs}] associated=[{associated}]",
            self.role.join("::"),
        )
    }

    #[cfg(test)]
    fn declared_type_binder_dump(&self, ty: &DeclaredType) -> String {
        let mut binders = Vec::new();
        ty.collect_source_binders(&mut binders);
        let mut binders = binders
            .into_iter()
            .filter_map(|binder| self.universal_binder_for(binder.id))
            .collect::<Vec<_>>();
        binders.sort_by_key(|binder| binder.0);
        binders.dedup();
        format!(
            "{{{}}}",
            binders
                .into_iter()
                .map(|binder| format!("U{}", binder.0))
                .collect::<Vec<_>>()
                .join(",")
        )
    }

    #[cfg(test)]
    fn universal_binder_for(&self, annotation_var: AnnTypeVarId) -> Option<ImplUniversalBinderId> {
        self.universal_binders
            .iter()
            .find_map(|binder| (binder.annotation_var == annotation_var).then_some(binder.id))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ImplUniversalBinder {
    pub(crate) id: ImplUniversalBinderId,
    pub(crate) annotation_var: AnnTypeVarId,
    pub(crate) source_name: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct ImplUniversalBinderId(pub(crate) u32);

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DeclaredType {
    pub(crate) annotation: AnnType,
}

impl DeclaredType {
    pub(crate) fn new(annotation: AnnType) -> Self {
        Self { annotation }
    }

    fn collect_source_binders(&self, out: &mut Vec<AnnTypeVar>) {
        collect_ann_type_vars(&self.annotation, out);
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum AssociatedAssignment {
    Explicit {
        name: String,
        ty: DeclaredType,
        source: SourceRange,
    },
    Inferred {
        name: String,
        binder: AssociatedInferenceBinder,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct AssociatedInferenceBinder {
    pub(crate) id: AssociatedInferenceBinderId,
    pub(crate) annotation_var: AnnTypeVarId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct AssociatedInferenceBinderId(pub(crate) u32);

fn collect_ann_type_vars(ty: &AnnType, out: &mut Vec<AnnTypeVar>) {
    match ty {
        AnnType::Builtin(_) | AnnType::Named(_) => {}
        AnnType::Var(var) => out.push(var.clone()),
        AnnType::Wildcard(_) => {}
        AnnType::EffectRow(row) => collect_effect_row_vars(row, out),
        AnnType::Effectful { eff, ret } => {
            collect_effect_row_vars(eff, out);
            collect_ann_type_vars(ret, out);
        }
        AnnType::Tuple(items) => {
            for item in items {
                collect_ann_type_vars(item, out);
            }
        }
        AnnType::Apply { callee, args } => {
            collect_ann_type_vars(callee, out);
            for arg in args {
                collect_ann_type_vars(arg, out);
            }
        }
        AnnType::Function {
            param,
            arg_eff,
            ret_eff,
            ret,
        } => {
            collect_ann_type_vars(param, out);
            if let Some(arg_eff) = arg_eff {
                collect_effect_row_vars(arg_eff, out);
            }
            if let Some(ret_eff) = ret_eff {
                collect_effect_row_vars(ret_eff, out);
            }
            collect_ann_type_vars(ret, out);
        }
    }
}

fn collect_effect_row_vars(row: &AnnEffectRow, out: &mut Vec<AnnTypeVar>) {
    for item in &row.items {
        if let AnnEffectAtom::Type(ty) = item {
            collect_ann_type_vars(ty, out);
        }
    }
    if let Some(tail) = &row.tail {
        out.push(tail.clone());
    }
}
