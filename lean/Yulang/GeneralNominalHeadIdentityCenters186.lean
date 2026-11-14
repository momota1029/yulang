import Yulang.GeneralNominalHeadIdentityInduction186
import Yulang.GeneralNominalHeadSchemaSemantic186

/-! Semantic center agreement for equal numeric identities in actual traces.
Full occurrence equality and equal capture bounds are not assumptions. -/
namespace Yulang.GeneralNominalHeadIdentityCenters186
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadStepKernel
open GeneralNominalOriginTerms
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalHeadIdentityInduction186 (CentersSame)
open GeneralNominalCenteredHeadWFBoundary (boundary)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

theorem trace_registered_binders
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (first last : Plan roles) (one : first ∈ state.core.plans) (two : last ∈ state.core.plans)
    (declaration : first.packet.declaration = last.packet.declaration)
    (model : Assignment) (valid : Models state model)
    (centers : CentersSame model first.input last.input)
    (name : Nat) (named : name ∈ first.packet.declaration.inputNames) :
    Same model (.source (first.binder name)) (.source (last.binder name)) := by
  have a := GeneralNominalHeadReadback185.registered_initial_configuration path first one
  have b := GeneralNominalHeadReadback185.registered_initial_configuration path last two
  exact GeneralNominalHeadSchemaSemantic186.binder_same first last declaration
    (a.2.1.trans b.2.1.symm) (a.2.2.trans b.2.2.symm) centers
    (valid.1.2.2 first one).2.2.1 (valid.1.2.2 last two).2.2.1
    (GeneralNominalHeadCoreCoverage185.registered_finished path first one) name named

theorem trace_registered_identity_centers_same (checked : Checked registry)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (first last : Site roles) (one : first ∈ state.core.sites) (two : last ∈ state.core.sites)
    (identity : first.occurrence.identity = last.occurrence.identity)
    (model : Assignment) (valid : Models state model) : CentersSame model first last :=
  GeneralNominalHeadIdentityInduction186.trace_identity_centers checked path model
    (fun a ha b hb declaration centers name named =>
      trace_registered_binders path a b ha hb declaration model valid centers name named)
    first last one two identity

theorem registered_identity_centers_same (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (first last : Site roles) (one : first ∈ state.core.sites) (two : last ∈ state.core.sites)
    (identity : first.occurrence.identity = last.occurrence.identity)
    (model : Assignment) (valid : Models state model) : CentersSame model first last := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ :=
    GeneralNominalCenteredHeadWFBoundary.reachable_old reachable
  exact trace_registered_identity_centers_same checked path first last one two identity model valid

theorem registered_identity_binders_same (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (first last : Plan roles) (one : first ∈ state.core.plans) (two : last ∈ state.core.plans)
    (identity : first.packet.site.occurrence.identity = last.packet.site.occurrence.identity)
    (declaration : first.packet.declaration = last.packet.declaration)
    (name : Nat) (named : name ∈ first.packet.declaration.inputNames)
    (model : Assignment) (valid : Models state model) :
    Same model (.source (first.binder name)) (.source (last.binder name)) := by
  have centers := registered_identity_centers_same checked reachable first.input last.input
    (GeneralNominalHeadCandidateReadback185.wf_registered_input reachable first one)
    (GeneralNominalHeadCandidateReadback185.wf_registered_input reachable last two)
    ((congrArg Occurrence.identity first.input_exact).trans
      (identity.trans (congrArg Occurrence.identity last.input_exact).symm)) model valid
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ :=
    GeneralNominalCenteredHeadWFBoundary.reachable_old reachable
  exact trace_registered_binders path first last one two declaration model valid centers name named

end Yulang.GeneralNominalHeadIdentityCenters186
