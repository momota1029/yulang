import Yulang.GeneralNominalChildSemantic186
import Yulang.GeneralNominalHeadRootOverlap185

/-! The numeric invocation induction for registered site centers. Its local
binder-transfer premise is isolated from the trace argument; a separate
schema theorem supplies it. No equality of full occurrences is required. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Yulang.GeneralNominalHeadIdentityInduction186
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadStepKernel
open GeneralNominalOriginTerms
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

def CentersSame (model : Assignment) (first last : Site roles) : Prop :=
  ∀ index : Nat, Same model
    (.source (((List.ofFn first.center)[index]?).getD 0))
    (.source (((List.ofFn last.center)[index]?).getD 0))

theorem centers_self (model : Assignment) (site : Site roles) : CentersSame model site site :=
  fun _ => source_self model _

private theorem childSite_congr (plan : Plan roles) (first last : Clause)
    (equal : first = last) (one : first.Signature roles) (two : last.Signature roles) :
    plan.childSite first one = plan.childSite last two := by
  cases equal
  rfl

theorem trace_identity_centers (checked : Checked registry)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (model : Assignment)
    (transfer : ∀ first ∈ state.core.plans, ∀ last ∈ state.core.plans,
      first.packet.declaration = last.packet.declaration →
      CentersSame model first.input last.input →
      ∀ name ∈ first.packet.declaration.inputNames,
        Same model (.source (first.binder name)) (.source (last.binder name)))
    (first last : Site roles) (one : first ∈ state.core.sites) (two : last ∈ state.core.sites)
    (identity : first.occurrence.identity = last.occurrence.identity) :
    CentersSame model first last := by
  have byIdentity : ∀ number, ∀ first last : Site roles,
      first ∈ state.core.sites → last ∈ state.core.sites →
      first.occurrence.identity = number →
      first.occurrence.identity = last.occurrence.identity → CentersSame model first last := by
    intro number
    induction number using Nat.strongRecOn with
    | ind number ih =>
      intro first last one two atNumber identity
      rcases GeneralNominalHeadSiteOrigin185.initial_site_origin path first one with rfl | ⟨a,ha,ea⟩
      · rcases GeneralNominalHeadSiteOrigin185.initial_site_origin path last two with rfl | ⟨b,hb,eb⟩
        · exact centers_self model _
        · have rootEq := GeneralNominalHeadRootOverlap185.trace_root_identity path last two identity.symm
          exact False.elim (GeneralNominalHeadSiteCoherence185.emitted_not_root path b hb last eb rootEq)
      · rcases GeneralNominalHeadSiteOrigin185.initial_site_origin path last two with rfl | ⟨b,hb,eb⟩
        · have rootEq := GeneralNominalHeadRootOverlap185.trace_root_identity path first one identity
          exact False.elim (GeneralNominalHeadSiteCoherence185.emitted_not_root path a ha first ea rootEq)
        · obtain ⟨ca,_,rfl⟩ := List.mem_map.mp ea
          obtain ⟨cb,_,rfl⟩ := List.mem_map.mp eb
          have seed := (GeneralNominalHeadSiteOrigin185.plan_seed path a ha).trans
            (GeneralNominalHeadSiteOrigin185.plan_seed path b hb).symm
          obtain ⟨parent,decl,clauses⟩ := GeneralNominalChildCoherence184.producer_declarations
            registry checked a b seed
            ((GeneralNominalHeadSiteCoherence185.registered_producers path).2 a ha).2
            ((GeneralNominalHeadSiteCoherence185.registered_producers path).2 b hb).2
            ca.val cb.val ca.property cb.property _ _ identity
          have smaller := GeneralNominalCenteredWhere.packet_child_above a.packet _
            (GeneralNominalCenteredTrace.clauseChild_mem a.packet ca.val ca.property
              (a.packet.checked.signature.2.2.2 ca.val ca.property))
          have small : a.input.occurrence.identity < number := by
            rw [a.input_exact,← atNumber]
            exact smaller
          have parentCenters := ih a.input.occurrence.identity small a.input b.input
            (GeneralNominalHeadCandidateReadback185.registered_inputs path a ha)
            (GeneralNominalHeadCandidateReadback185.registered_inputs path b hb) rfl
            ((congrArg Occurrence.identity a.input_exact).trans
              (parent.trans (congrArg Occurrence.identity b.input_exact).symm))
          have binders := transfer a ha b hb decl parentCenters
          have sameCenters := GeneralNominalChildSemantic186.child_centers_list a b seed parent decl
            ca.val ca.property (a.packet.checked.signature.2.2.2 ca.val ca.property) model binders
          have sitesEqual : b.childSite cb.val (b.packet.checked.signature.2.2.2 cb.val cb.property) =
              b.childSite ca.val (a.packet.checked.signature.2.2.2 ca.val ca.property) := by
            exact childSite_congr b _ _ clauses.symm _ _
          rw [sitesEqual]
          exact sameCenters
  exact byIdentity first.occurrence.identity first last one two rfl identity

end Yulang.GeneralNominalHeadIdentityInduction186
