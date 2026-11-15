import Yulang.GeneralNominalChildSemantic186
import Yulang.GeneralDictionaryDefaultChoice214
import Yulang.GeneralDictionaryDefault214ActualSupport
import Yulang.GeneralDictionaryDefaultProvenance212
import Yulang.GeneralDictionaryDefaultConfiguration209
import Yulang.GeneralNominalHeadSchemaSemantic186

/-! The numeric invocation induction for registered site centers. Its local
binder-transfer premise is isolated from the trace argument; a separate
schema theorem supplies it. No equality of full occurrences is required. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Yulang.GeneralDictionaryDefaultIdentityCenters214
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
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

theorem emitted_above_root
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (plan : Plan roles) (registered : plan ∈ state.core.plans)
    (site : Site roles) (emitted : site ∈ plan.emitted) : root.identity < site.occurrence.identity := by
  have packet := GeneralDictionaryDefault214ActualSupport.registered_packets path plan registered
  have parent := GeneralDictionaryDefaultProvenance212.root_le_registered path plan.packet.site
    (GeneralDictionaryDefaultChoice214.packet_sites path plan.packet packet).1
  obtain ⟨clause,_,rfl⟩ := List.mem_map.mp emitted
  exact Nat.lt_of_le_of_lt parent (GeneralNominalCenteredWhere.packet_child_above plan.packet _
    (GeneralNominalCenteredTrace.clauseChild_mem plan.packet clause.val clause.property
      (plan.packet.checked.signature.2.2.2 clause.val clause.property)))

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
      rcases GeneralDictionaryDefault214ActualSites.initial_site_origin path first one with rfl | ⟨a,ha,ea⟩
      · rcases GeneralDictionaryDefault214ActualSites.initial_site_origin path last two with rfl | ⟨b,hb,eb⟩
        · exact centers_self model _
        · have above := emitted_above_root path b hb last eb
          exact False.elim (Nat.lt_irrefl _ (identity ▸ above))
      · rcases GeneralDictionaryDefault214ActualSites.initial_site_origin path last two with rfl | ⟨b,hb,eb⟩
        · have above := emitted_above_root path a ha first ea
          exact False.elim (Nat.lt_irrefl _ (identity ▸ above))
        · obtain ⟨ca,_,rfl⟩ := List.mem_map.mp ea
          obtain ⟨cb,_,rfl⟩ := List.mem_map.mp eb
          have seed := (GeneralDictionaryDefault214ActualSites.plan_seed path a ha).trans
            (GeneralDictionaryDefault214ActualSites.plan_seed path b hb).symm
          obtain ⟨parent,decl,clauses⟩ := GeneralNominalChildCoherence184.producer_declarations
            registry checked a b seed
            (GeneralDictionaryDefaultChoice214.visible_packets path a.packet (GeneralDictionaryDefault214ActualSupport.registered_packets path a ha))
            (GeneralDictionaryDefaultChoice214.visible_packets path b.packet (GeneralDictionaryDefault214ActualSupport.registered_packets path b hb))
            ca.val cb.val ca.property cb.property _ _ identity
          have smaller := GeneralNominalCenteredWhere.packet_child_above a.packet _
            (GeneralNominalCenteredTrace.clauseChild_mem a.packet ca.val ca.property
              (a.packet.checked.signature.2.2.2 ca.val ca.property))
          have small : a.input.occurrence.identity < number := by
            rw [a.input_exact,← atNumber]
            exact smaller
          have parentCenters := ih a.input.occurrence.identity small a.input b.input
            (GeneralDictionaryDefault214ActualSupport.registered_input path a ha)
            (GeneralDictionaryDefault214ActualSupport.registered_input path b hb) rfl
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

end Yulang.GeneralDictionaryDefaultIdentityCenters214

namespace Yulang.GeneralDictionaryDefaultIdentityCenters214
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralNominalOriginTerms
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

theorem stored_binders_same
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (first last : Plan roles) (one : first ∈ state.core.plans) (two : last ∈ state.core.plans)
    (declaration : first.packet.declaration = last.packet.declaration)
    (valid : Models state model) (centers : CentersSame model first.input last.input)
    (name : Nat) (named : name ∈ first.packet.declaration.inputNames) :
    Same model (.source (first.binder name)) (.source (last.binder name)) := by
  have built := GeneralDictionaryDefaultTrace208.built_trace path
  have a := GeneralDictionaryDefaultConfiguration209.stored built one
  have b := GeneralDictionaryDefaultConfiguration209.stored built two
  exact GeneralNominalHeadSchemaSemantic186.binder_same first last declaration
    (a.2.2.2.trans b.2.2.2.symm) (a.2.2.1.trans b.2.2.1.symm) centers
    (GeneralNominalCenteredHeadMatStepPackets.head_equations (valid.2.2.2.2.1 first one)).2.2
    (GeneralNominalCenteredHeadMatStepPackets.head_equations (valid.2.2.2.2.1 last two)).2.2
    (GeneralDictionaryDefault214ActualReadback.registered_finished path first one) name named

/-- Equal numeric occurrence identity enforces semantic center agreement for
all registered sites in corrected traces. No pointness, whole-occurrence
identity or equal capture report is assumed. -/
theorem registered_identity_centers_same (checked : Checked registry)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (first last : Site roles) (one : first ∈ state.core.sites) (two : last ∈ state.core.sites)
    (identity : first.occurrence.identity = last.occurrence.identity)
    (valid : Models state model) : CentersSame model first last :=
  trace_identity_centers checked path model
    (fun a ha b hb declaration centers name named =>
      stored_binders_same path a b ha hb declaration valid centers name named)
    first last one two identity

theorem registered_identity_binders_same (checked : Checked registry)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (first last : Plan roles) (one : first ∈ state.core.plans) (two : last ∈ state.core.plans)
    (identity : first.packet.site.occurrence.identity = last.packet.site.occurrence.identity)
    (declaration : first.packet.declaration = last.packet.declaration)
    (name : Nat) (named : name ∈ first.packet.declaration.inputNames)
    (valid : Models state model) :
    Same model (.source (first.binder name)) (.source (last.binder name)) := by
  have centers := registered_identity_centers_same checked path first.input last.input
    (GeneralDictionaryDefault214ActualSupport.registered_input path first one)
    (GeneralDictionaryDefault214ActualSupport.registered_input path last two)
    ((congrArg Occurrence.identity first.input_exact).trans
      (identity.trans (congrArg Occurrence.identity last.input_exact).symm)) valid
  exact stored_binders_same path first last one two declaration valid centers name named
end Yulang.GeneralDictionaryDefaultIdentityCenters214
