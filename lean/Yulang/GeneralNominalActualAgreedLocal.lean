import Yulang.GeneralNominalActualBoundary
import Yulang.GeneralNominalSharedPositive

/-! Policy-parametric operational agreement. Residual installation gaps are
kept explicit; their absence is a separate source-completeness obligation. -/
namespace Yulang.GeneralNominalActualAgreedLocal
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalDemandMerging
open CommonRoleOutermostResolver (Frontier)

abbrev vocabulary := GeneralNominalActualBoundary.vocabulary
abbrev GapPredicate (roles : Roles.RoleDecls) := Registry → Tracked roles → Occurrence roles → Prop

def Installable (registry : Registry) (state : Tracked roles) (packet : Packet roles) : Prop :=
  GeneralNominalFeedbackSteps.Installable registry state.current packet ∧
    ∃ support, GeneralNominalActualInspectionSteps.PacketGuard state packet support

def Available (registry : Registry) (state : Tracked roles) (root : Occurrence roles)
    (key : Nat) (children : List (Occurrence roles)) : Prop :=
  ∃ packet : Packet roles, packet.site.occurrence = root ∧ packet.declaration.id = key ∧
    packet.children = children ∧ (Installable registry state packet ∨
      (packet.registry = registry ∧ packet ∈ state.current.packets ∧
       GeneralNominalFeedbackSteps.Committed state.current packet))

/-- The reported site and every inspected alternative are explicit witnesses. -/
def InspectedCycle (registry : Registry) (state : Tracked roles) (root : Occurrence roles) : Prop :=
  ∃ site ∈ state.current.sites, site.occurrence = root ∧
    ∃ declaration ∈ registry.declarations,
      ∃ checked : DeclarationChecked registry.constructors roles declaration,
        declaration.role = root.demand.role ∧
        GeneralNominalRecursiveCandidates.HeadReady registry state.current.context root declaration ∧
        ∃ bounds, GeneralNominalRecursiveCandidates.arguments state.current.context root = some bounds ∧
          ∃ entry ∈ (GeneralNominalActualInspectionSteps.inspection state.current
            ⟨registry,state.current.context,site,declaration,checked,bounds⟩).tests,
            GeneralNominalActualInspectionSteps.Cyclic state.current entry.1

abbrev OldFields (roles : Roles.RoleDecls) := GeneralNominalFeedbackK2.fields roles
abbrev OldUnique (registry : Registry) (state : Tracked roles) (root : Occurrence roles) :=
  GeneralNominalLocalBoundary.Unique (OldFields roles) registry state.current root

def Blocked (registry : Registry) (state : Tracked roles) (root : Occurrence roles) : Prop :=
  ∃ key children, OldUnique registry state root key children ∧ ¬ Available registry state root key children

/-- A concrete missing-sharing predicate, independent of the policy choice.
Other installation premises are deliberately not called provenance. -/
def ProvenanceGap (registry : Registry) (state : Tracked roles) (root : Occurrence roles) : Prop :=
  ∃ packet : Packet roles, GeneralNominalFeedbackSteps.Installable registry state.current packet ∧
    packet.site.occurrence = root ∧
    (¬ GeneralNominalSharedCaptures.GenerationGuard state packet ∨
      ¬ GeneralNominalSharedCaptures.InputCoherence packet)

def ResidualGap (gap : GapPredicate roles) (registry : Registry) (state : Tracked roles)
    (root : Occurrence roles) : Prop := Blocked registry state root ∧ ¬ gap registry state root

theorem leaf_certificates (state : Tracked roles) (packet : Packet roles)
    (leaf : packet.declaration.requirements = []) :
    GeneralNominalSharedCaptures.GenerationGuard state packet ∧
      GeneralNominalSharedCaptures.InputCoherence packet :=
  ⟨GeneralNominalSharedCaptures.no_children_guard leaf,
    GeneralNominalSharedPositive.leaf_input_coherent packet leaf⟩

theorem leaf_registry_no_gap
    (leaves : ∀ declaration ∈ registry.declarations, declaration.requirements = []) :
    ¬ ProvenanceGap registry state root := by
  rintro ⟨packet,enabled,_,missing⟩
  have certificates := leaf_certificates state packet (leaves packet.declaration enabled.1.2.2.2.1)
  exact missing.elim (fun no => no certificates.1) (fun no => no certificates.2)

def fields (defer : Bool) (gap : GapPredicate roles) : GeneralNominalLocalBoundary.Fields (vocabulary roles) :=
  { GeneralNominalValueBoundary.fields roles with
    CandidateK2 := fun registry state root =>
      GeneralNominalFeedbackK2.CandidateK2 registry state.current root ∨ InspectedCycle registry state root
    InspectionPending := fun registry state root =>
      (OldFields roles).InspectionPending registry state.current root ∨
      (¬ GeneralNominalSharedSupport.DecisionGuard registry state root) ∨
      ResidualGap gap registry state root ∨
      (defer = true ∧ Blocked registry state root ∧ gap registry state root) }

abbrev Local (defer : Bool) (gap : GapPredicate roles) (registry : Registry) (state : Tracked roles) :=
  GeneralNominalLocalBoundary.Local (fields defer gap) registry state

theorem local_functional (one : Local defer gap registry state root first)
    (two : Local defer gap registry state root last) : first = last :=
  GeneralNominalLocalBoundary.local_functional one two

theorem local_total (defer : Bool) (gap : GapPredicate roles) (registry : Registry)
    (checked : Checked registry) (state : Tracked roles) (root : Occurrence roles) :
    ∃ frontier, Local defer gap registry state root frontier :=
  GeneralNominalLocalBoundary.local_total (fun key first last one two =>
    GeneralNominalRecursiveCandidates.survivor_children_functional registry checked state.current.context root
      key first last one two)

theorem selected_old (selected : Local defer gap registry state root (.selected key children)) :
    GeneralNominalFeedbackK2.Local registry state.current root (.selected key children) := by
  cases selected with
  | selected safe unique =>
    exact .selected ⟨safe.1,safe.2.1,fun cycle => safe.2.2.1 (Or.inl cycle),
      fun pending => safe.2.2.2 (Or.inl pending)⟩ unique

theorem selected_available (policy : defer = true ∨ ¬ gap registry state root)
    (selected : Local defer gap registry state root (.selected key children)) :
    Available registry state root key children := by
  classical
  cases selected with
  | selected safe unique =>
    apply Classical.byContradiction
    intro absent
    have blocked : Blocked registry state root := ⟨key,children,unique,absent⟩
    by_cases missing : gap registry state root
    · have lazy : defer = true := policy.resolve_right (fun no => no missing)
      exact safe.2.2.2 (Or.inr (Or.inr (Or.inr ⟨lazy,blocked,missing⟩)))
    · exact safe.2.2.2 (Or.inr (Or.inr (Or.inl ⟨blocked,missing⟩)))

theorem available_not_blocked (unique : OldUnique registry state root key children)
    (available : Available registry state root key children) : ¬ Blocked registry state root := by
  rintro ⟨other,ds,also,absent⟩
  obtain ⟨rfl,rfl⟩ := unique.2 _ _ also.1
  exact absent available

theorem selected_of_available (selected : GeneralNominalFeedbackK2.Local registry state.current root (.selected key children))
    (safeActual : ¬ InspectedCycle registry state root)
    (justified : GeneralNominalSharedSupport.DecisionGuard registry state root)
    (available : Available registry state root key children) :
    Local defer gap registry state root (.selected key children) := by
  cases selected with
  | selected safe unique =>
    have unblocked := available_not_blocked unique available
    refine .selected ⟨safe.1,safe.2.1,?_,?_⟩ unique
    · exact fun cycle => cycle.elim safe.2.2.1 safeActual
    · rintro (pending | unsupported | residual | delayed)
      · exact safe.2.2.2 pending
      · exact unsupported justified
      · exact unblocked residual.1
      · exact unblocked delayed.2.1

theorem selected_iff (policy : defer = true ∨ ¬ gap registry state root) :
    Local defer gap registry state root (.selected key children) ↔
      GeneralNominalFeedbackK2.Local registry state.current root (.selected key children) ∧
      ¬ InspectedCycle registry state root ∧
      GeneralNominalSharedSupport.DecisionGuard registry state root ∧ Available registry state root key children := by
  constructor
  · intro selected
    refine ⟨selected_old selected,?_,?_,selected_available policy selected⟩
    · cases selected with
      | selected safe _ => exact fun cycle => safe.2.2.1 (Or.inr cycle)
    · apply Classical.byContradiction
      intro unsupported
      cases selected with
      | selected safe _ => exact safe.2.2.2 (Or.inr (Or.inl unsupported))
  · rintro ⟨old,safe,justified,available⟩
    exact selected_of_available old safe justified available

theorem installable_selected (enabled : Installable registry state packet)
    (safeActual : ¬ InspectedCycle registry state packet.site.occurrence) :
    Local defer gap registry state packet.site.occurrence (.selected packet.declaration.id packet.children) := by
  have justified : GeneralNominalSharedSupport.DecisionGuard registry state packet.site.occurrence := by
    obtain ⟨support,guard⟩ := enabled.2
    simpa only [enabled.1.1.1,enabled.1.1.2.1] using guard.1.2.1
  exact selected_of_available enabled.1.2.1 safeActual justified ⟨packet,rfl,rfl,rfl,Or.inl enabled⟩

theorem installable_site_acyclic {roles : Roles.RoleDecls} {state : Tracked roles}
    {packet : Packet roles}
    {bounds : List (GeneralNominalInspection.Bounds state.current.context.state)}
    (enabled : Installable registry state packet)
    (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (role : declaration.role = packet.site.occurrence.demand.role)
    (ready : GeneralNominalRecursiveCandidates.HeadReady registry state.current.context packet.site.occurrence declaration)
    (located : GeneralNominalRecursiveCandidates.arguments state.current.context packet.site.occurrence = some bounds)
    (member : entry ∈ (GeneralNominalActualInspectionSteps.inspection state.current
      ⟨registry,state.current.context,packet.site,declaration,checked,bounds⟩).tests) :
    ¬ GeneralNominalActualInspectionSteps.Cyclic state.current entry.1 := by
  obtain ⟨base,support,guard⟩ := enabled
  have alternatives : GeneralNominalActualInspectionSteps.AlternativesSafe registry state.current packet.site := by
    simpa only [base.1.1] using guard.2.2
  exact ((alternatives declaration visible checked role ready bounds located).2 entry member).2

/-- This additional premise concerns site registration, not a new K2 rule. -/
theorem installable_selected_unique_site (enabled : Installable registry state packet)
    (oneSite : ∀ site ∈ state.current.sites, site.occurrence = packet.site.occurrence → site = packet.site) :
    Local defer gap registry state packet.site.occurrence (.selected packet.declaration.id packet.children) := by
  apply installable_selected enabled
  rintro ⟨site,registered,same,declaration,visible,checked,role,ready,bounds,located,entry,member,cycle⟩
  obtain rfl := oneSite site registered same
  exact installable_site_acyclic enabled visible checked role ready located member cycle

theorem inspected_cycle_rejected (known : ¬ GeneralNominalState.RootPending state.current.context.state root.demand)
    (cycle : InspectedCycle registry state root) : Local defer gap registry state root .rejected :=
  .rejected ⟨known,Or.inr (Or.inl (Or.inr cycle))⟩

theorem initial_installable_selected
    (enabled : Installable registry (GeneralNominalSupport.initial context root) packet) :
    Local defer gap registry (GeneralNominalSupport.initial context root) packet.site.occurrence
      (.selected packet.declaration.id packet.children) := by
  apply installable_selected_unique_site enabled
  intro site member _
  have packetSite : packet.site = pointSite root := List.mem_singleton.mp enabled.1.1.2.2.1
  exact (List.mem_singleton.mp member).trans packetSite.symm

theorem candidate_cycle_at_site_blocks {roles : Roles.RoleDecls} {state : Tracked roles}
    {support : List (Occurrence roles)}
    {packet : Packet roles}
    {bounds : List (GeneralNominalInspection.Bounds state.current.context.state)}
    (visible : declaration ∈ packet.registry.declarations)
    (checked : DeclarationChecked packet.registry.constructors roles declaration)
    (role : declaration.role = packet.site.occurrence.demand.role)
    (ready : GeneralNominalRecursiveCandidates.HeadReady packet.registry state.current.context packet.site.occurrence declaration)
    (located : GeneralNominalRecursiveCandidates.arguments state.current.context packet.site.occurrence = some bounds)
    (member : entry ∈ (GeneralNominalActualInspectionSteps.inspection state.current
      ⟨packet.registry,state.current.context,packet.site,declaration,checked,bounds⟩).tests)
    (cycle : GeneralNominalActualInspectionSteps.Cyclic state.current entry.1) :
    ¬ GeneralNominalActualInspectionSteps.PacketGuard state packet support := by
  intro guard
  exact ((guard.2.2 declaration visible checked role ready bounds located).2 entry member).2 cycle

theorem root_cycle_rejected (cycle : GeneralNominalFeedbackK2.RootK2 state.current root) :
    Local defer gap registry state root .rejected :=
  .rejected ⟨GeneralNominalFeedbackK2.root_ready cycle,Or.inl cycle⟩

theorem candidate_cycle_exact : (fields defer gap).CandidateK2 registry state root ↔
    GeneralNominalFeedbackK2.CandidateK2 registry state.current root ∨ InspectedCycle registry state root := Iff.rfl

theorem support_pending
    (known : ¬ (fields defer gap).RootPending registry state root)
    (unsupported : ¬ GeneralNominalSharedSupport.DecisionGuard registry state root)
    (noRoot : ¬ (fields defer gap).RootK2 registry state root)
    (noCycle : ¬ (fields defer gap).CandidateK2 registry state root) :
    Local defer gap registry state root .pending :=
  .inspectionPending known (Or.inr (Or.inl unsupported)) noRoot noCycle

theorem rejected_exact : Local defer gap registry state root .rejected ↔
    ¬ (fields defer gap).RootPending registry state root ∧
      (GeneralNominalFeedbackK2.RootK2 state.current root ∨
       GeneralNominalFeedbackK2.CandidateK2 registry state.current root ∨
       InspectedCycle registry state root ∨
       (¬ (fields defer gap).InspectionPending registry state root ∧
         ∀ key children, ¬ (fields defer gap).Survivor registry state root key children)) := by
  constructor
  · intro localRule
    cases localRule with
    | rejected reason =>
      rcases reason with ⟨known,root | (legacy | actual) | empty⟩
      · exact ⟨known,Or.inl root⟩
      · exact ⟨known,Or.inr (Or.inl legacy)⟩
      · exact ⟨known,Or.inr (Or.inr (Or.inl actual))⟩
      · exact ⟨known,Or.inr (Or.inr (Or.inr empty))⟩
  · rintro ⟨known,root | legacy | actual | empty⟩
    · exact .rejected ⟨known,Or.inl root⟩
    · exact .rejected ⟨known,Or.inr (Or.inl (Or.inl legacy))⟩
    · exact .rejected ⟨known,Or.inr (Or.inl (Or.inr actual))⟩
    · exact .rejected ⟨known,Or.inr (Or.inr empty)⟩

theorem pending_exact : Local defer gap registry state root .pending ↔
    (fields defer gap).RootPending registry state root ∨
      (¬ (fields defer gap).RootPending registry state root ∧
       (fields defer gap).InspectionPending registry state root ∧
       ¬ (fields defer gap).RootK2 registry state root ∧
       ¬ (fields defer gap).CandidateK2 registry state root) := by
  constructor
  · intro localRule
    cases localRule with
    | pending pending => exact Or.inl pending
    | inspectionPending known pending root candidate => exact Or.inr ⟨known,pending,root,candidate⟩
  · rintro (pending | ⟨known,pending,root,candidate⟩)
    · exact .pending pending
    · exact .inspectionPending known pending root candidate

theorem local_transport_pending
    (pending : (fields first gap).InspectionPending registry state root ↔
      (fields last gap).InspectionPending registry state root)
    (localRule : Local first gap registry state root frontier) : Local last gap registry state root frontier := by
  cases localRule with
  | pending h => exact .pending h
  | inspectionPending known h root candidate =>
      exact .inspectionPending known (pending.mp h) root candidate
  | rejected reason =>
      rcases reason with ⟨known,root | candidate | ⟨noPending,empty⟩⟩
      · exact .rejected ⟨known,Or.inl root⟩
      · exact .rejected ⟨known,Or.inr (Or.inl candidate)⟩
      · exact .rejected ⟨known,Or.inr (Or.inr ⟨fun h => noPending (pending.mpr h),empty⟩)⟩
  | ambiguous safe one two distinct =>
      exact .ambiguous ⟨safe.1,safe.2.1,safe.2.2.1,fun h => safe.2.2.2 (pending.mpr h)⟩ one two distinct
  | selected safe unique =>
      exact .selected ⟨safe.1,safe.2.1,safe.2.2.1,fun h => safe.2.2.2 (pending.mpr h)⟩ unique

theorem policies_agree (complete : ¬ gap registry state root) :
    Local true gap registry state root frontier ↔ Local false gap registry state root frontier := by
  have pending : (fields true gap).InspectionPending registry state root ↔
      (fields false gap).InspectionPending registry state root := by
    change (_ ∨ _ ∨ _ ∨ (true = true ∧ _ ∧ _)) ↔ (_ ∨ _ ∨ _ ∨ (false = true ∧ _ ∧ _))
    simp only [complete,and_false,or_false]
  exact ⟨local_transport_pending pending,local_transport_pending pending.symm⟩

end Yulang.GeneralNominalActualAgreedLocal
