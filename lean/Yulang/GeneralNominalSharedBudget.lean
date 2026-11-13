import Yulang.GeneralNominalSharedSteps

/-! Finite-signature reduction for the shared-origin relation. Packet contexts are
erased using packet_exact. The remaining source hypothesis is a finite cover of
semantic input/output deltas and literal child edges, not a proposed rank. -/
namespace Yulang.GeneralNominalSharedBudget
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSharedSteps
open GeneralNominalCommonBridge (Assignment)

structure Signature (roles : Roles.RoleDecls) where
  parent : Occurrence roles
  children : List (Occurrence roles)
  delta : Assignment → Prop

def Represents (signature : Signature roles) (packet : Packet roles) : Prop :=
  signature.parent = packet.site.occurrence ∧ signature.children = packet.children ∧
    ∀ model, signature.delta model ↔
      GeneralNominalPacketSupport.Inputs packet model ∧ GeneralNominalPacketSupport.Outputs packet model

def Holds (state : Tracked roles) (signature : Signature roles) : Prop :=
  (∀ model, Models state.current model → signature.delta model) ∧
    ∀ child ∈ signature.children, (signature.parent,child) ∈ state.current.edges

theorem holds_monotone (step : Step registry root before after) (known : Holds before signature) :
    Holds after signature :=
  ⟨fun model valid => known.1 model (step_models step model valid),fun child member =>
    at_edges step.choose_spec.2 _ (known.2 child member)⟩

theorem novel_signature (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet)
    (novel : ¬ GeneralNominalFeedbackSteps.Committed state.current packet)
    (represents : Represents signature packet) : ¬ Holds state signature := by
  intro held
  apply novel
  refine ⟨?_,?_⟩
  · intro model valid
    apply (GeneralNominalPacketSupport.packet_exact packet model).mpr
    refine ⟨?_,(represents.2.2 model).mp (held.1 model valid)⟩
    simpa only [enabled.1.2.1] using valid.1
  · intro child member
    simpa only [represents.1] using held.2 child (represents.2.1.symm ▸ member)

theorem installed_signature {roles : Roles.RoleDecls} {signature : Signature roles}
    {packet : Packet roles} {state : Tracked roles}
    (represents : Represents signature packet) (support : List (Occurrence roles)) :
    Holds (install state packet support) signature := by
  have committed := GeneralNominalSharedSteps.installed_committed state packet support
  refine ⟨?_,?_⟩
  · intro model valid
    exact (represents.2.2 model).mpr ((GeneralNominalPacketSupport.packet_exact packet model).mp
      (committed.1 model valid)).2
  · intro child member
    rw [represents.1]
    exact committed.2 child (represents.2.1 ▸ member)

noncomputable def remaining (basis : List (Signature roles)) (state : Tracked roles) : Nat := by
  classical
  exact basis.foldr (fun signature count => if Holds state signature then count else count+1) 0

theorem remaining_monotone (basis : List (Signature roles)) (step : Step registry root before after) :
    remaining basis after ≤ remaining basis before := by
  classical
  induction basis with
  | nil => exact Nat.le_refl _
  | cons signature rest ih =>
    change (if Holds after signature then remaining rest after else remaining rest after+1) ≤
      (if Holds before signature then remaining rest before else remaining rest before+1)
    by_cases old : Holds before signature
    · simp only [old,holds_monotone step old,ite_true]; exact ih
    · by_cases now : Holds after signature <;> simp only [old,now,ite_true,ite_false] <;> omega

theorem remaining_decreases (basis : List (Signature roles)) (step : Step registry root before after)
    (member : signature ∈ basis) (old : ¬ Holds before signature) (now : Holds after signature) :
    remaining basis after < remaining basis before := by
  classical
  induction basis with
  | nil => cases member
  | cons head rest ih =>
    change (if Holds after head then remaining rest after else remaining rest after+1) <
      (if Holds before head then remaining rest before else remaining rest before+1)
    rcases List.mem_cons.mp member with rfl | member
    · have tail := remaining_monotone rest step
      simp only [old,now,ite_true,ite_false]
      omega
    · have tail := ih member
      by_cases was : Holds before head
      · simp only [was,holds_monotone step was,ite_true]; exact tail
      · by_cases is : Holds after head <;> simp only [was,is,ite_true,ite_false] <;> omega

/-- The unresolved source-budget obligation. Every future installation needs
one representative with the same semantic delta and exact emitted edges.
Finiteness of discharge proofs at each snapshot does not construct this list. -/
structure SignatureCover (registry : Registry) (root : Occurrence roles) (start : Tracked roles) where
  basis : List (Signature roles)
  covers : ∀ state, B4Target.Steps (Step registry root) start state →
    ∀ packet : Packet roles, ∀ support,
      Generated state.current root packet.site.occurrence →
      GeneralNominalFeedbackSteps.Installable registry state.current packet →
      ¬ GeneralNominalFeedbackSteps.Committed state.current packet → PacketGuard state packet support →
      ∃ signature ∈ basis, Represents signature packet

theorem accessible_of_signature_cover {roles : Roles.RoleDecls} {registry : Registry}
    {root : Occurrence roles} {start : Tracked roles} (cover : SignatureCover registry root start)
    (formed : SourceFormed registry root start) :
    Acc (fun next current => Step registry root current next) start := by
  have all : ∀ n, ∀ state : Tracked roles, remaining cover.basis state = n →
      SourceFormed registry root state → B4Target.Steps (Step registry root) start state →
      Acc (fun next current => Step registry root current next) state := by
    intro n
    induction Nat.lt_wfRel.wf.apply n with
    | intro n below ih =>
      intro state
      induction passive_accessible registry state with
      | intro state predecessors admin =>
        intro equal current path
        refine Acc.intro state ?_
        intro next step
        have nextFormed := SourceFormed.update current step
        have nextPath := B4Target.Steps.tail path step
        rcases formed_step_cases current step with passive | ⟨packet,support,generated,enabled,novel,guard,rfl⟩
        · have weak := remaining_monotone cover.basis step
          rcases Nat.lt_or_eq_of_le weak with strict | same
          · exact ih _ (equal ▸ strict) next rfl nextFormed nextPath
          · exact admin next passive (same.trans equal) nextFormed nextPath
        · obtain ⟨signature,member,represents⟩ := cover.covers state path packet support generated enabled novel guard
          have strict := remaining_decreases cover.basis step member (novel_signature enabled novel represents)
            (installed_signature represents support)
          exact ih _ (equal ▸ strict) _ rfl nextFormed nextPath
  exact all _ start rfl formed .refl

/-- Exactly the remaining source-to-finite-basis theorem, quantified over
checked registries and the existing empty-journal initial source predicate. -/
def SourceBudget (roles : Roles.RoleDecls) : Prop :=
  ∀ registry, Checked registry → ∀ context (root : Occurrence roles),
    GeneralNominalSourceFormation.InitialSource registry context root →
      Nonempty (SignatureCover registry root (initial context root))

theorem checked_initial_accessible (budget : SourceBudget roles) (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles)) :
    Acc (fun next current => Step registry root current next) (initial context root) := by
  obtain ⟨cover⟩ := budget registry checked context root source
  exact accessible_of_signature_cover cover (.initial context source)

end Yulang.GeneralNominalSharedBudget
