import Yulang.GeneralNominalPhaseLabels
import Yulang.GeneralNominalHoleElimination
import Yulang.GeneralNominalSourceFrontier

/-! Fixed-hole phases need finite covers only while their inventory is
unchanged. Genuine eliminations may restart with any finite cover. -/
namespace Yulang.GeneralNominalHolePhases
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalActualInspectionSteps GeneralNominalHoleElimination
open GeneralNominalSharedBudget (Signature Represents remaining remaining_monotone remaining_decreases
  novel_signature installed_signature)

variable {roles : Roles.RoleDecls}

theorem refinement_cases (trace : Trace tests growth before after count) :
    before = after ∨ after.holes.length < before.holes.length := by
  have length := trace_count trace
  cases trace with
  | refl => exact Or.inl rfl
  | next hole value present closed bounded trace =>
    exact Or.inr (by omega)

/-- Only the finite source frontier fixes hole identities. A cover can grow
after a genuine elimination, with no source-wide size bound in this contract. -/
structure PhaseCover (registry : Registry) (context : GeneralNominalCandidates.Context) (root : Occurrence roles) where
  start : Inventory
  tests : List GeneralNominalRecursiveInspection.Test
  holes : start.holes = List.range (GeneralNominalSourceFrontier.frontier context.state).length
  valid : Valid tests start
  invariant : Tracked roles → Inventory → Prop
  initial : invariant (GeneralNominalSupport.initial context root) start
  basis : Inventory → List (Signature roles)
  next : ∀ state, B4Target.Steps (Step registry root) (GeneralNominalSupport.initial context root) state →
    ∀ inventory, invariant state inventory → ∀ after, Step registry root state after →
      ∃ updated growth count, Trace tests growth inventory updated count ∧ invariant after updated
  covers : ∀ state, B4Target.Steps (Step registry root) (GeneralNominalSupport.initial context root) state →
    ∀ inventory, invariant state inventory → ∀ packet : Packet roles, ∀ support,
      Generated state.current root packet.site.occurrence →
      GeneralNominalFeedbackSteps.Installable registry state.current packet →
      ¬ GeneralNominalFeedbackSteps.Committed state.current packet → PacketGuard state packet support →
      ∃ signature ∈ basis inventory, Represents signature packet

inductive History (tests : List GeneralNominalRecursiveInspection.Test) : Inventory → Inventory → Nat → Prop
  | refl (inventory) : History tests inventory inventory 0
  | tail : History tests before middle count → Trace tests growth middle after additions →
      History tests before after (count + additions)

theorem history_count (history : History tests before after count) :
    count + after.holes.length = before.holes.length := by
  induction history with
  | refl => omega
  | tail history update ih => have length := trace_count update; omega

theorem history_valid (history : History tests before after count) (valid : Valid tests before) : Valid tests after := by
  induction history with
  | refl => exact valid
  | tail history update ih => exact trace_valid update ih

theorem replay (cover : PhaseCover registry context (root : Occurrence roles))
    (path : B4Target.Steps (Step registry root) (GeneralNominalSupport.initial context root) state) :
    ∃ inventory count, History cover.tests cover.start inventory count ∧
      cover.invariant state inventory ∧ count ≤ cover.start.holes.length ∧ Valid cover.tests inventory := by
  have run : ∀ state, B4Target.Steps (Step registry root) (GeneralNominalSupport.initial context root) state →
      ∃ inventory count, History cover.tests cover.start inventory count ∧ cover.invariant state inventory := by
    intro state trace
    induction trace with
    | refl => exact ⟨cover.start,0,.refl _,cover.initial⟩
    | @tail before after trace step ih =>
      obtain ⟨inventory,count,history,invariant⟩ := ih
      obtain ⟨updated,growth,additions,update,next⟩ := cover.next before trace inventory invariant after step
      exact ⟨updated,count+additions,.tail history update,next⟩
  obtain ⟨inventory,count,history,invariant⟩ := run state path
  exact ⟨inventory,count,history,invariant,by have length := history_count history; omega,history_valid history cover.valid⟩

theorem accessible (cover : PhaseCover registry context (root : Occurrence roles))
    (source : GeneralNominalSourceFormation.InitialSource registry context root) :
    Acc (fun next current => Step registry root current next) (GeneralNominalSupport.initial context root) := by
  have all : ∀ h, ∀ inventory : Inventory, inventory.holes.length = h →
      ∀ state, B4Target.Steps (Step registry root) (GeneralNominalSupport.initial context root) state → cover.invariant state inventory →
      Acc (fun next current => Step registry root current next) state := by
    intro h
    induction Nat.lt_wfRel.wf.apply h with
    | intro h below outer =>
      intro inventory height
      have phase : ∀ n, ∀ state : Tracked roles, remaining (cover.basis inventory) state = n →
          B4Target.Steps (Step registry root) (GeneralNominalSupport.initial context root) state → cover.invariant state inventory →
          Acc (fun next current => Step registry root current next) state := by
        intro n
        induction Nat.lt_wfRel.wf.apply n with
        | intro n below inner =>
          intro state
          induction GeneralNominalSharedSteps.passive_accessible registry state with
          | intro state predecessors admin =>
            intro equal path invariant
            refine Acc.intro state ?_
            intro after step
            have nextPath := B4Target.Steps.tail path step
            obtain ⟨updated,growth,count,trace,next⟩ := cover.next state path inventory invariant after step
            rcases refinement_cases trace with same | less
            · subst updated
              have formed := GeneralNominalActualTraceSupport.formed_trace (.initial context source) path
              rcases GeneralNominalActualBudget.formed_step_cases formed step with passive | ⟨packet,support,generated,enabled,novel,guard,rfl⟩
              · have weak := remaining_monotone (cover.basis inventory) (step_shared step)
                rcases Nat.lt_or_eq_of_le weak with strict | same
                · exact inner _ (equal ▸ strict) _ rfl nextPath next
                · exact admin after passive (same.trans equal) nextPath next
              · obtain ⟨signature,member,represents⟩ := cover.covers state path inventory invariant packet support generated enabled novel guard
                have strict := remaining_decreases (cover.basis inventory) (step_shared step) member
                  (novel_signature enabled novel represents) (installed_signature represents support)
                exact inner _ (equal ▸ strict) _ rfl nextPath next
            · exact outer _ (height ▸ less) updated rfl after nextPath next
      intro state path invariant
      exact phase _ state rfl path invariant
  exact all _ cover.start rfl _ .refl cover.initial

/-- A source-wide cover implies the phase criterion by using no eliminations.
The reverse implication is not assumed. -/
def of_signature_cover (cover : GeneralNominalActualBudget.SignatureCover registry root (GeneralNominalSupport.initial context root)) :
    PhaseCover registry context (root : Occurrence roles) where
  start := ⟨List.range (GeneralNominalSourceFrontier.frontier context.state).length,[],0⟩
  tests := []
  holes := rfl
  valid := ⟨List.nodup_range,by intro term member; cases member⟩
  invariant := fun _ _ => True
  initial := trivial
  basis := fun _ => cover.basis
  next := fun _ _ inventory _ _ _ => ⟨inventory,(fun _ => 0),0,.refl _,trivial⟩
  covers := fun state path _ _ packet support generated enabled novel guard =>
    cover.covers state path packet support generated enabled novel guard

theorem of_depth_bound (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (depth : GeneralNominalInvocationAncestry.InstalledDepthBound registry context root limit) :
    Nonempty (PhaseCover registry context root) :=
  ⟨of_signature_cover (GeneralNominalActualBudget.signatureCover checked source depth)⟩

def ClassPHolePhases (roles : Roles.RoleDecls) : Prop :=
  ∀ registry, Checked registry → ∀ context (root : Occurrence roles),
    GeneralNominalSourceFormation.InitialSource registry context root → GeneralNominalActualBudget.PointSource context root →
      Nonempty (PhaseCover registry context root)

theorem class_p_accessible (phases : ClassPHolePhases roles) (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (point : GeneralNominalActualBudget.PointSource context root) :
    Acc (fun next current => Step registry root current next) (GeneralNominalSupport.initial context root) := by
  obtain ⟨cover⟩ := phases registry checked context root source point
  exact accessible cover source

theorem invocation_bound_implies_phases (bounded : GeneralNominalActualBudget.ClassPInvocationBound roles) :
    ClassPHolePhases roles := by
  intro registry checked context root source point
  obtain ⟨limit,depth⟩ := bounded registry checked context root source point
  exact of_depth_bound checked source depth

end Yulang.GeneralNominalHolePhases
