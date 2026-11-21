import Yulang.GeneralDeclarativeApplyAssoc324
import Yulang.GeneralDeclarativeReobserve324

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRuleSequence324
open GeneralDeclarations (Registry Declaration Checked)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeAssocRule323 (SourceEquation)
open GeneralDeclarativeEntailment320 (appendFacts Holds)
open GeneralDeclarativeApplyAssoc324 (Applies effect)
open GeneralDeclarativeModelStable324 (StableUnder stable_exact)
open GeneralNominalInspection (Interpretation)
open CommonRoleOutermostResolver (Frontier)

structure Occurrence where
  goal : Demand
  declaration : Declaration
  capture : Nat → Capture

def law (r : Registry) (i : Interpretation) (frame : Occurrence) (eq : Equation) : Prop :=
  SourceEquation r i frame.goal frame.declaration frame.capture eq

/-- Finite ordinary rule-application proof, external to the ordinary
state. Each application is justified at the snapshot in which source
observations allowed it. This does not claim that the classification
that produced a rule is still the final classification. -/
inductive AppliesInOrder (r : Registry) (i : Interpretation)
    (choices : State → Demand → Frontier Demand → Prop) : State → List Occurrence → State → Prop where
  | none : AppliesInOrder r i choices s [] s
  | next : Applies s r i (choices s) d impl names place rows →
      AppliesInOrder r i choices (appendFacts s rows) more t →
      AppliesInOrder r i choices s (⟨d,impl,names.input⟩ :: more) t

theorem exact_models (checked : Checked r) (sequence : AppliesInOrder r i choices s frames t) (m) :
    Models t m ↔ Models s m ∧ ∀ frame ∈ frames, ∀ row, law r i frame row → Holds m row := by
  induction sequence with
  | none => simp
  | next applied later ih =>
    rw [ih,effect checked applied m]
    constructor
    · rintro ⟨⟨old,one⟩,rest⟩
      refine ⟨old,?_⟩
      intro frame there row justified
      rcases List.mem_cons.mp there with rfl|inside
      · exact one row justified
      · exact rest frame inside row justified
    · rintro ⟨old,all⟩
      exact ⟨⟨old,all _ List.mem_cons_self⟩,fun fr present => all fr (List.mem_cons_of_mem _ present)⟩

/-- Every genuinely applied ordinary equation remains entailed in the
final state. A separate readback theorem is needed to transport it to
another current occurrence. -/
theorem remains_applied (checked : Checked r) (sequence : AppliesInOrder r i choices s frames t) :
    StableUnder t (fun row => ∃ occurrence ∈ frames, law r i occurrence row) := by
  apply stable_exact.mpr
  rintro row ⟨frame,visited,origin⟩ m valid
  exact ((exact_models checked sequence m).mp valid).2 frame visited row origin

theorem replay_sound (checked : Checked r) (sequence : AppliesInOrder r i choices s frames t)
    (included : (⟨d,impl,old⟩ : Occurrence) ∈ frames)
    (visible : impl ∈ r.declarations)
    (matchesNew : GeneralDeclarativeReobserve324.Reobserves t impl old new) :
    StableUnder t (SourceEquation r i d impl new) :=
  GeneralDeclarativeReobserve324.ordinary_reobserved checked visible matchesNew
    (fun row source => remains_applied checked sequence row ⟨_,included,source⟩)

end Yulang.GeneralDeclarativeRuleSequence324
