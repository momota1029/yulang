import Yulang.GeneralDeclarativeSourceAdvance325
import Yulang.GeneralDeclarativeOutputIdentity324

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeReplayNames325
open GeneralDeclarations (Checked Declaration)
open GeneralDeclarativeHead320 (State Models byMode)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeTermWalk322 (Walk Binds Occurrence)
open GeneralDeclarativeTermOccurrences322 (source_binders actual_positions)
open GeneralDeclarativeEqualities322 (semantic)
open GeneralDeclarativeEmissionForest322 (children)
open GeneralDeclarativeEmissionOutputs322 (Agree)
open GeneralDeclarativeModelStable324 (StableUnder)
open GeneralDeclarativeAssocRule323 (SourceEquation)
open GeneralDeclarativeReobserve324 (Reobserves ordinary_reobserved)
open GeneralDeclarativeOutputIdentity324 (output_identity)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm eqv_refl)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarationPatterns (Pattern normalize normalizeArgs variablesArgs)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent)
open CommonRoleOutermostResolver (All₂)

def Joint (s : State) (c : GeneralDeclarationPatterns.Constructors) (i : GeneralNominalInspection.Interpretation)
    (old fresh : Nat → Capture) (p : Pattern) : Prop :=
  ∃ exp code uses, translate c i (normalize p) = some code ∧ Walk .actual exp code uses ∧
    Binds s old uses ∧ Binds s fresh uses

/-- The same real normalized ordinary walk supplies the binder positions.
Their names may differ; ordinary derivations force their values to agree.
Inverting the normalized union expression is not used. -/
theorem local_names {s : State} (same : Joint s c i old fresh p)
    (n : Nat) (written : n ∈ (normalize p).variables) (m : Assignment) (valid : Models s m) :
    Equivalent (m (old n).center).1 (m (fresh n).center).1 := by
  obtain ⟨exp,code,uses,built,walk,a,b⟩ := same
  rw [← (source_binders built walk).1] at written
  obtain ⟨o,inWalk,rfl⟩ := List.mem_map.mp written
  have mode := (actual_positions walk).2 o inWalk
  have first := semantic (a o inWalk) m valid
  have last := semantic (b o inWalk) m valid
  simpa only [mode,byMode,GeneralNominalCenteredHeadMatExpressions.value,GeneralDeclarativeHead320.environment]
    using eqv_trans (eqv_symm first) last

theorem all_inputs {s : State} {ps : List Pattern}
    (shared : ∀ p ∈ ps, Joint s c i old fresh p) (m : Assignment) (valid : Models s m) :
    ∀ n ∈ variablesArgs (normalizeArgs ps), Equivalent (m (old n).center).1 (m (fresh n).center).1 := by
  induction ps with
  | nil => intro _ never; cases never
  | cons p ps ih =>
    intro n lexical
    rcases List.mem_append.mp lexical with inHead|later
    · exact local_names (shared p List.mem_cons_self) n inHead m valid
    · exact ih (fun p h => shared p (List.mem_cons_of_mem _ h)) n later

theorem actual_reobserves {s : State}
    (shared : ∀ p ∈ impl.head, Joint s c i old.input fresh.input p)
    (producing : impl.Produced) (oldEnough : Agree impl old) (newEnough : Agree impl fresh)
    (sameChildren : All₂ (fun a b : Demand => a.outputs = b.outputs)
      (children impl old oldPlace) (children impl fresh freshPlace)) :
    Reobserves s impl old.input fresh.input := by
  intro m valid
  refine ⟨all_inputs shared m valid,?_⟩
  intro n out
  rw [oldEnough n out,newEnough n out,output_identity producing sameChildren n out]
  exact eqv_refl _

/-- Stability of the previously applied fixed-target ordinary rule
survives differing input names under an actual shared observation and
the same ordered producing output occurrences. No journal is needed. -/
theorem replay {s : State} (checked : Checked r) (visible : impl ∈ r.declarations)
    (shared : ∀ p ∈ impl.head, Joint s r.constructors i old.input fresh.input p)
    (oldEnough : Agree impl old) (newEnough : Agree impl fresh)
    (sameChildren : All₂ (fun a b : Demand => a.outputs = b.outputs)
      (children impl old oldPlace) (children impl fresh freshPlace))
    (applied : StableUnder s (SourceEquation r i d impl old.input)) :
    StableUnder s (SourceEquation r i d impl fresh.input) :=
  ordinary_reobserved checked visible
    (actual_reobserves shared (checked.2 impl visible).produced oldEnough newEnough sameChildren) applied

end Yulang.GeneralDeclarativeReplayNames325
