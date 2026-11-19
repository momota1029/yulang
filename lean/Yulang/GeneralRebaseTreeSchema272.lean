import Yulang.GeneralRebaseTreeExprCompile272
import Yulang.GeneralNominalVersionedPlans231

namespace Yulang.GeneralRebaseTreeSchema272
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalMaterialization (Mode)
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedPlans231 (variables emittedSchema)
open GeneralNominalVersionedFrame231 (binder capture)
open GeneralNominalCenteredHeadMatSchemas (Equation Schema)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralRebaseTreeInterpreter272 (Source Certified)
open GeneralRebaseTreeExprCompile272 (Env Variables Interprets compile compile_sound)
open GeneralRebaseFiniteTree272 (Tree Canonical value)

def identity (plan : Plan roles) (mode : Mode) (name : Nat) : Nat :=
 if name ∈ plan.packet.declaration.outputNames then binder plan name
 else match mode with
 | .actual => binder plan name
 | .lower => ((capture plan.packet).inputs name).1
 | .upper => ((capture plan.packet).inputs name).2

theorem identity_exact (plan : Plan roles) (m : Assignment) (mode : Mode) (id : Nat) :
 variables plan m mode id = (m (identity plan mode id)).1 := by
 unfold variables identity
 by_cases h : id ∈ plan.packet.declaration.outputNames <;> cases mode <;> simp [h] <;> rfl

def environment (plan : Plan roles) (known : Source) : Env :=
 fun mode id => known (identity plan mode id)

theorem environment_sound (plan : Plan roles) (m : Assignment) (known : Source) (checked : Certified m known) :
 Interprets (environment plan known) (variables plan m) := by
 intro mode id t found
 rw [identity_exact]
 exact checked _ t found

def entry (env : Env) (id : Nat) (equation : Equation) : Option Tree :=
 if equation.target = id then compile env equation.mode equation.expression else none

def compute (env : Env) (schema : Schema) (id : Nat) : Option Tree :=
 schema.equations.findSome? (entry env id)

theorem compute_sound (env : Env) (m : Assignment) (vars : Variables) (schema : Schema) (id : Nat)
 (honest : Interprets env vars) (holds : schema.Holds vars m) (tree : Tree)
 (found : compute env schema id = some tree) : Canonical tree ∧ Equivalent (m id).1 (value tree) := by
 obtain ⟨left,equation,right,whereAt,someComputed,_⟩ := List.findSome?_eq_some_iff.mp found
 have present : equation ∈ schema.equations := by
   rw [whereAt]
   exact List.mem_append_right _ List.mem_cons_self
 unfold entry at someComputed
 split at someComputed
 · rename_i same
   have one := compile_sound env vars honest equation.mode equation.expression tree someComputed
   have eval := holds equation present
   change Equivalent (m equation.target).1 _ at eval
   rw [same] at eval
   exact ⟨one.1,subtype_trans eval.1 one.2.1,subtype_trans one.2.2 eval.2⟩
 · contradiction

def enrich (known : Source) (plan : Plan roles) : Source :=
 fun id => (known id).or (compute (environment plan known) (emittedSchema plan) id)

theorem enrich_sound (known : Source) (plan : Plan roles) (m : Assignment)
 (cert : Certified m known) (holds : GeneralNominalVersionedPlans231.Outputs plan m) :
 Certified m (enrich known plan) := by
 intro id tree found
 unfold enrich at found
 cases current : known id with
 | none =>
   exact compute_sound _ m _ _ id (environment_sound plan m known cert) holds tree
     (by simpa [current,Option.or] using found)
 | some live =>
   have same : live = tree := Option.some.inj (by simpa [current,Option.or] using found)
   exact same ▸ cert id live current

theorem enrich_preserves_source (known : Source) (plan : Plan roles) (id : Nat) (tree : Tree)
 (present : known id = some tree) : enrich known plan id = some tree := by simp [enrich,present,Option.or]

def runPlans (known : Source) (plans : List (Plan roles)) : Source := plans.foldl enrich known

theorem runPlans_sound (known : Source) (plans : List (Plan roles)) (m : Assignment)
 (initial : Certified m known) (holds : ∀ plan ∈ plans, GeneralNominalVersionedPlans231.Outputs plan m) :
 Certified m (runPlans known plans) := by
 induction plans generalizing known with
 | nil => exact initial
 | cons p ps ih =>
   apply ih
   · exact enrich_sound known p m initial (holds p List.mem_cons_self)
   · exact fun plan h => holds plan (List.mem_cons_of_mem _ h)

def rounds (state : State roles) : Nat → Source → Source
 | 0,known => known
 | fuel+1,known => rounds state fuel (runPlans known state.plans)

theorem rounds_sound (state : State roles) (m : Assignment) (valid : Models state m)
 (fuel : Nat) (known : Source) (cert : Certified m known) :
 Certified m (rounds state fuel known) := by
 induction fuel generalizing known with
 | zero => exact cert
 | succ n ih =>
   apply ih
   exact runPlans_sound known state.plans m cert (fun plan stored => (valid.2.1 plan stored).2.2)

end Yulang.GeneralRebaseTreeSchema272
