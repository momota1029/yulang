import Yulang.GeneralPresenceGuardedRecovery247
import Yulang.GeneralPresenceConsumerSupport246
/-! Constructive elimination of guarded definitions for consumers that do not
read private type coordinates. Private row-coordinate reads remain permitted.
This is not a claim that every actual source consumer satisfies that condition. -/
namespace Yulang.GeneralPresenceGuardedConsumers247
open Core.PresenceGeneration PresenceNormalForm
open GeneralPresenceDefinitionRewrite244 GeneralPresenceGuardedBlock246
open GeneralPresenceConsumerSupport246
open CommonNominalFullCarrier
variable {Name : Type} [DecidableEq Name]

def OutsideReads (targets : Fin nodes → Name) (atoms : List (Atom Name)) : Prop :=
 ∀ name ∈ listTypedReads atoms, ∀ index, targets index ≠ name

theorem consumers_extend (body : Body Name nodes parameters) (targets : Fin nodes → Name)
 (parametersAt : Fin parameters → Name) (assignment : Name → Comp model)
 (atoms : List (Atom Name)) (outside : OutsideReads targets atoms) :
 All model (extend body targets parametersAt assignment) atoms ↔ All model assignment atoms := by
 apply GeneralPresenceConsumerSupport246.all_iff model (extend body targets parametersAt assignment) assignment (fun _ => rfl)
 intro name member
 exact congrArg Prod.fst (extend_outside body targets parametersAt assignment name (outside name member))

theorem add_definitions (body : Body Name nodes parameters) (targets : Fin nodes → Name)
 (injective : Function.Injective targets) (parametersAt : Fin parameters → Name)
 (separate : ∀ index parameter, targets index ≠ parametersAt parameter)
 (boundary : Name → Comp model) (atoms : List (Atom Name)) (outside : OutsideReads targets atoms) :
 All model boundary atoms ↔
 ∃ assignment, All model assignment (atoms ++ block (entries body targets parametersAt)) ∧
   (∀ name, (∀ index, targets index ≠ name) → assignment name = boundary name) ∧
   (∀ name, (assignment name).2 = (boundary name).2) := by
 constructor
 · intro valid
   refine ⟨extend body targets parametersAt boundary,?_,extend_outside body targets parametersAt boundary,
     extend_rows body targets parametersAt boundary⟩
   exact (all_append model _ atoms _).mpr
     ⟨(consumers_extend body targets parametersAt boundary atoms outside).mpr valid,
       block_satisfied body targets injective parametersAt separate boundary⟩
 · rintro ⟨assignment,valid,kept,rows⟩
   have consumers := ((all_append model assignment atoms _).mp valid).1
   apply (GeneralPresenceConsumerSupport246.all_iff model assignment boundary rows atoms ?_).mp consumers
   intro name member
   exact congrArg Prod.fst (kept name (outside name member))

def outsideCheck (targets : Fin nodes → Name) (atoms : List (Atom Name)) : Bool :=
 (listTypedReads atoms).all fun name => (List.finRange nodes).all fun index => decide (targets index ≠ name)

theorem outsideCheck_exact (targets : Fin nodes → Name) (atoms : List (Atom Name)) :
 outsideCheck targets atoms = true ↔ OutsideReads targets atoms := by
 simp [outsideCheck,OutsideReads]

theorem checked_add_definitions (body : Body Name nodes parameters) (targets : Fin nodes → Name)
 (injective : Function.Injective targets) (parametersAt : Fin parameters → Name)
 (separate : ∀ index parameter, targets index ≠ parametersAt parameter)
 (boundary : Name → Comp model) (atoms : List (Atom Name)) (checked : outsideCheck targets atoms = true) :
 All model boundary atoms ↔
 ∃ assignment, All model assignment (atoms ++ block (entries body targets parametersAt)) ∧
   (∀ name, (∀ index, targets index ≠ name) → assignment name = boundary name) ∧
   (∀ name, (assignment name).2 = (boundary name).2) :=
 add_definitions body targets injective parametersAt separate boundary atoms ((outsideCheck_exact targets atoms).mp checked)
end Yulang.GeneralPresenceGuardedConsumers247
