import Yulang.GeneralFiniteAssignment246
import Yulang.GeneralPresenceGuardedLayer246
import Yulang.GeneralPresenceReadback245
/-! A finite guarded block in actual Presence syntax has a constructed regular
Common model for every outside assignment. No External or source-rank premise
is used. This fragment is not asserted to encode all source operations. -/
namespace Yulang.GeneralPresenceGuardedBlock246
open Core.PresenceGeneration PresenceNormalForm
open GeneralPresenceDefinitionRewrite244
open GeneralPresenceGuardedLayer246
open CommonNominalFullCarrier
variable {Name : Type} [DecidableEq Name]

abbrev Body (Name : Type) (nodes parameters : Nat) := Fin nodes → Layer Name (Fin nodes ⊕ Fin parameters)

def entries (body : Body Name nodes parameters) (targets : Fin nodes → Name) (parametersAt : Fin parameters → Name) : List (Entry Name) :=
 List.ofFn (fun index => (targets index,translate (Sum.elim targets parametersAt) (body index)))

def compiled (body : Body Name nodes parameters) (assignment : Name → Comp model) :
 CommonNominalFullGuardedClosure.Body nodes parameters := fun index => lower assignment (body index)

def arguments (parametersAt : Fin parameters → Name) (assignment : Name → Comp model) : Fin parameters → Ty :=
 fun index => (assignment (parametersAt index)).1

def targetValues (targets : Fin nodes → Name) (assignment : Name → Comp model) : Fin nodes → Ty :=
 fun index => (assignment (targets index)).1

def values (body : Body Name nodes parameters) (parametersAt : Fin parameters → Name)
 (assignment : Name → Comp model) : Fin nodes → Ty :=
 CommonNominalFullGuardedClosure.instantiate (compiled body assignment) (arguments parametersAt assignment)

def extend (body : Body Name nodes parameters) (targets : Fin nodes → Name)
 (parametersAt : Fin parameters → Name) (assignment : Name → Comp model) (name : Name) : Comp model :=
 (GeneralFiniteAssignment246.finite targets (values body parametersAt assignment) (fun name => (assignment name).1) name,
   (assignment name).2)

theorem extend_rows (body : Body Name nodes parameters) (targets : Fin nodes → Name)
 (parametersAt : Fin parameters → Name) (assignment : Name → Comp model) (name : Name) :
 (extend body targets parametersAt assignment name).2 = (assignment name).2 := rfl

theorem extend_at (body : Body Name nodes parameters) (targets : Fin nodes → Name)
 (injective : Function.Injective targets) (parametersAt : Fin parameters → Name)
 (assignment : Name → Comp model) (index : Fin nodes) :
 (extend body targets parametersAt assignment (targets index)).1 = values body parametersAt assignment index :=
 GeneralFiniteAssignment246.finite_at targets injective _ _ index

theorem extend_outside (body : Body Name nodes parameters) (targets : Fin nodes → Name)
 (parametersAt : Fin parameters → Name) (assignment : Name → Comp model) (name : Name)
 (outside : ∀ index, targets index ≠ name) :
 extend body targets parametersAt assignment name = assignment name := by
 apply Prod.ext
 · exact GeneralFiniteAssignment246.finite_outside targets _ _ name outside
 · rfl

omit [DecidableEq Name] in
theorem eval_equation (body : Body Name nodes parameters) (targets : Fin nodes → Name)
 (parametersAt : Fin parameters → Name) (assignment : Name → Comp model) (index : Fin nodes) :
 (translate (Sum.elim targets parametersAt) (body index)).eval model assignment =
 CommonNominalFullGuardedClosure.equation (compiled body assignment) (arguments parametersAt assignment)
   (targetValues targets assignment) index := by
 rw [eval_bridge]
 unfold CommonNominalFullGuardedClosure.equation compiled
 congr 1
 funext reference
 cases reference <;> rfl

theorem compiled_extend (body : Body Name nodes parameters) (targets : Fin nodes → Name)
 (parametersAt : Fin parameters → Name) (assignment : Name → Comp model) :
 compiled body (extend body targets parametersAt assignment) = compiled body assignment := by
 funext index
 exact lower_rows (extend body targets parametersAt assignment) assignment (fun _ => rfl) (body index)

theorem arguments_extend (body : Body Name nodes parameters) (targets : Fin nodes → Name)
 (parametersAt : Fin parameters → Name) (separate : ∀ index parameter, targets index ≠ parametersAt parameter)
 (assignment : Name → Comp model) :
 arguments parametersAt (extend body targets parametersAt assignment) = arguments parametersAt assignment := by
 funext parameter
 exact congrArg Prod.fst (extend_outside body targets parametersAt assignment (parametersAt parameter) (fun index => separate index parameter))

theorem targets_extend (body : Body Name nodes parameters) (targets : Fin nodes → Name)
 (injective : Function.Injective targets) (parametersAt : Fin parameters → Name)
 (assignment : Name → Comp model) :
 targetValues targets (extend body targets parametersAt assignment) = values body parametersAt assignment := by
 funext index
 exact extend_at body targets injective parametersAt assignment index

theorem equation_satisfied (body : Body Name nodes parameters) (targets : Fin nodes → Name)
 (injective : Function.Injective targets) (parametersAt : Fin parameters → Name)
 (separate : ∀ index parameter, targets index ≠ parametersAt parameter)
 (assignment : Name → Comp model) (index : Fin nodes) :
 Equivalent (extend body targets parametersAt assignment (targets index)).1
   ((translate (Sum.elim targets parametersAt) (body index)).eval model (extend body targets parametersAt assignment)) := by
 rw [extend_at body targets injective parametersAt assignment index,eval_equation,
   compiled_extend,arguments_extend body targets parametersAt separate,targets_extend body targets injective]
 exact CommonNominalFullGuardedClosure.all_parameter_sound _ _ index

theorem block_satisfied (body : Body Name nodes parameters) (targets : Fin nodes → Name)
 (injective : Function.Injective targets) (parametersAt : Fin parameters → Name)
 (separate : ∀ index parameter, targets index ≠ parametersAt parameter)
 (assignment : Name → Comp model) :
 All model (extend body targets parametersAt assignment) (block (entries body targets parametersAt)) := by
 intro atom member
 obtain ⟨entry,entryMem,atomMem⟩ := List.mem_flatMap.mp member
 obtain ⟨index,rfl⟩ := List.mem_ofFn.mp entryMem
 have same := equation_satisfied body targets injective parametersAt separate assignment index
 simp only [equations,List.mem_cons,List.not_mem_nil,or_false] at atomMem
 rcases atomMem with rfl | rfl
 · exact same.1
 · exact same.2

theorem arbitrary_public_model (body : Body Name nodes parameters) (targets : Fin nodes → Name)
 (injective : Function.Injective targets) (parametersAt : Fin parameters → Name)
 (separate : ∀ index parameter, targets index ≠ parametersAt parameter)
 (boundary : Name → Comp model) :
 ∃ assignment, All model assignment (block (entries body targets parametersAt)) ∧
   (∀ name, (∀ index, targets index ≠ name) → assignment name = boundary name) ∧
   (∀ name, (assignment name).2 = (boundary name).2) :=
 ⟨extend body targets parametersAt boundary,block_satisfied body targets injective parametersAt separate boundary,
   extend_outside body targets parametersAt boundary,extend_rows body targets parametersAt boundary⟩
end Yulang.GeneralPresenceGuardedBlock246
