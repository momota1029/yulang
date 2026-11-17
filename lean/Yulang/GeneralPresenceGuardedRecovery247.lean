import Yulang.GeneralPresenceGuardedBlock246
import Yulang.GeneralPresenceCommonLaws245
/-! Every model of the actual compiled guarded block is recovered by its
constructed regular solution up to mutual subtyping. This is not a compiler
for arbitrary source terms or a solver transition termination theorem. -/
namespace Yulang.GeneralPresenceGuardedRecovery247
open Core.PresenceGeneration PresenceNormalForm
open GeneralPresenceDefinitionRewrite244 GeneralPresenceGuardedLayer246
open GeneralPresenceGuardedBlock246
open CommonNominalFullCarrier
variable {Name : Type} [DecidableEq Name]

omit [DecidableEq Name] in
theorem models_equations (body : Body Name nodes parameters) (targets : Fin nodes → Name)
 (parametersAt : Fin parameters → Name) (assignment : Name → Comp model) :
 All model assignment (block (entries body targets parametersAt)) ↔
 CommonNominalFullGuardedClosure.Models (compiled body assignment) (arguments parametersAt assignment)
   (targetValues targets assignment) := by
 constructor
 · intro valid index
   have member : (targets index,translate (Sum.elim targets parametersAt) (body index)) ∈ entries body targets parametersAt :=
     List.mem_ofFn.mpr ⟨index,rfl⟩
   have one := valid (.tyLe (.var (targets index)) (translate (Sum.elim targets parametersAt) (body index)))
     (List.mem_flatMap.mpr ⟨_,member,by simp [equations]⟩)
   have two := valid (.tyLe (translate (Sum.elim targets parametersAt) (body index)) (.var (targets index)))
     (List.mem_flatMap.mpr ⟨_,member,by simp [equations]⟩)
   change Equivalent (assignment (targets index)).1 _
   rw [← eval_equation]
   exact ⟨one,two⟩
 · intro valid atom member
   obtain ⟨entry,entryMem,atomMem⟩ := List.mem_flatMap.mp member
   obtain ⟨index,rfl⟩ := List.mem_ofFn.mp entryMem
   have same := valid index
   rw [← eval_equation] at same
   simp only [equations,List.mem_cons,List.not_mem_nil,or_false] at atomMem
   rcases atomMem with rfl | rfl
   · exact same.1
   · exact same.2

omit [DecidableEq Name] in
theorem recover_values (body : Body Name nodes parameters) (targets : Fin nodes → Name)
 (parametersAt : Fin parameters → Name) (assignment : Name → Comp model)
 (valid : All model assignment (block (entries body targets parametersAt))) (index : Fin nodes) :
 Equivalent (values body parametersAt assignment index) (assignment (targets index)).1 :=
 CommonNominalFullGuardedClosure.all_models_recovered _ _ _ ((models_equations body targets parametersAt assignment).mp valid) index

theorem extend_compatible (body : Body Name nodes parameters) (targets : Fin nodes → Name)
 (injective : Function.Injective targets) (parametersAt : Fin parameters → Name)
 (assignment : Name → Comp model) (valid : All model assignment (block (entries body targets parametersAt))) :
 GeneralPresenceModelCongruence245.Compatible model (extend body targets parametersAt assignment) assignment := by
 intro name
 refine ⟨?_,rfl⟩
 by_cases inside : ∃ index, targets index = name
 · obtain ⟨index,rfl⟩ := inside
   rw [extend_at body targets injective parametersAt assignment index]
   exact recover_values body targets parametersAt assignment valid index
 · rw [extend_outside body targets parametersAt assignment name (fun index equal => inside ⟨index,equal⟩)]
   exact ⟨subtype_refl _,subtype_refl _⟩

/-- Arbitrary consumers are preserved for an already valid block model;
this is different from installing a fresh, unrelated block. -/
theorem all_recovered (body : Body Name nodes parameters) (targets : Fin nodes → Name)
 (injective : Function.Injective targets) (parametersAt : Fin parameters → Name)
 (assignment : Name → Comp model) (valid : All model assignment (block (entries body targets parametersAt)))
 (atoms : List (Atom Name)) :
 All model (extend body targets parametersAt assignment) atoms ↔ All model assignment atoms :=
 GeneralPresenceModelCongruence245.all_iff GeneralPresenceCommonLaws245.common_laws
   (extend_compatible body targets injective parametersAt assignment valid) atoms

theorem recovered_block (body : Body Name nodes parameters) (targets : Fin nodes → Name)
 (injective : Function.Injective targets) (parametersAt : Fin parameters → Name)
 (assignment : Name → Comp model) (valid : All model assignment (block (entries body targets parametersAt))) :
 All model (extend body targets parametersAt assignment) (block (entries body targets parametersAt)) :=
 (all_recovered body targets injective parametersAt assignment valid _).mpr valid
end Yulang.GeneralPresenceGuardedRecovery247
