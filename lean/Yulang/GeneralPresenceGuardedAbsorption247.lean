import Yulang.GeneralPresenceGuardedRecovery247
namespace Yulang.GeneralPresenceGuardedAbsorption247
open Core.PresenceGeneration
open GeneralPresenceGuardedBlock246 CommonNominalFullCarrier
variable {Name : Type} [DecidableEq Name]

theorem arguments_after (oldParameters : Fin oldCount → Name)
 (fresh : Body Name nodes newCount) (targets : Fin nodes → Name) (newParameters : Fin newCount → Name)
 (separate : ∀ index parameter, targets index ≠ oldParameters parameter)
 (assignment : Name → Comp model) :
 arguments oldParameters (extend fresh targets newParameters assignment) = arguments oldParameters assignment := by
 funext parameter
 exact congrArg Prod.fst (extend_outside fresh targets newParameters assignment (oldParameters parameter)
   (fun index => separate index parameter))

theorem values_after (old : Body Name nodes oldCount) (oldParameters : Fin oldCount → Name)
 (fresh : Body Name nodes newCount) (targets : Fin nodes → Name) (newParameters : Fin newCount → Name)
 (separate : ∀ index parameter, targets index ≠ oldParameters parameter)
 (assignment : Name → Comp model) :
 values old oldParameters (extend fresh targets newParameters assignment) = values old oldParameters assignment := by
 unfold values
 have rows : compiled old (extend fresh targets newParameters assignment) = compiled old assignment := by
   funext index
   exact GeneralPresenceGuardedLayer246.lower_rows (extend fresh targets newParameters assignment) assignment (fun _ => rfl) (old index)
 rw [rows,arguments_after oldParameters fresh targets newParameters separate]

theorem extend_absorbs (old : Body Name nodes oldCount) (oldParameters : Fin oldCount → Name)
 (fresh : Body Name nodes newCount) (targets : Fin nodes → Name) (injective : Function.Injective targets)
 (newParameters : Fin newCount → Name)
 (separate : ∀ index parameter, targets index ≠ oldParameters parameter)
 (assignment : Name → Comp model) :
 extend old targets oldParameters (extend fresh targets newParameters assignment) = extend old targets oldParameters assignment := by
 funext name
 apply Prod.ext
 · by_cases inside : ∃ index, targets index = name
   · obtain ⟨index,rfl⟩ := inside
     rw [extend_at old targets injective,extend_at old targets injective,
       values_after old oldParameters fresh targets newParameters separate]
   · have outside : ∀ index, targets index ≠ name := fun index equal => inside ⟨index,equal⟩
     rw [extend_outside old targets oldParameters _ name outside,
       extend_outside fresh targets newParameters assignment name outside,
       extend_outside old targets oldParameters assignment name outside]
 · rfl

theorem extend_idempotent (body : Body Name nodes parameters) (targets : Fin nodes → Name)
 (injective : Function.Injective targets) (parametersAt : Fin parameters → Name)
 (separate : ∀ index parameter, targets index ≠ parametersAt parameter)
 (assignment : Name → Comp model) :
 extend body targets parametersAt (extend body targets parametersAt assignment) = extend body targets parametersAt assignment :=
 extend_absorbs body parametersAt body targets injective parametersAt separate assignment
end Yulang.GeneralPresenceGuardedAbsorption247
