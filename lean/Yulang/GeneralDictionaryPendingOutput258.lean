import Yulang.GeneralDictionaryOutputDepth252
import Yulang.GeneralDictionaryFastFill258
namespace Yulang.GeneralDictionaryPendingOutput258
open GeneralDictionaryOutputDepth252
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

/-- Slot3 is a requested but unconstrained output in this initial source. -/
def replace (output : Ty) : Assignment :=
 fun name => if name = 3 then (output,(model name).2) else model name

theorem other (output : Ty) (name : Nat) (different : name ≠ 3) : replace output name = model name := by
 simp only [replace,different,ite_false]

theorem target (output : Ty) : (replace output 3).1 = output := rfl

theorem base_models (output : Ty) : GeneralNominalCommonBridge.Models base (replace output) := by
 refine And.intro ?_ (And.intro (by intro _ _ h; cases h) (by intro _ h; cases h))
 intro atom member
 simp only [atoms,List.flatMap_cons,List.flatMap_nil,List.cons_append,List.nil_append,
   GeneralSourceState.equationAtoms,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl <;> exact subtype_refl _

theorem source_models (output : Ty) : GeneralNominalState.Models snapshot (replace output) := by
 refine ⟨base_models output,?_,by intro _ h; cases h⟩
 intro slot d found
 change (if slot = 2 then some foo else none) = some d at found
 split at found
 · rename_i same; subst slot; cases Option.some.inj found
   exact ⟨[.inl S],.cons ⟨subtype_refl _,subtype_refl _⟩ .nil,⟨subtype_refl _,subtype_refl _⟩⟩
 · cases found

theorem initial_models (output : Ty) : GeneralNominalVersionedJournal232.Models initial (replace output) :=
 (GeneralNominalVersionedJournal232.initial_models ..).mpr
   ⟨source_models output,fun _ => ⟨subtype_refl _,subtype_refl _⟩⟩

theorem rhs_fixed (output : Ty) :
 GeneralNominalCenteredHeadMatExpressions.value (GeneralNominalVersionedPlans231.variables plan (replace output)) .actual rhs = P := by
 simp only [GeneralNominalCenteredHeadMatExpressions.value,GeneralNominalCenteredHeadMatExpressions.values]
 change nominal 0 [.inl (nominal 0 [.inl (replace output (GeneralNominalVersionedFrame231.binder plan 0)).1])] = P
 rw [binder_exact]
 rfl

theorem outputs_exact (output : Ty) : GeneralNominalVersionedPlans231.Outputs plan (replace output) ↔ Equivalent output P := by
 unfold GeneralNominalVersionedPlans231.Outputs
 rw [emitted_exact]
 change (∀ equation ∈ ([⟨3,.actual,rhs⟩] : List GeneralNominalCenteredHeadMatSchemas.Equation), equation.Holds _ _) ↔ _
 constructor
 · intro valid
   have one := valid ⟨3,.actual,rhs⟩ (List.mem_singleton_self _)
   change Equivalent output (GeneralNominalCenteredHeadMatExpressions.value _ .actual rhs) at one
   rwa [rhs_fixed] at one
 · intro equal equation member
   cases List.mem_singleton.mp member
   change Equivalent output (GeneralNominalCenteredHeadMatExpressions.value _ .actual rhs)
   rwa [rhs_fixed]
end Yulang.GeneralDictionaryPendingOutput258
