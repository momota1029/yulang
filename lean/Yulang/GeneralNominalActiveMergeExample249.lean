import Yulang.GeneralNominalActiveMerge249
import Yulang.GeneralNominalOrderedRefreshPoolLimit248
/-! Two actual propagation primitives, single then repeated capture. The second
uses already reserved owner slots. Source scheduler reachability is separate. -/
namespace Yulang.GeneralNominalActiveMergeExample249
open GeneralDeclarations GeneralNominalAllocation
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalActiveSupport249 GeneralNominalActiveMerge249

def base : GeneralSourceState.State where
 slots := 0
 source := Fin.elim0
 source_injective := by intro i; exact Fin.elim0 i
 rowSource := Fin.elim0
 ordinary := []
 kinds := 0
 shapes := Fin.elim0
 shapes_injective := by intro i; exact Fin.elim0 i
 heads := Fin.elim0
 intervals := []
 heads_sound := by intro assignment valid slot; exact Fin.elim0 slot
 intervals_sound := by intro assignment valid pair present; cases present

def view : GeneralNormalizedObservation.Snapshot base where
 kinds := 0
 shapes := Fin.elim0
 shapes_injective := by intro i; exact Fin.elim0 i
 canonical := by intro kind; exact Fin.elim0 kind
 heads := Fin.elim0
 checked := by intro slot; exact Fin.elim0 slot

def initial : GeneralNominalState.State :=
 { GeneralNominalState.embed base view (fun _ => none) with seed := 10 }
def declaration : Declaration := ⟨0,0,[.var 7],[],[],[]⟩
def oldBindings : Bindings := [(7,(0,1))]
def freshBindings : Bindings := [(7,(0,1)),(7,(1,0))]
def first (registry : Registry) := propagate initial registry 0 declaration oldBindings

theorem active_first (registry : Registry) : activeSources (first registry) = [0,1] := rfl

theorem initial_models (assignment : Assignment) : GeneralNominalState.Models initial assignment := by
 refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
 · intro atom member; cases member
 · intro slot; exact Fin.elim0 slot
 · intro pair member; cases member
 · intro slot; exact Fin.elim0 slot
 · intro atom member; cases member

theorem first_models (registry : Registry) (assignment : Assignment)
 (cross : Compatible freshBindings assignment) : GeneralNominalState.Models (first registry) assignment := by
 apply (propagate_models initial registry 0 declaration oldBindings assignment).mpr
 refine ⟨initial_models assignment,?_,?_⟩
 · intro first one last two same
   exact cross first (by simpa [oldBindings,freshBindings] using Or.inl one)
     last (by simpa [oldBindings,freshBindings] using Or.inl two) same
 · intro atom member; cases member

theorem bounded_reads (registry : Registry) :
 ∀ name ∈ protectedSources (first registry) freshBindings [0,1], name ≤ (first registry).seed := by
 intro name member
 change name ≤ 10
 change name ∈ [0,1,0,1,1,0,0,1] at member
 simp only [List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem second_model (registry : Registry) (assignment : Assignment)
 (cross : Compatible freshBindings assignment) :
 ∃ extended, GeneralNominalState.Models (propagate (first registry) registry 0 declaration freshBindings) extended ∧
   extended 0 = assignment 0 ∧ extended 1 = assignment 1 ∧
   (∀ name, (extended name).2 = (assignment name).2) := by
 obtain ⟨extended,valid,_,kept,rows⟩ := bounded_propagation (first registry) registry 0 declaration freshBindings [0,1]
   (bounded_reads registry) assignment (first_models registry assignment cross) cross
 exact ⟨extended,valid,kept 0 (by simp),kept 1 (by simp),rows⟩

theorem old_pool_insufficient (registry : Registry) (declared : declaration ∈ registry.declarations) :
 ¬ GeneralNominalRebaseDefinitions241.Fresh (first registry).seed 0 declaration.id freshBindings declaration.inputNames
   (GeneralNominalState.sources (first registry)) :=
 GeneralNominalOrderedRefreshPoolLimit248.not_full_pool_fresh initial registry 0 declaration declared oldBindings freshBindings
   7 (by decide) (by decide)
end Yulang.GeneralNominalActiveMergeExample249
