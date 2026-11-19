import Yulang.GeneralRebaseOutputDepthSuccessor271
import Yulang.GeneralRebaseRawIntoFull271

set_option maxRecDepth 24000
set_option maxHeartbeats 2200000
namespace Yulang.GeneralRebaseInstalledReadback271
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedCycles232 (Head Equal Edge Path)
open GeneralNominalRecursiveInspection (Origin)
open GeneralNominalOriginTerms (project)
open GeneralNominalFiniteMeaning (At build project_value)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

theorem source_at (m : Assignment) (n : Nat) (ty : Ty) (equal : Equivalent (m n).1 ty) :
 At m .actual (.source n) ty := by
 refine ⟨⟨_,.source _⟩,?_⟩
 intro actual found
 cases found
 exact equal

theorem at_equal (state : State roles) (x y : Origin) (ty : Ty)
 (first : ∀ m, Models state m → At m .actual x ty)
 (last : ∀ m, Models state m → At m .actual y ty) : Equal state x y := by
 intro m valid
 have a := first m valid
 have b := last m valid
 refine ⟨a.1,b.1,?_⟩
 intro v w xSeen ySeen
 have xSame := a.2 _ xSeen
 have ySame := b.2 _ ySeen
 exact ⟨subtype_trans xSame.1 ySame.2,subtype_trans ySame.1 xSame.2⟩

def next (o : Origin) : Origin := .nominal o 0 0

theorem child_at (m : Assignment) (p : Origin) (child : Ty)
 (known : At m .actual p (nominal 0 [.inl child])) : At m .actual (next p) child :=
 project_value (.nominal 0 1) (by trivial) (fun _ => child) known ⟨0,by decide +kernel⟩

theorem nominal_head (state : State roles) (x : Origin) (ty : Ty)
 (source : ∀ m, Models state m → At m .actual x (nominal 0 [.inl ty])) :
 Head state x (.nominal 0 1) := by
 intro m valid
 exact ⟨(source m valid).1,fun _ seen => ⟨[.inl ty],rfl,(source m valid).2 _ seen⟩⟩

theorem certified_step (state : State roles) (x y : Origin) (ty : Ty)
 (before : ∀ m, Models state m → At m .actual x (nominal 0 [.inl ty]))
 (after : ∀ m, Models state m → At m .actual y ty) : Edge state x y := by
 exact ⟨x,.nominal 0 1,⟨0,by decide +kernel⟩,nominal_head state x ty before,at_equal state x x _ before before,
   at_equal state (next x) y ty (fun m valid => child_at m x ty (before m valid)) after⟩

namespace Actual252
open GeneralDictionaryOutputDepth252 (F P foo_fixed plan)
open GeneralDictionaryOutputDepthInstall252 (installed output_forced installed_model)
open GeneralRebaseNominalOrigin269 (Raw origin)
open GeneralRebaseStructuralOrigin270 (Slots)

theorem output_head (m : Assignment) (valid : Models installed m) : At m .actual (.source 3) P :=
 source_at m 3 P (output_forced m valid)

theorem intermediate (m : Assignment) (valid : Models installed m) :
 At m .actual (next (.source 3)) (nominal 0 [.inl F]) :=
 child_at m (.source 3) _ (output_head m valid)

theorem original_input (m : Assignment) (valid : Models installed m) : At m .actual (.source 2) F :=
 source_at m 2 F (foo_fixed m (valid.2.1 plan List.mem_cons_self).1)

theorem full_path : Path installed (.source 3) (.source 2) :=
 .cons (certified_step installed (.source 3) (next (.source 3)) _ output_head intermediate)
  (.cons (certified_step installed (next (.source 3)) (.source 2) F intermediate original_input) (.nil _))

def outputSlot : Slots installed := ⟨3,by decide +kernel⟩
def inputSlot : Slots installed := ⟨2,by decide +kernel⟩

theorem raw_stops : ∀ target,
 ¬ GeneralNominalMixedRecurrence.Edge (Raw installed) outputSlot target := by
 intro target old
 rcases old with ⟨k,kids,recorded,i,same⟩ | ⟨declaration,recorded,index,meaning⟩
 · have defers : (Raw installed).view.heads outputSlot = .deferred .unresolved := rfl
   rw [defers] at recorded
   cases recorded
 · have missing : (Raw installed).nominals outputSlot = none := rfl
   rw [missing] at recorded
   cases recorded

theorem raw_path_absent : ¬ GeneralNominalMixedRecurrence.Path (Raw installed) outputSlot inputSlot := by
 intro old
 cases old with
 | cons first _ => exact raw_stops _ first

/-- This is a genuine reachable installed journal with a model. The raw
snapshot graph misses an actual full-model output-to-input path. -/
theorem converse_fails :
 (∃ m, Models installed m) ∧ Path installed (origin installed outputSlot) (origin installed inputSlot) ∧
 ¬ GeneralNominalMixedRecurrence.Path (Raw installed) outputSlot inputSlot :=
 ⟨⟨GeneralDictionaryOutputDepth252.model,installed_model⟩,full_path,raw_path_absent⟩

end Actual252
end Yulang.GeneralRebaseInstalledReadback271
