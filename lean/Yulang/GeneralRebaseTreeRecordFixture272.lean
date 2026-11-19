import Yulang.GeneralRebaseTreeConstructors272
import Yulang.GeneralRebaseTreeCoverage272
import Yulang.GeneralRebaseRecordAcyclicFixture271

namespace Yulang.GeneralRebaseTreeRecordFixture272
open CommonNominalFullCarrier
open GeneralNominalRecursiveInspection (Origin Observes)
open GeneralNominalVersionedCycles232 (Cyclic)
open GeneralRebaseFiniteTree272 (Tree Canonical value)
open GeneralRebaseTreeConstructors272 (emptyTree empty_canonical recordTree record_canonical)
open GeneralRebaseTreeInterpreter272 (run inspect Certified)
open GeneralRebaseTreeReadbackState272 (Meaning)
open GeneralRebaseRecordAcyclicFixture271 (journal model full_model)

def middle : Tree := recordTree [3] (fun _ => emptyTree)
def first : Tree := recordTree [2,7] (fun i => if i.val = 0 then middle else emptyTree)

theorem middle_checked : Canonical middle :=
 record_canonical [3] (by simp) _ (fun _ => empty_canonical)

theorem first_checked : Canonical first := by
 apply record_canonical [2,7] (by simp)
 intro i
 split
 · exact middle_checked
 · exact empty_canonical

def term : Nat → Tree | 0 => first | 1 => middle | _ => emptyTree
def source (n : Nat) : Option Tree := some (term n)

theorem cert : Certified model source := by
 intro n t given
 have eq : term n = t := Option.some.inj given
 subst t
 cases n with
 | zero => exact ⟨first_checked,subtype_refl _,subtype_refl _⟩
 | succ n => cases n <;> first
   | exact ⟨middle_checked,subtype_refl _,subtype_refl _⟩
   | exact ⟨empty_canonical,subtype_refl _,subtype_refl _⟩

def hidden : Origin := .structural (.source 0) (.record [7,2,2]) 2
def visible : Origin := .structural (.source 0) (.record [7,2,2]) 1
def nested : Origin := .nominal hidden 937 32

theorem read_visible : run source visible = .found middle := rfl

theorem read_many : run source hidden = .many := rfl

theorem read_nested_many : run source nested = .many := rfl

theorem over_bound : run source (.structural hidden .pair 2) = .absent := rfl

theorem wrong_width : run source (.structural (.source 2) (.record [2]) 0) = .absent := rfl

theorem genuinely_ambiguous : ∀ v, Observes model nested v := by
 have found := GeneralRebaseTreeInterpreter272.run_sound model source cert nested
 rw [read_nested_many] at found
 exact found

theorem actual_no_cycle (o : Origin) : ¬ Cyclic journal o := by
 have uses := GeneralRebaseTreeInterpreter272.inspect_sound journal model full_model source cert o
 rw [GeneralRebaseTreeCoverage272.returns_negative source o ⟨_,rfl⟩] at uses
 exact uses

end Yulang.GeneralRebaseTreeRecordFixture272
