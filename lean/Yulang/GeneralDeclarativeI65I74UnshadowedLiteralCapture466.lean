import Yulang.GeneralDeclarativeI65I74ReadyHeadCaptureReceipt466

set_option backward.isDefEq.respectTransparency false
namespace Yulang.C466ShadowFreeWritten
open Yulang.GeneralDeclarationPatterns (Pattern normalize normalizeArgs hide)
open Yulang.GeneralDeclarativeI65.I72.WrittenPattern460.PhysicalOrigin (atSource Pose)

def spineTags : Pattern → List Nat
  | .record label _ tail => label :: spineTags tail
  | _ => []

private theorem hide_absent (tag : Nat) (p : Pattern) (absent : tag ∉ spineTags p) :
    hide tag p = p := by
  cases p with
  | record other payload tail =>
    simp only [spineTags,List.mem_cons,not_or] at absent
    simp [hide,absent.1,hide_absent tag tail absent.2]
  | var | app | variant | join => rfl

mutual
/-- A conservative syntax-only fragment: no join and no shadowed field
along any literal record spine. This is not a validity rule. -/
inductive Unshadowed : Pattern → Prop
  | var : Unshadowed (.var name)
  | app : UnshadowedArgs ps → Unshadowed (.app key ps)
  | record : tag ∉ spineTags tail → Unshadowed payload → Unshadowed tail →
      Unshadowed (.record tag payload tail)
  | variant : Unshadowed term → Unshadowed (.variant key term)

inductive UnshadowedArgs : List Pattern → Prop
  | nil : UnshadowedArgs []
  | cons : Unshadowed p → UnshadowedArgs ps → UnshadowedArgs (p::ps)
end

mutual
def checkUnshadowed : Pattern → Bool
  | .var _ => true
  | .app _ ps => checkUnshadowedArgs ps
  | .record key p tail => decide (key ∉ spineTags tail) &&
      (checkUnshadowed p && checkUnshadowed tail)
  | .variant _ p => checkUnshadowed p
  | .join .. => false

def checkUnshadowedArgs : List Pattern → Bool
  | [] => true
  | p::ps => checkUnshadowed p && checkUnshadowedArgs ps
end

mutual
theorem literal_whole_fragment_has_finite_check (p : Pattern) :
    checkUnshadowed p = true ↔ Unshadowed p := by
  cases p with
  | var => exact ⟨fun _ => .var,fun _ => rfl⟩
  | app k ps =>
    rw [checkUnshadowed,all_fragments_have_finite_check]
    exact ⟨.app,fun h => by cases h with | app h => exact h⟩
  | record k p tail =>
    simp only [checkUnshadowed,Bool.and_eq_true,decide_eq_true_eq,
      literal_whole_fragment_has_finite_check p,literal_whole_fragment_has_finite_check tail]
    exact ⟨fun h => .record h.1 h.2.1 h.2.2,fun h => by
      cases h with | record absent a b => exact ⟨absent,a,b⟩⟩
  | variant k p =>
    rw [checkUnshadowed,literal_whole_fragment_has_finite_check]
    exact ⟨.variant,fun h => by cases h with | variant h => exact h⟩
  | join p q =>
    constructor
    · intro no; simp [checkUnshadowed] at no
    · intro no; cases no
termination_by sizeOf p

theorem all_fragments_have_finite_check (ps : List Pattern) :
    checkUnshadowedArgs ps = true ↔ UnshadowedArgs ps := by
  cases ps with
  | nil => exact ⟨fun _ => .nil,fun _ => rfl⟩
  | cons p ps =>
    rw [checkUnshadowedArgs,Bool.and_eq_true,literal_whole_fragment_has_finite_check,
      all_fragments_have_finite_check]
    exact ⟨fun h => .cons h.1 h.2,fun h => by cases h with | cons a b => exact ⟨a,b⟩⟩
termination_by sizeOf ps
end

theorem authored_unshadowed_tree_is_not_renumbered_by_normalization
    {p : Pattern} (h : Unshadowed p) : normalize p = p := by
  exact Unshadowed.rec
    (motive_1 := fun p _ => normalize p = p)
    (motive_2 := fun ps _ => normalizeArgs ps = ps)
    rfl
    (fun _ ih => by simp only [normalize,ih])
    (fun absent _ _ a b => by simp only [normalize,a,b,hide_absent _ _ absent])
    (fun _ ih => by simp only [normalize,ih])
    rfl
    (fun _ _ a b => by simp only [normalizeArgs,a,b])
    h

theorem any_address_in_the_checked_fragment_is_a_genuine_written_address
    {p : Pattern} (h : checkUnshadowed p = true) (loc : List Pose) :
    atSource (normalize p) loc = atSource p loc := by
  rw [authored_unshadowed_tree_is_not_renumbered_by_normalization
    ((literal_whole_fragment_has_finite_check p).mp h)]


open Yulang.C466WrittenBinderCoordinates
open Yulang.GeneralDeclarativeI65.I72.PreparedDeclarations463
open Yulang.GeneralDeclarativeI65.I72.Checker408 (Problem)
open Yulang.GeneralDeclarativeOrigins321 (Supported restriction)
open Yulang.GeneralDeclarativeNestedView332 (Sources)

theorem accepted_ready_capture_point_names_actual_ordinary_row_and_literal_original_unshadowed_binder
    {p : Problem} (tab : CheckedTable p.state.core.current)
    {done : Nat → Prop} {auth : Supported (ordinary p) done}
    (idx : Sources (restriction auth)) (addr : HeadAddress) (keep : List Nat)
    (job : Nat) (r : CheckedCaptureHead p tab)
    (pass : readCaptureFromReadyHead p tab idx addr keep job = some r)
    (unshadowed : checkUnshadowed r.original.orig.original = true) :
    r.original.orig.location = addr ∧
    r.allocated.after.equations[r.allocated.rawOrdinal]? =
      some ⟨r.allocated.target,r.allocated.captured.term⟩ ∧
    atSource r.original.orig.original r.allocated.written =
      some (.var r.allocated.captured.binder) := by
  obtain ⟨actual,_,raw,source⟩ :=
    ready_head_receipt_preserves_actual_source_identity_and_physical_coordinate p tab idx addr keep job r pass
  refine ⟨actual,raw,?_⟩
  rw [← any_address_in_the_checked_fragment_is_a_genuine_written_address unshadowed]
  exact source

end Yulang.C466ShadowFreeWritten
