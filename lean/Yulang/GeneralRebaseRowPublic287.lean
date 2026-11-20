import Yulang.GeneralRebaseRowPayloadExact287

/-! Raw model/evidence and canonical completion use different supports:
the nominal row's independent field remains public, but completion supplies
the output type itself without rewriting any of the ambient rows. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 14500000
namespace Yulang.GeneralRebaseRowPublic287
open GeneralRebaseRowChildSource287
open GeneralRebaseRowChildRaw287 (SourceCheck OutputCheck before_exact complete_check)
open GeneralRebaseRowParentFrame287 (after after_exact)
open GeneralRebaseRowParentOutput287 (replaceOutput completion_rows completion_types)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedEvidence231 (Evidence)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open CommonNominalFullCarrier

structure InputView where
  inside : Ty
  outside : Ty
  row : Common.Row

def viewOf (a : Assignment) : InputView := ⟨(a 0).1,(a 1).1,(a 0).2⟩

def ValidView (v : InputView) : Prop :=
  Equivalent v.inside (R v.row) ∧ Equivalent v.outside (F v.inside)

def baseFrom (v : InputView) (ambient : Nat → Common.Row) : Assignment :=
  fun n => (if n = 0 then v.inside else if n = 1 then v.outside else .base .int,
    if n = 0 then v.row else ambient n)

def canonical (v : InputView) (ambient : Nat → Common.Row) : Assignment :=
  replaceOutput (baseFrom v ambient)

def Public (v : InputView) (p : Payload) : Prop :=
  ∃ m : Assignment, viewOf m = v ∧ Models (after true) m ∧ Evidence (registry true) (after true).core m root p

theorem input_preserved (v : InputView) (ambient : Nat → Common.Row) : viewOf (canonical v ambient) = v := by
  cases v
  rfl

theorem other_rows (v : InputView) (ambient : Nat → Common.Row) (n : Nat) (h : n ≠ 0) :
    (canonical v ambient n).2 = ambient n := by
  unfold canonical
  rw [completion_rows]
  exact ite_eq_right h

theorem matches_source (a : Assignment) : SourceCheck a ↔ ValidView (viewOf a) := Iff.rfl

theorem canonical_exact (v : InputView) (ambient : Nat → Common.Row) (p : Payload) :
    Models (after true) (canonical v ambient) ∧
      Evidence (registry true) (after true).core (canonical v ambient) root p ↔
    ValidView v ∧ p = .node 0 [.node 1 []] := by
  rw [GeneralRebaseRowPayloadExact287.exact]
  constructor
  · rintro ⟨checked,shape⟩
    have h := (matches_source _).mp checked.1
    rw [input_preserved] at h
    exact ⟨h,shape⟩
  · rintro ⟨checked,shape⟩
    have s : SourceCheck (baseFrom v ambient) := by
      exact checked
    exact ⟨(complete_check _).mpr s,shape⟩

theorem public_exact (v : InputView) (p : Payload) :
    Public v p ↔ ValidView v ∧ p = .node 0 [.node 1 []] := by
  constructor
  · rintro ⟨a,same,held,witness⟩
    have h := (GeneralRebaseRowPayloadExact287.exact a p).mp ⟨held,witness⟩
    exact ⟨same ▸ (matches_source a).mp h.1.1,h.2⟩
  · intro checked
    exact ⟨canonical v (fun _ => Common.rowEmpty),input_preserved _ _,
      (canonical_exact v (fun _ => Common.rowEmpty) p).mpr checked⟩

theorem public_arbitrary_unused_rows (v : InputView) (p : Payload) (ambient : Nat → Common.Row) :
    Public v p ↔ Models (after true) (canonical v ambient) ∧
      Evidence (registry true) (after true).core (canonical v ambient) root p :=
  (public_exact v p).trans (canonical_exact v ambient p).symm

theorem completion_same_assignment_gate (m : Assignment) (p : Payload) :
    Models (after true) (replaceOutput m) ∧
      Evidence (registry true) (after true).core (replaceOutput m) root p ↔
    Models before m ∧ p = .node 0 [.node 1 []] := by
  rw [GeneralRebaseRowPayloadExact287.exact,complete_check,before_exact]

/-- Among assignments already admitted by the source, this whole-type route
does not add an independent ambient-row test while keeping every type fixed. -/
theorem no_new_ambient_row_test (choice : Bool) (a b : Assignment)
    (priorA : Models before a) (priorB : Models before b)
    (types : ∀ n, (a n).1 = (b n).1) :
    Models (after choice) a ↔ Models (after choice) b := by
  rw [after_exact,after_exact]
  unfold OutputCheck
  rw [types 0,types 2]
  have left := (before_exact a).mp priorA
  have right := (before_exact b).mp priorB
  exact and_congr ⟨fun _ => right,fun _ => left⟩ Iff.rfl

end Yulang.GeneralRebaseRowPublic287
