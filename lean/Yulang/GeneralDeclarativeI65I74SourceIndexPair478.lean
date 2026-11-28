import Yulang.GeneralDeclarativeI65I74BeforeCaptureEvent475

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)

/-- The two ordinal namespaces are separate. A pair merely records
coordinates; it is not evidence that a compiler issued the pair. -/
structure SourceIndexPair478 where
  raw : Nat
  author : Nat
  deriving DecidableEq, Repr

def StampedRead.indexPair478 (s : StampedRead) : SourceIndexPair478 := ⟨s.raw,s.author⟩

def recoverOldStamp478 (raw authored : List Equation) (id : SourceIndexPair478) :
    Option StampedRead := do
  let row ← raw[id.raw]?
  if authored[id.author]? = some row then some ⟨id.raw,id.author,row⟩ else none

theorem two_exact_old_coordinates_recover_only_the_literal_equation478
    {raw authored : List Equation} {id : SourceIndexPair478} {out : StampedRead} :
    recoverOldStamp478 raw authored id = some out ↔
      out.indexPair478 = id ∧ raw[id.raw]? = some out.row ∧ authored[id.author]? = some out.row := by
  rcases id with ⟨i,j⟩
  rcases out with ⟨a,b,e⟩
  cases own : raw[i]? with
  | none => simp [recoverOldStamp478,own]
  | some value =>
    constructor
    · intro read
      simp only [recoverOldStamp478,own,bind,Option.bind] at read
      split at read
      · rename_i supported
        cases read
        exact ⟨rfl,rfl,supported⟩
      · cases read
    · rintro ⟨eq,body,backed⟩
      obtain ⟨rfl,rfl⟩ := SourceIndexPair478.mk.inj eq
      have same := Option.some.inj body
      change value = e at same
      subst value
      simp [recoverOldStamp478,own,backed]

def recoverOldStamps478 (raw authored : List Equation) : List SourceIndexPair478 → Option (List StampedRead)
  | [] => some []
  | id :: more => do
    let row ← recoverOldStamp478 raw authored id
    let rest ← recoverOldStamps478 raw authored more
    pure (row :: rest)

inductive PairedOldRows478 (raw authored : List Equation) :
    List SourceIndexPair478 → List StampedRead → Prop
  | nil : PairedOldRows478 raw authored [] []
  | cons {id row ids rows} : row.indexPair478 = id →
      raw[id.raw]? = some row.row → authored[id.author]? = some row.row →
      PairedOldRows478 raw authored ids rows →
      PairedOldRows478 raw authored (id :: ids) (row :: rows)

theorem ordered_old_stamp_recovery_has_independent_exact_replay478
    {raw authored : List Equation} {ids : List SourceIndexPair478} {rows : List StampedRead} :
    recoverOldStamps478 raw authored ids = some rows ↔ PairedOldRows478 raw authored ids rows := by
  constructor
  · intro hit
    induction ids generalizing rows with
    | nil =>
      have empty : rows = [] := Option.some.inj hit.symm
      rw [empty]
      exact .nil
    | cons id ids ih =>
      simp only [recoverOldStamps478,bind,Option.bind] at hit
      cases row : recoverOldStamp478 raw authored id with
      | none => simp [row] at hit
      | some first =>
        cases rest : recoverOldStamps478 raw authored ids with
        | none => simp [row,rest] at hit
        | some tail =>
          have same : first :: tail = rows := by simpa [row,rest] using hit
          subst rows
          obtain ⟨key,l,r⟩ := two_exact_old_coordinates_recover_only_the_literal_equation478.mp row
          exact .cons key l r (ih rest)
  · intro independent
    induction independent with
    | nil => rfl
    | cons key l r _ tail =>
      have first := two_exact_old_coordinates_recover_only_the_literal_equation478.mpr ⟨key,l,r⟩
      simp [recoverOldStamps478,first,tail]

theorem erasing_duplicate_row_payload_fields_loses_no_old_ordered_read478
    (raw authored : List Equation) (rows : List StampedRead) :
    recoverOldStamps478 raw authored (rows.map StampedRead.indexPair478) = some rows ↔
      valid raw authored rows = true := by
  induction rows with
  | nil => exact ⟨fun _ => rfl,fun _ => rfl⟩
  | cons first more ih =>
    constructor
    · intro accepted
      have data := ordered_old_stamp_recovery_has_independent_exact_replay478.mp accepted
      cases data with
      | cons _ rawAt authAt tail =>
        have validTail := ih.mp (ordered_old_stamp_recovery_has_independent_exact_replay478.mpr tail)
        obtain ⟨rawTail,authTail⟩ := Bool.and_eq_true_iff.mp validTail
        change raw[first.raw]? = some first.row at rawAt
        change authored[first.author]? = some first.row at authAt
        simp [valid,checkedSubsequence,rawAt,authAt,rawTail,authTail]
    · intro ready
      have rawAt : raw[first.raw]? = some first.row := by
        exact checkedSubsequence_exact.mp (Bool.and_eq_true_iff.mp ready).1 _
          (List.mem_map.mpr ⟨first,List.mem_cons_self,rfl⟩)
      have authAt : authored[first.author]? = some first.row := by
        exact checkedSubsequence_exact.mp (Bool.and_eq_true_iff.mp ready).2 _
          (List.mem_map.mpr ⟨first,List.mem_cons_self,rfl⟩)
      have validTail : valid raw authored more = true := by
        unfold valid at ready ⊢
        simp only [List.map_cons,checkedSubsequence,Bool.and_eq_true] at ready ⊢
        exact ⟨ready.1.2,ready.2.2⟩
      have head := (two_exact_old_coordinates_recover_only_the_literal_equation478 (id := first.indexPair478)).mpr
        ⟨rfl,rawAt,authAt⟩
      simp [recoverOldStamps478,head,ih.mpr validTail]

theorem recovery_never_reorders_original_pairs478
    {raw authored : List Equation} {pairs : List SourceIndexPair478} {rows : List StampedRead}
    (run : recoverOldStamps478 raw authored pairs = some rows) :
    rows.map StampedRead.indexPair478 = pairs := by
  have independent := ordered_old_stamp_recovery_has_independent_exact_replay478.mp run
  clear run
  induction independent with
  | nil => rfl
  | cons key _ _ _ tail => simp [key,tail]

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
