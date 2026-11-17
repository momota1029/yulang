import Yulang.GeneralPresenceOrderedBlock247

/-! A bounded topological producer for actual definition lists. Successful
sorting certifies permutation and SafeOrder. Failure is not source rejection:
cyclic or other unsupported representations may still have semantic models.
Duplicate targets must be handled separately before this producer is used. -/
namespace Yulang.GeneralPresenceOrderedSort247
open Core.PresenceGeneration
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247
open GeneralPresenceUsedSupport245 (typedReads)
variable {Name : Type} [DecidableEq Name]

def readyCheck (entry : Entry Name) (allEntries : List (Entry Name)) : Bool :=
  allEntries.all (fun other => !(typedReads entry.2).contains other.1)

def Ready (entry : Entry Name) (allEntries : List (Entry Name)) : Prop :=
  ∀ other ∈ allEntries, other.1 ∉ typedReads entry.2

theorem ready_exact (entry : Entry Name) (allEntries : List (Entry Name)) :
    readyCheck entry allEntries = true ↔ Ready entry allEntries := by
  simp [readyCheck,Ready]

def select (allEntries : List (Entry Name)) : List (Entry Name) → Option (Entry Name × List (Entry Name))
  | [] => none
  | entry :: rest =>
      if readyCheck entry allEntries then some (entry,rest)
      else match select allEntries rest with
        | none => none
        | some (chosen,remaining) => some (chosen,entry :: remaining)

theorem select_sound (allEntries scan : List (Entry Name))
    (chosen : Entry Name) (remaining : List (Entry Name))
    (found : select allEntries scan = some (chosen,remaining)) :
    Ready chosen allEntries ∧ List.Perm scan (chosen :: remaining) := by
  induction scan generalizing remaining with
  | nil => simp [select] at found
  | cons entry rest ih =>
    by_cases ready : readyCheck entry allEntries = true
    · have equal : entry = chosen ∧ rest = remaining := by simpa [select,ready] using found
      obtain ⟨rfl,rfl⟩ := equal
      exact ⟨(ready_exact _ _).mp ready,List.Perm.refl _⟩
    · cases result : select allEntries rest with
      | none => simp [select,ready,result] at found
      | some pair =>
        obtain ⟨next,tail⟩ := pair
        have equal : next = chosen ∧ entry :: tail = remaining := by
          simpa [select,ready,result] using found
        obtain ⟨rfl,rfl⟩ := equal
        obtain ⟨safe,perm⟩ := ih tail result
        exact ⟨safe,(perm.cons entry).trans (List.Perm.swap _ _ _)⟩

def sortFuel : Nat → List (Entry Name) → Option (List (Entry Name))
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel+1, entries@(_ :: _) =>
      match select entries entries with
      | none => none
      | some (entry,rest) =>
          match sortFuel fuel rest with
          | none => none
          | some sorted => some (entry :: sorted)

def sort (entries : List (Entry Name)) : Option (List (Entry Name)) := sortFuel entries.length entries

theorem sortFuel_sound (fuel : Nat) (entries sorted : List (Entry Name))
    (distinct : (entries.map Prod.fst).Nodup)
    (success : sortFuel fuel entries = some sorted) :
    List.Perm entries sorted ∧ SafeOrder sorted := by
  induction fuel generalizing entries sorted with
  | zero =>
    cases entries with
    | nil =>
      have equal : sorted = [] := by simpa [sortFuel] using success.symm
      subst sorted
      exact ⟨List.Perm.refl _,True.intro⟩
    | cons head rest => simp [sortFuel] at success
  | succ fuel ih =>
    cases entries with
    | nil =>
      have equal : sorted = [] := by simpa [sortFuel] using success.symm
      subst sorted
      exact ⟨List.Perm.refl _,True.intro⟩
    | cons head rest =>
      cases selected : select (head :: rest) (head :: rest) with
      | none => simp [sortFuel,selected] at success
      | some pair =>
        obtain ⟨chosen,remaining⟩ := pair
        cases ordered : sortFuel fuel remaining with
        | none => simp [sortFuel,selected,ordered] at success
        | some tail =>
          have equal : sorted = chosen :: tail := by simpa [sortFuel,selected,ordered] using success.symm
          subst sorted
          obtain ⟨ready,perm⟩ := select_sound (head :: rest) (head :: rest) chosen remaining selected
          have projected := (perm.map Prod.fst).nodup_iff.mp distinct
          have tailDistinct := (List.nodup_cons.mp projected).2
          obtain ⟨tailPerm,tailSafe⟩ := ih remaining tail tailDistinct ordered
          have finalPerm := perm.trans (tailPerm.cons chosen)
          have finalDistinct := (finalPerm.map Prod.fst).nodup_iff.mp distinct
          refine ⟨finalPerm,?_,?_,?_,tailSafe⟩
          · exact ready chosen (finalPerm.mem_iff.mpr (by simp))
          · intro later member same
            exact (List.nodup_cons.mp finalDistinct).1 (List.mem_map.mpr ⟨later,member,same⟩)
          · intro later member
            exact ready later (finalPerm.mem_iff.mpr (List.mem_cons_of_mem _ member))

theorem sort_sound (entries sorted : List (Entry Name))
    (distinct : (entries.map Prod.fst).Nodup) (success : sort entries = some sorted) :
    List.Perm entries sorted ∧ SafeOrder sorted :=
  sortFuel_sound entries.length entries sorted distinct success

theorem reversed_alias_sorted :
    sort ([(3,.var 2),(2,.var 0)] : List (Entry Nat)) = some [(2,.var 0),(3,.var 2)] := rfl

theorem cycle_no_sort :
    sort ([(2,.var 3),(3,.var 2)] : List (Entry Nat)) = none := rfl

/-- Only dependencies on targets in this block must lower the rank. -/
def Ranked (rank : Name → Nat) (entries : List (Entry Name)) : Prop :=
  ∀ entry ∈ entries, ∀ dependency ∈ entries,
    dependency.1 ∈ typedReads entry.2 → rank dependency.1 < rank entry.1

omit [DecidableEq Name] in
theorem minimum_entry (rank : Name → Nat) (entries : List (Entry Name)) (nonempty : entries ≠ []) :
    ∃ entry ∈ entries, ∀ other ∈ entries, rank entry.1 ≤ rank other.1 := by
  induction entries with
  | nil => exact False.elim (nonempty rfl)
  | cons head rest ih =>
    by_cases empty : rest = []
    · subst rest
      refine ⟨head,by simp,?_⟩
      intro other member
      have same : other = head := by simpa using member
      subst other
      exact Nat.le_refl _
    · obtain ⟨least,present,minimal⟩ := ih empty
      by_cases before : rank head.1 ≤ rank least.1
      · refine ⟨head,by simp,?_⟩
        intro other member
        rcases List.mem_cons.mp member with rfl | member
        · exact Nat.le_refl _
        · exact Nat.le_trans before (minimal other member)
      · refine ⟨least,List.mem_cons_of_mem _ present,?_⟩
        intro other member
        rcases List.mem_cons.mp member with rfl | member
        · omega
        · exact minimal other member

omit [DecidableEq Name] in
theorem ranked_ready (rank : Name → Nat) (entries : List (Entry Name))
    (ranked : Ranked rank entries) (nonempty : entries ≠ []) :
    ∃ entry ∈ entries, Ready entry entries := by
  obtain ⟨least,present,minimal⟩ := minimum_entry rank entries nonempty
  refine ⟨least,present,?_⟩
  intro dependency member read
  have lower := ranked least present dependency member read
  have bound := minimal dependency member
  omega

theorem select_complete (allEntries scan : List (Entry Name))
    (available : ∃ entry ∈ scan, Ready entry allEntries) :
    ∃ chosen remaining, select allEntries scan = some (chosen,remaining) := by
  induction scan with
  | nil => simp at available
  | cons head rest ih =>
    by_cases checked : readyCheck head allEntries = true
    · exact ⟨head,rest,by simp [select,checked]⟩
    · have tailAvailable : ∃ entry ∈ rest, Ready entry allEntries := by
        obtain ⟨entry,member,ready⟩ := available
        rcases List.mem_cons.mp member with rfl | member
        · exact False.elim (checked ((ready_exact _ _).mpr ready))
        · exact ⟨entry,member,ready⟩
      obtain ⟨chosen,remaining,selected⟩ := ih tailAvailable
      exact ⟨chosen,head :: remaining,by simp [select,checked,selected]⟩

theorem sortFuel_complete (fuel : Nat) (rank : Name → Nat) (entries : List (Entry Name))
    (ranked : Ranked rank entries) (enough : entries.length ≤ fuel) :
    ∃ sorted, sortFuel fuel entries = some sorted := by
  induction fuel generalizing entries with
  | zero =>
    have empty : entries = [] := List.length_eq_zero_iff.mp (by omega)
    subst entries
    exact ⟨[],rfl⟩
  | succ fuel ih =>
    cases entries with
    | nil => exact ⟨[],rfl⟩
    | cons head rest =>
      obtain ⟨chosen,remaining,selected⟩ := select_complete (head :: rest) (head :: rest)
        (ranked_ready rank (head :: rest) ranked (by simp))
      have permutation := (select_sound (head :: rest) (head :: rest) chosen remaining selected).2
      have tailRanked : Ranked rank remaining := by
        intro entry member dependency present read
        exact ranked entry (permutation.mem_iff.mpr (List.mem_cons_of_mem _ member))
          dependency (permutation.mem_iff.mpr (List.mem_cons_of_mem _ present)) read
      have lengthEqual := permutation.length_eq
      have tailEnough : remaining.length ≤ fuel := by simp only [List.length_cons] at *; omega
      obtain ⟨sorted,success⟩ := ih remaining tailRanked tailEnough
      exact ⟨chosen :: sorted,by simp [sortFuel,selected,success]⟩

/-- A supplied finite dependency ranking guarantees success. Producing that
ranking for actual source operations is a separate obligation. -/
theorem sort_complete (rank : Name → Nat) (entries : List (Entry Name))
    (ranked : Ranked rank entries) : ∃ sorted, sort entries = some sorted :=
  sortFuel_complete entries.length rank entries ranked (Nat.le_refl _)

theorem ranked_sorted (rank : Name → Nat) (entries : List (Entry Name))
    (ranked : Ranked rank entries) (distinct : (entries.map Prod.fst).Nodup) :
    ∃ sorted, sort entries = some sorted ∧ List.Perm entries sorted ∧ SafeOrder sorted := by
  obtain ⟨sorted,success⟩ := sort_complete rank entries ranked
  exact ⟨sorted,success,sort_sound entries sorted distinct success⟩

end Yulang.GeneralPresenceOrderedSort247
