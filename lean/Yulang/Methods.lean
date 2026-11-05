import Yulang.CastGraph

/-!
# Order-independent method selection for union receivers

The input is a finite list of resolved union member types and the result of
method lookup on each member. Lookup priority, module visibility, reference
unwrapping, and unresolved receiver variables belong to the caller. Repeated
occurrences of the same member type do not create another candidate.

Selection distinguishes zero candidates, one distinct candidate, and at least
two distinct candidates. It never uses list order to break ambiguity.
-/

namespace Yulang.Methods

inductive Selection (α : Type u) where
  | missing
  | unique (receiver : α)
  | ambiguous
  deriving DecidableEq, Repr

def AllEqual [DecidableEq α] (members : List α) (receiver : α) : Bool :=
  members.all (fun member => decide (member = receiver))

def select [DecidableEq α] : List α → Selection α
  | [] => .missing
  | receiver :: rest => if AllEqual rest receiver then .unique receiver else .ambiguous

/-- One distinct candidate; duplicate list occurrences are immaterial. -/
def Unique (members : List α) (receiver : α) : Prop :=
  receiver ∈ members ∧ ∀ other ∈ members, other = receiver

def Ambiguous (members : List α) : Prop :=
  ∃ first ∈ members, ∃ second ∈ members, first ≠ second

@[simp] theorem allEqual_exact [DecidableEq α] (members : List α) (receiver : α) :
    AllEqual members receiver = true ↔ ∀ member ∈ members, member = receiver := by
  simp [AllEqual, List.all_eq_true]

private theorem different_member [DecidableEq α] (members : List α) (receiver : α)
    (different : AllEqual members receiver ≠ true) :
    ∃ member ∈ members, member ≠ receiver := by
  induction members with
  | nil => simp [AllEqual] at different
  | cons member rest ih =>
    by_cases equal : member = receiver
    · subst member
      have tailDifferent : AllEqual rest receiver ≠ true := by
        simpa [AllEqual] using different
      obtain ⟨other, present, unequal⟩ := ih tailDifferent
      exact ⟨other, List.mem_cons_of_mem _ present, unequal⟩
    · exact ⟨member, by simp, equal⟩

theorem select_missing_iff [DecidableEq α] (members : List α) :
    select members = .missing ↔ ∀ member, member ∉ members := by
  cases members with
  | nil => simp [select]
  | cons first rest =>
    constructor
    · intro missing
      by_cases equal : AllEqual rest first = true <;> simp [select, equal] at missing
    · intro absent
      exact False.elim (absent first (by simp))

theorem select_unique_iff [DecidableEq α] (members : List α) (receiver : α) :
    select members = .unique receiver ↔ Unique members receiver := by
  cases members with
  | nil => simp [select, Unique]
  | cons first rest =>
    by_cases equal : AllEqual rest first = true
    · have same := (allEqual_exact rest first).mp equal
      constructor
      · intro selected
        have firstIsReceiver : first = receiver := by simpa [select, equal] using selected
        subst receiver
        exact ⟨by simp, fun other member => (List.mem_cons.mp member).elim id (same other)⟩
      · rintro ⟨_, unique⟩
        have firstIsReceiver := unique first (by simp)
        simpa [select, equal] using firstIsReceiver
    · constructor
      · simp [select, equal]
      · rintro ⟨_, unique⟩
        have firstIsReceiver := unique first (by simp)
        apply False.elim
        apply equal
        apply (allEqual_exact rest first).mpr
        intro other member
        exact (unique other (List.mem_cons_of_mem _ member)).trans firstIsReceiver.symm

theorem select_ambiguous_iff [DecidableEq α] (members : List α) :
    select members = .ambiguous ↔ Ambiguous members := by
  cases members with
  | nil => simp [select, Ambiguous]
  | cons first rest =>
    by_cases equal : AllEqual rest first = true
    · constructor
      · simp [select, equal]
      · rintro ⟨left, hl, right, hr, different⟩
        have same := (allEqual_exact rest first).mp equal
        have leftIsFirst : left = first := (List.mem_cons.mp hl).elim id (same left)
        have rightIsFirst : right = first := (List.mem_cons.mp hr).elim id (same right)
        exact False.elim (different (leftIsFirst.trans rightIsFirst.symm))
    · constructor
      · intro _
        obtain ⟨other, present, different⟩ := different_member rest first equal
        exact ⟨other, List.mem_cons_of_mem _ present, first, by simp, different⟩
      · intro _
        simp [select, equal]

/-- Membership, not multiplicity or order, determines the result. -/
theorem select_ext [DecidableEq α] {left right : List α}
    (sameMembers : ∀ member, member ∈ left ↔ member ∈ right) :
    select left = select right := by
  cases selected : select left with
  | missing =>
    have absent := (select_missing_iff left).mp selected
    symm
    apply (select_missing_iff right).mpr
    intro member present
    exact absent member ((sameMembers member).mpr present)
  | unique receiver =>
    rcases (select_unique_iff left receiver).mp selected with ⟨present, unique⟩
    symm
    apply (select_unique_iff right receiver).mpr
    exact ⟨(sameMembers receiver).mp present,
      fun other member => unique other ((sameMembers other).mpr member)⟩
  | ambiguous =>
    rcases (select_ambiguous_iff left).mp selected with ⟨first, hf, second, hs, unequal⟩
    symm
    apply (select_ambiguous_iff right).mpr
    exact ⟨first, (sameMembers first).mp hf, second, (sameMembers second).mp hs, unequal⟩

theorem select_perm [DecidableEq α] {left right : List α} (permutation : left.Perm right) :
    select left = select right :=
  select_ext (fun _ => permutation.mem_iff)

def candidates (hasMethod : α → Bool) (members : List α) : List α :=
  members.filter hasMethod

def resolve [DecidableEq α] (hasMethod : α → Bool) (members : List α) : Selection α :=
  select (candidates hasMethod members)

def Candidate (hasMethod : α → Bool) (members : List α) (receiver : α) : Prop :=
  receiver ∈ members ∧ hasMethod receiver = true

theorem resolve_unique_iff [DecidableEq α] (hasMethod : α → Bool)
    (members : List α) (receiver : α) :
    resolve hasMethod members = .unique receiver ↔
      Candidate hasMethod members receiver ∧
        ∀ other, Candidate hasMethod members other → other = receiver := by
  simp [resolve, select_unique_iff, Unique, candidates, Candidate]

theorem resolve_missing_iff [DecidableEq α] (hasMethod : α → Bool) (members : List α) :
    resolve hasMethod members = .missing ↔ ∀ receiver, ¬ Candidate hasMethod members receiver := by
  simp [resolve, select_missing_iff, candidates, Candidate]

theorem resolve_ambiguous_iff [DecidableEq α] (hasMethod : α → Bool) (members : List α) :
    resolve hasMethod members = .ambiguous ↔
      ∃ first second, Candidate hasMethod members first ∧
        Candidate hasMethod members second ∧ first ≠ second := by
  simp only [resolve, select_ambiguous_iff, Ambiguous, candidates, List.mem_filter, Candidate]
  constructor
  · rintro ⟨first, hf, second, hs, unequal⟩
    exact ⟨first, second, hf, hs, unequal⟩
  · rintro ⟨first, second, hf, hs, unequal⟩
    exact ⟨first, hf, second, hs, unequal⟩

theorem resolve_perm [DecidableEq α] (hasMethod : α → Bool) {left right : List α}
    (permutation : left.Perm right) : resolve hasMethod left = resolve hasMethod right := by
  apply select_ext
  intro member
  simp [candidates, permutation.mem_iff]

/-! ## The selected receiver is an ordinary cast boundary for every member -/

open Casts

inductive CallResult where
  | missingMethod
  | ambiguous
  | invalidCasts
  | missingCast
  | resolved (receiver : Ty)
  deriving DecidableEq, Repr

def membersAccept (fits : Compatibility) (registry : CastGraph.Registry n)
    (members : List Ty) (receiver : Ty) : Bool :=
  members.all (fun member => accepts fits.check registry.find member receiver)

theorem membersAccept_exact (fits : Compatibility) (registry : CastGraph.Registry n)
    (members : List Ty) (receiver : Ty) :
    membersAccept fits registry members receiver = true ↔
      ∀ member ∈ members, Boundary fits.Rel registry.Explicit member receiver := by
  simp only [membersAccept, List.all_eq_true]
  exact forall_congr' (fun member => forall_congr' (fun _ => accepts_exact fits registry.oracle member receiver))

def checkCall (fits : Compatibility) (registry : CastGraph.Registry n)
    (hasMethod : Ty → Bool) (members : List Ty) : CallResult :=
  match resolve hasMethod members with
  | .missing => .missingMethod
  | .ambiguous => .ambiguous
  | .unique receiver =>
    if registry.validate then
      if membersAccept fits registry members receiver then .resolved receiver else .missingCast
    else .invalidCasts

/-- Independent resolved-call judgement: one distinct method owner and a valid
ordinary boundary from each possible receiver member to that owner. -/
def CallTyping (fits : Compatibility) (registry : CastGraph.Registry n)
    (hasMethod : Ty → Bool) (members : List Ty) (receiver : Ty) : Prop :=
  (Candidate hasMethod members receiver ∧
    ∀ other, Candidate hasMethod members other → other = receiver) ∧
  registry.WellFormed ∧
    ∀ member ∈ members, Boundary fits.Rel registry.Explicit member receiver

private theorem checkCall_result_iff (fits : Compatibility) (registry : CastGraph.Registry n)
    (hasMethod : Ty → Bool) (members : List Ty) (receiver : Ty) :
    checkCall fits registry hasMethod members = .resolved receiver ↔
      resolve hasMethod members = .unique receiver ∧ registry.validate = true ∧
        membersAccept fits registry members receiver = true := by
  cases selected : resolve hasMethod members with
  | missing => simp [checkCall, selected]
  | ambiguous => simp [checkCall, selected]
  | unique chosen =>
    by_cases valid : registry.validate = true
    · by_cases convertible : membersAccept fits registry members chosen = true
      · constructor
        · intro result
          have same : chosen = receiver := by simpa [checkCall, selected, valid, convertible] using result
          subst receiver
          exact ⟨rfl, valid, convertible⟩
        · rintro ⟨same, _, _⟩
          have equal : chosen = receiver := Selection.unique.inj same
          subst receiver
          simp [checkCall, selected, valid, convertible]
      · constructor
        · simp [checkCall, selected, valid, convertible]
        · rintro ⟨same, _, converted⟩
          have equal : chosen = receiver := Selection.unique.inj same
          subst receiver
          exact False.elim (convertible converted)
    · simp [checkCall, selected, valid]

theorem checkCall_exact (fits : Compatibility) (registry : CastGraph.Registry n)
    (hasMethod : Ty → Bool) (members : List Ty) (receiver : Ty) :
    checkCall fits registry hasMethod members = .resolved receiver ↔
      CallTyping fits registry hasMethod members receiver := by
  rw [checkCall_result_iff, resolve_unique_iff, registry.validate_exact, membersAccept_exact]
  rfl

theorem membersAccept_perm (fits : Compatibility) (registry : CastGraph.Registry n)
    {left right : List Ty} (permutation : left.Perm right) (receiver : Ty) :
    membersAccept fits registry left receiver = membersAccept fits registry right receiver := by
  have equivalent : membersAccept fits registry left receiver = true ↔
      membersAccept fits registry right receiver = true := by
    rw [membersAccept_exact, membersAccept_exact]
    exact ⟨fun h member present => h member (permutation.mem_iff.mpr present),
      fun h member present => h member (permutation.mem_iff.mp present)⟩
  cases hl : membersAccept fits registry left receiver <;>
    cases hr : membersAccept fits registry right receiver <;> simp_all

/-- Cast acceptance as well as candidate selection is independent of union order. -/
theorem checkCall_perm (fits : Compatibility) (registry : CastGraph.Registry n)
    (hasMethod : Ty → Bool) {left right : List Ty} (permutation : left.Perm right) :
    checkCall fits registry hasMethod left = checkCall fits registry hasMethod right := by
  simp only [checkCall, resolve_perm hasMethod permutation]
  cases resolve hasMethod right with
  | missing | ambiguous => rfl
  | unique receiver =>
    dsimp only
    rw [membersAccept_perm fits registry permutation receiver]

namespace Examples

example : resolve (fun n : Nat => n == 0) [1, 0, 0] = .unique 0 := by decide
example : resolve (fun _ : Nat => true) [0, 1] = .ambiguous := by decide
example : resolve (fun _ : Nat => false) [0, 1] = .missing := by decide

end Examples
end Yulang.Methods
