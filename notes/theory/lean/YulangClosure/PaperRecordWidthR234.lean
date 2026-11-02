import YulangClosure.AbstractCachedConstrainR233
import Init.Data.List.Perm

/-!
Finite mandatory records from Parreaux, section 3.2.2 and Fig. 9, and
Typer.scala:108--114 at 9bae772624c23b52a93c1b226157e16898b4d9db.

`Required` is the independent width/depth equation. `emit` traverses the
upper row, finds the first matching lower field, and emits lower-to-upper
child comparisons. It models decomposition, not execution of the recursive
callbacks, mutation, cache, or errors after previous callbacks have run.
The equation with `Required` explicitly requires functional lower labels;
the equation with `LookupRequired` covers arbitrary first-match lists.

Child comparison remains an arbitrary relation `R`; no recursive record-type
model or full comparator is asserted here. The concrete R233 width example
uses the unchanged SimpleSub.Sub on its one reflexive atom child. Existing
Sub, its closed tails and optional flags, all original roots, and their
quantifiers stay fixed. The primary's two rejected recursive constructions
are preserved as failure evidence in the revision-2 handoff.

Author constructed this file without invoking Lean/Lake: Luna owns checking
and all cache outputs. The audit requests below are not execution receipts.
-/
namespace YulangClosure.PaperRecordWidthR234

universe u

abbrev Fields (α : Type u) := List (Nat × α)

/-- First-match lookup, including its explicit behavior on duplicate labels. -/
def lookup {α : Type u} : Fields α → Nat → Option α
  | [], _ => none
  | (label, ty) :: rest, wanted =>
      if label = wanted then some ty else lookup rest wanted

/-- Equal labels carry equal payloads. Repeated identical entries are allowed.
No claim that this is Yulang's duplicate-label well-formedness rule is made. -/
def Functional {α : Type u} (fields : Fields α) : Prop :=
  ∀ label left right, (label, left) ∈ fields → (label, right) ∈ fields → left = right

/-- The paper's width/depth equation: every required upper field has a lower
field with the same label, whose type compares in the lower-to-upper direction.
Extra lower labels impose no obligation. This definition does not call `emit`. -/
def Required {α : Type u} (R : α → α → Prop) (lower upper : Fields α) : Prop :=
  ∀ field ∈ upper, ∃ lowerType, (field.1, lowerType) ∈ lower ∧ R lowerType field.2

/-- Exact first-match specification, even for conflicting duplicate labels. -/
def LookupRequired {α : Type u} (R : α → α → Prop) (lower upper : Fields α) : Prop :=
  ∀ field ∈ upper, ∃ lowerType,
    lookup lower field.1 = some lowerType ∧ R lowerType field.2

/-- All recursive child comparisons must hold; decomposition success alone
does not establish any child comparison. -/
def Children {α : Type u} (R : α → α → Prop) : List (α × α) → Prop
  | [] => True
  | child :: rest => R child.1 child.2 ∧ Children R rest

/-- The lookup/decomposition branch in upper traversal order. `none` denotes
a missing required label; it does not encode the mutable reference cache. -/
def emit {α : Type u} (lower : Fields α) : Fields α → Option (List (α × α))
  | [] => some []
  | field :: rest =>
      match lookup lower field.1 with
      | none => none
      | some lowerType =>
          match emit lower rest with
          | none => none
          | some children => some ((lowerType, field.2) :: children)

theorem lookup_some_mem {α : Type u} {fields : Fields α} {label : Nat} {ty : α}
    (found : lookup fields label = some ty) : (label, ty) ∈ fields := by
  revert found
  induction fields with
  | nil => intro found; simp [lookup] at found
  | cons field rest ih =>
      intro found
      rcases field with ⟨headLabel, headType⟩
      by_cases same : headLabel = label
      · have types : headType = ty := by simpa [lookup, same] using found
        subst headLabel
        subst headType
        exact List.mem_cons_self
      · have tailFound : lookup rest label = some ty := by
          simpa [lookup, same] using found
        exact List.mem_cons_of_mem _ (ih tailFound)

theorem lookup_eq_some_iff_mem {α : Type u} {fields : Fields α}
    (functional : Functional fields) (label : Nat) (ty : α) :
    lookup fields label = some ty ↔ (label, ty) ∈ fields := by
  constructor
  · exact lookup_some_mem
  · intro member
    revert functional member
    induction fields with
    | nil => intro functional member; simp at member
    | cons field rest ih =>
        intro functional member
        rcases field with ⟨headLabel, headType⟩
        by_cases same : headLabel = label
        · have headMember : (label, headType) ∈ (headLabel, headType) :: rest := by
            simp [same]
          have types : headType = ty := functional label headType ty headMember member
          simp [lookup, same, types]
        · have tailMember : (label, ty) ∈ rest := by
            rcases List.mem_cons.mp member with head | tail
            · have labels : label = headLabel := congrArg Prod.fst head
              exact False.elim (same labels.symm)
            · exact tail
          have tailFunctional : Functional rest := by
            intro name left right leftMem rightMem
            exact functional name left right
              (List.mem_cons_of_mem _ leftMem) (List.mem_cons_of_mem _ rightMem)
          have tailFound := ih tailFunctional tailMember
          simpa [lookup, same] using tailFound

theorem lookup_required_iff_required {α : Type u} (R : α → α → Prop)
    {lower upper : Fields α} (functional : Functional lower) :
    LookupRequired R lower upper ↔ Required R lower upper := by
  constructor
  · intro h field member
    obtain ⟨ty, found, related⟩ := h field member
    exact ⟨ty, lookup_some_mem found, related⟩
  · intro h field member
    obtain ⟨ty, present, related⟩ := h field member
    exact ⟨ty, (lookup_eq_some_iff_mem functional _ _).mpr present, related⟩

theorem lookup_required_cons {α : Type u} (R : α → α → Prop)
    (lower : Fields α) (field : Nat × α) (rest : Fields α) :
    LookupRequired R lower (field :: rest) ↔
      (∃ ty, lookup lower field.1 = some ty ∧ R ty field.2) ∧
        LookupRequired R lower rest := by
  constructor
  · intro h
    exact ⟨h field List.mem_cons_self,
      fun other member => h other (List.mem_cons_of_mem _ member)⟩
  · rintro ⟨head, tail⟩ other member
    rcases List.mem_cons.mp member with equal | member
    · subst other
      exact head
    · exact tail other member

theorem children_cons {α : Type u} (R : α → α → Prop)
    (child : α × α) (rest : List (α × α)) :
    Children R (child :: rest) ↔ R child.1 child.2 ∧ Children R rest := Iff.rfl

/-- Exact branch equation, including arbitrary first-match duplicate lists.
Success here includes all emitted recursive child obligations. -/
theorem emit_success_iff_lookup_required {α : Type u} (R : α → α → Prop)
    (lower upper : Fields α) :
    (∃ children, emit lower upper = some children ∧ Children R children) ↔
      LookupRequired R lower upper := by
  induction upper with
  | nil => simp [emit, Children, LookupRequired]
  | cons field rest ih =>
      rw [lookup_required_cons]
      cases found : lookup lower field.1 with
      | none => simp [emit, found]
      | some lowerType =>
          cases emitted : emit lower rest with
          | none =>
              have absent : ¬ LookupRequired R lower rest := by
                intro h
                obtain ⟨children, equal, _⟩ := ih.mpr h
                simp [emitted] at equal
              simp [emit, found, emitted, absent]
          | some children =>
              have tail : Children R children ↔ LookupRequired R lower rest := by
                simpa [emitted] using ih
              simp [emit, found, emitted, children_cons, tail]

/-- Width/depth correctness on functional mandatory rows. Upper rows need no
uniqueness premise: each upper occurrence is traversed and checked. -/
theorem emit_success_iff_required {α : Type u} (R : α → α → Prop)
    {lower : Fields α} (functional : Functional lower) (upper : Fields α) :
    (∃ children, emit lower upper = some children ∧ Children R children) ↔
      Required R lower upper :=
  (emit_success_iff_lookup_required R lower upper).trans
    (lookup_required_iff_required R functional)

/-- Reuses the actual emitted list; it cannot select unrelated child witnesses. -/
theorem emitted_children_preserved {α : Type u} (R : α → α → Prop)
    {lower upper : Fields α} {children : List (α × α)}
    (functional : Functional lower) (emitted : emit lower upper = some children)
    (related : Required R lower upper) : Children R children := by
  obtain ⟨actual, equal, valid⟩ := (emit_success_iff_required R functional upper).mpr related
  have same : actual = children := Option.some.inj (equal.symm.trans emitted)
  subst actual
  exact valid

theorem children_true {α : Type u} (children : List (α × α)) :
    Children (fun _ _ => True) children := by
  induction children with
  | nil => trivial
  | cons child rest ih => exact ⟨True.intro, ih⟩

/-- A missing upper label rejects decomposition, regardless of child relation
and without assuming label uniqueness. -/
theorem missing_upper_rejects {α : Type u} {lower upper : Fields α}
    {field : Nat × α} (member : field ∈ upper)
    (missing : lookup lower field.1 = none) : emit lower upper = none := by
  cases emitted : emit lower upper with
  | none => rfl
  | some children =>
      have covered := (emit_success_iff_lookup_required (fun _ _ => True) lower upper).mp
        ⟨children, emitted, children_true children⟩
      obtain ⟨ty, found, _⟩ := covered field member
      simp [missing] at found

/-- Pure relation permutation invariance. Algorithm output order is separate. -/
theorem required_permutation {α : Type u} (R : α → α → Prop)
    {lower lower' upper upper' : Fields α}
    (lowerPerm : lower.Perm lower') (upperPerm : upper.Perm upper') :
    Required R lower upper ↔ Required R lower' upper' := by
  constructor
  · intro h field member
    obtain ⟨ty, present, related⟩ := h field (upperPerm.mem_iff.mpr member)
    exact ⟨ty, lowerPerm.mem_iff.mp present, related⟩
  · intro h field member
    obtain ⟨ty, present, related⟩ := h field (upperPerm.mem_iff.mp member)
    exact ⟨ty, lowerPerm.mem_iff.mpr present, related⟩

theorem functional_permutation {α : Type u} {lower lower' : Fields α}
    (permutation : lower.Perm lower') (functional : Functional lower) :
    Functional lower' := by
  intro label left right leftMem rightMem
  exact functional label left right
    (permutation.mem_iff.mpr leftMem) (permutation.mem_iff.mpr rightMem)

/-- Validated success is invariant under both row permutations, on functional
lower rows. The emitted sequence itself follows upper order. -/
theorem emit_success_permutation {α : Type u} (R : α → α → Prop)
    {lower lower' upper upper' : Fields α} (functional : Functional lower)
    (lowerPerm : lower.Perm lower') (upperPerm : upper.Perm upper') :
    (∃ children, emit lower upper = some children ∧ Children R children) ↔
      (∃ children, emit lower' upper' = some children ∧ Children R children) :=
  (emit_success_iff_required R functional upper).trans
    ((required_permutation R lowerPerm upperPerm).trans
      (emit_success_iff_required R (functional_permutation lowerPerm functional) upper').symm)

def widthLowerFields : Fields (SimpleSub.Term .value) := [(0, .atom 0), (1, .atom 1)]
def widthUpperFields : Fields (SimpleSub.Term .value) := [(0, .atom 0)]

theorem width_emit : emit widthLowerFields widthUpperFields =
    some [(.atom 0, .atom 0)] := rfl

theorem width_branch_success :
    ∃ children, emit widthLowerFields widthUpperFields = some children ∧
      Children SimpleSub.Sub children :=
  ⟨[(.atom 0, .atom 0)], rfl, SimpleSub.Sub.refl _, True.intro⟩

theorem width_required : Required SimpleSub.Sub widthLowerFields widthUpperFields := by
  intro field member
  have same : field = (0, SimpleSub.Term.atom 0) := by
    simpa [widthUpperFields] using member
  subst field
  exact ⟨.atom 0, by simp [widthLowerFields], SimpleSub.Sub.refl _⟩

/-- The child pair direction is observably lower-to-upper, rather than reversed. -/
theorem directed_child : emit ([(0, 3)] : Fields Nat) [(0, 5)] = some [(3, 5)] := rfl

theorem missing_width_label : emit widthLowerFields [(2, SimpleSub.Term.atom 0)] = none := rfl

theorem lower_order_example :
    emit ([(1, .atom 1), (0, .atom 0)] : Fields (SimpleSub.Term .value)) widthUpperFields =
      some [(.atom 0, .atom 0)] := rfl

theorem upper_order_example :
    emit widthLowerFields [(1, .atom 1), (0, .atom 0)] =
      some [(.atom 1, .atom 1), (.atom 0, .atom 0)] := rfl

/-- Conflicting duplicates exhibit why unrestricted lower permutation is false. -/
theorem conflicting_duplicate_order :
    emit ([(0, 3), (0, 4)] : Fields Nat) [(0, 5)] = some [(3, 5)] ∧
    emit ([(0, 4), (0, 3)] : Fields Nat) [(0, 5)] = some [(4, 5)] := ⟨rfl, rfl⟩

/-- The exact atoms/labels in R233's two closed mandatory rows satisfy the
paper field equation, while the frozen full-row Sub comparison remains false.
No general Yulang/source encoding is asserted by this finite pair. -/
theorem r233_paper_width_and_closed_row_obstruction :
    Required SimpleSub.Sub
      ([(0, .atom 0), (1, .atom 1)] : Fields (SimpleSub.Term .value)) [(0, .atom 0)] ∧
    ¬ SimpleSub.Sub SimpleSub.CachedConstrainR233.widthLower
      SimpleSub.CachedConstrainR233.widthUpper := by
  exact ⟨width_required, SimpleSub.CachedConstrainR233.width_not_sub⟩

end YulangClosure.PaperRecordWidthR234

/- Complete author-requested printed type / transitive axiom audit. -/
#check @YulangClosure.PaperRecordWidthR234.lookup_some_mem
#print axioms YulangClosure.PaperRecordWidthR234.lookup_some_mem
#check @YulangClosure.PaperRecordWidthR234.lookup_eq_some_iff_mem
#print axioms YulangClosure.PaperRecordWidthR234.lookup_eq_some_iff_mem
#check @YulangClosure.PaperRecordWidthR234.lookup_required_iff_required
#print axioms YulangClosure.PaperRecordWidthR234.lookup_required_iff_required
#check @YulangClosure.PaperRecordWidthR234.lookup_required_cons
#print axioms YulangClosure.PaperRecordWidthR234.lookup_required_cons
#check @YulangClosure.PaperRecordWidthR234.children_cons
#print axioms YulangClosure.PaperRecordWidthR234.children_cons
#check @YulangClosure.PaperRecordWidthR234.emit_success_iff_lookup_required
#print axioms YulangClosure.PaperRecordWidthR234.emit_success_iff_lookup_required
#check @YulangClosure.PaperRecordWidthR234.emit_success_iff_required
#print axioms YulangClosure.PaperRecordWidthR234.emit_success_iff_required
#check @YulangClosure.PaperRecordWidthR234.emitted_children_preserved
#print axioms YulangClosure.PaperRecordWidthR234.emitted_children_preserved
#check @YulangClosure.PaperRecordWidthR234.children_true
#print axioms YulangClosure.PaperRecordWidthR234.children_true
#check @YulangClosure.PaperRecordWidthR234.missing_upper_rejects
#print axioms YulangClosure.PaperRecordWidthR234.missing_upper_rejects
#check @YulangClosure.PaperRecordWidthR234.required_permutation
#print axioms YulangClosure.PaperRecordWidthR234.required_permutation
#check @YulangClosure.PaperRecordWidthR234.functional_permutation
#print axioms YulangClosure.PaperRecordWidthR234.functional_permutation
#check @YulangClosure.PaperRecordWidthR234.emit_success_permutation
#print axioms YulangClosure.PaperRecordWidthR234.emit_success_permutation
#check @YulangClosure.PaperRecordWidthR234.width_emit
#print axioms YulangClosure.PaperRecordWidthR234.width_emit
#check @YulangClosure.PaperRecordWidthR234.width_branch_success
#print axioms YulangClosure.PaperRecordWidthR234.width_branch_success
#check @YulangClosure.PaperRecordWidthR234.width_required
#print axioms YulangClosure.PaperRecordWidthR234.width_required
#check @YulangClosure.PaperRecordWidthR234.directed_child
#print axioms YulangClosure.PaperRecordWidthR234.directed_child
#check @YulangClosure.PaperRecordWidthR234.missing_width_label
#print axioms YulangClosure.PaperRecordWidthR234.missing_width_label
#check @YulangClosure.PaperRecordWidthR234.lower_order_example
#print axioms YulangClosure.PaperRecordWidthR234.lower_order_example
#check @YulangClosure.PaperRecordWidthR234.upper_order_example
#print axioms YulangClosure.PaperRecordWidthR234.upper_order_example
#check @YulangClosure.PaperRecordWidthR234.conflicting_duplicate_order
#print axioms YulangClosure.PaperRecordWidthR234.conflicting_duplicate_order
#check @YulangClosure.PaperRecordWidthR234.r233_paper_width_and_closed_row_obstruction
#print axioms YulangClosure.PaperRecordWidthR234.r233_paper_width_and_closed_row_obstruction
