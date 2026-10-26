import YulangClosure.RecordBoundaryPreservation

/-!
The finite native record scan, with original field indices and boundary metadata.
This is a proof-side transcription of lib.rs record dispatch, not a new native
pass. Metadata is carried independently of semantic payload types. One resolver
is fixed for the entire boundary. Source elaboration into an original RecMap_j,
child request/resumption contracts and complete Call evidence remain separate.
-/

namespace YulangClosure.NativeRecordPlan

open RecordBoundary

variable {Meta Ty Cast Value Event : Type}

/-- Increasing source enumeration with the first matching name retained. -/
def lookupIndexed (source : List (Field Ty)) (label : Nat) : Option (Nat × Spec Ty) :=
  match source with
  | [] => none
  | (name, spec) :: tail =>
      if label = name then some (0, spec)
      else (lookupIndexed tail label).map (fun found => (found.1 + 1, found.2))

theorem lookupIndexed_signature (source : List (Field Ty)) (label : Nat) :
    (lookupIndexed source label).map Prod.snd = signature source label := by
  induction source with
  | nil => rfl
  | cons field tail ih =>
      rcases field with ⟨name, spec⟩
      by_cases h : label = name
      · simp [lookupIndexed, signature, h]
      · simpa [lookupIndexed, signature, h, Option.map_map, Function.comp_def] using ih

theorem lookupIndexed_occurrence (source : List (Field Ty))
    (h : lookupIndexed source label = some (index, spec)) :
    source[index]? = some (label, spec) := by
  induction source generalizing index with
  | nil => simp [lookupIndexed] at h
  | cons field tail ih =>
      rcases field with ⟨name, origin⟩
      by_cases hn : label = name
      · simp [lookupIndexed, hn] at h
        rcases h with ⟨rfl, rfl⟩
        simp [hn]
      · cases hl : lookupIndexed tail label with
        | none => simp [lookupIndexed, hn, hl] at h
        | some found =>
            rcases found with ⟨i, s⟩
            simp only [lookupIndexed, hn, ↓reduceIte, hl, Option.map_some,
              Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            simpa using ih hl

/-- Every earlier source occurrence has a different name, including duplicates. -/
theorem lookupIndexed_first (source : List (Field Ty))
    (h : lookupIndexed source label = some (index, spec))
    (earlier : Nat) (before : earlier < index) {field : Field Ty}
    (found : source[earlier]? = some field) : field.1 ≠ label := by
  induction source generalizing index earlier with
  | nil => simp [lookupIndexed] at h
  | cons head tail ih =>
      rcases head with ⟨name, origin⟩
      by_cases hn : label = name
      · simp [lookupIndexed, hn] at h
        rcases h with ⟨rfl, rfl⟩
        omega
      · cases hl : lookupIndexed tail label with
        | none => simp [lookupIndexed, hn, hl] at h
        | some result =>
            rcases result with ⟨i, s⟩
            simp only [lookupIndexed, hn, ↓reduceIte, hl, Option.map_some,
              Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            cases earlier with
            | zero =>
                simp only [List.getElem?_cons_zero, Option.some.injEq] at found
                cases found
                exact Ne.symm hn
            | succ earlier =>
                exact ih hl earlier (Nat.lt_of_succ_lt_succ before) found

structure Hole (Meta Ty : Type) where
  boundary : Meta
  lowerIndex : Nat
  upperIndex : Nat
  sourceSpec : Spec Ty
  targetField : Field Ty
  deriving DecidableEq, Repr

inductive Slot (Meta Ty : Type) where
  | absent (upperIndex : Nat) (target : Field Ty)
  | child (hole : Hole Meta Ty)
  deriving DecidableEq, Repr

def Slot.target : Slot Meta Ty → Field Ty
  | .absent _ target => target
  | .child hole => hole.targetField

def Slot.upperIndex : Slot Meta Ty → Nat
  | .absent index _ => index
  | .child hole => hole.upperIndex

/-- Diagnostic recovery is distinct from availability failure and scan success. -/
inductive Failure where
  | diagnosticMissing (upperIndex : Nat)
  | unavailablePresence (lowerIndex upperIndex : Nat)
  deriving DecidableEq, Repr

def shapeField (boundary : Meta) (source : List (Field Ty))
    (upperIndex : Nat) (target : Field Ty) : Except Failure (Slot Meta Ty) :=
  match lookupIndexed source target.1 with
  | none =>
      if target.2.optional = true then .ok (.absent upperIndex target)
      else .error (.diagnosticMissing upperIndex)
  | some (lowerIndex, origin) =>
      if origin.optional = false ∨ target.2.optional = true then
        .ok (.child ⟨boundary, lowerIndex, upperIndex, origin, target⟩)
      else .error (.unavailablePresence lowerIndex upperIndex)

/-- Full slots retain absent targets; errors discard every accumulated child. -/
def shape (boundary : Meta) (source : List (Field Ty)) (next : Nat) :
    List (Field Ty) → Except Failure (List (Slot Meta Ty))
  | [] => .ok []
  | target :: tail =>
      match shapeField boundary source next target with
      | .error failure => .error failure
      | .ok slot =>
          match shape boundary source (next + 1) tail with
          | .error failure => .error failure
          | .ok slots => .ok (slot :: slots)

def Slot.Valid (source : List (Field Ty)) (boundary : Meta)
    (index : Nat) (target : Field Ty) : Slot Meta Ty → Prop
  | .absent actualIndex actualTarget =>
      actualIndex = index ∧ actualTarget = target ∧
      signature source target.1 = none ∧ target.2.optional = true
  | .child hole =>
      hole.boundary = boundary ∧ hole.upperIndex = index ∧ hole.targetField = target ∧
      lookupIndexed source target.1 = some (hole.lowerIndex, hole.sourceSpec) ∧
      (hole.sourceSpec.optional = false ∨ target.2.optional = true)

inductive ValidShape (source : List (Field Ty)) (boundary : Meta) :
    Nat → List (Field Ty) → List (Slot Meta Ty) → Prop where
  | nil : ValidShape source boundary index [] []
  | cons : slot.Valid source boundary index target →
      ValidShape source boundary (index + 1) targets slots →
      ValidShape source boundary index (target :: targets) (slot :: slots)

theorem shapeField_valid
    (h : shapeField boundary source index target = .ok slot) :
    slot.Valid source boundary index target := by
  unfold shapeField at h
  split at h
  next hs =>
    split at h
    next optional =>
      cases h
      exact ⟨rfl, rfl, by simpa [hs] using
        (lookupIndexed_signature source target.1).symm, optional⟩
    next => contradiction
  next found hs =>
    rcases found with ⟨lowerIndex, origin⟩
    split at h
    next presence =>
      cases h
      exact ⟨rfl, rfl, rfl, hs, presence⟩
    next => contradiction

theorem shape_valid
    (h : shape boundary source index targets = .ok slots) :
    ValidShape source boundary index targets slots := by
  induction targets generalizing index slots with
  | nil => cases h; exact .nil
  | cons target targets ih =>
      cases he : shapeField boundary source index target with
      | error failure => simp [shape, he] at h
      | ok slot =>
          cases ht : shape boundary source (index + 1) targets with
          | error failure => simp [shape, he, ht] at h
          | ok rest =>
              simp only [shape, he, ht, Except.ok.injEq] at h
              cases h
              exact .cons (shapeField_valid he) (ih ht)

theorem validShape_targets
    (h : ValidShape source boundary index targets slots) :
    slots.map Slot.target = targets := by
  induction h with
  | nil => rfl
  | @cons index targets slots target slot hv ht ih =>
      cases slot with
      | absent i t => simpa [Slot.target, hv.2.1] using congrArg (target :: ·) ih
      | child hole => simpa [Slot.target, hv.2.2.1] using congrArg (target :: ·) ih

/-- Slot position is never substituted for its original upper index. -/
theorem validShape_indexed
    {source : List (Field Ty)} {boundary : Meta} {start position : Nat}
    {targets : List (Field Ty)} {slots : List (Slot Meta Ty)} {slot : Slot Meta Ty}
    (h : ValidShape source boundary start targets slots)
    (hs : slots[position]? = some slot) :
    ∃ target, targets[position]? = some target ∧
      slot.Valid source boundary (start + position) target := by
  induction h generalizing position with
  | nil => simp at hs
  | @cons index targets slots target entry hv ht ih =>
      cases position with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
          cases hs
          exact ⟨target, rfl, by simpa using hv⟩
      | succ position =>
          simp only [List.getElem?_cons_succ] at hs
          obtain ⟨t, hp, valid⟩ := ih hs
          exact ⟨t, hp, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using valid⟩

def children : List (Slot Meta Ty) → List (Hole Meta Ty)
  | [] => []
  | .absent _ _ :: rest => children rest
  | .child hole :: rest => hole :: children rest

theorem child_mem_slots (h : hole ∈ children slots) : Slot.child hole ∈ slots := by
  induction slots with
  | nil => simp [children] at h
  | cons slot slots ih =>
      cases slot with
      | absent i t => exact List.mem_cons_of_mem _ (ih h)
      | child head =>
          simp only [children, List.mem_cons] at h
          rcases h with rfl | ht
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih ht)

theorem validShape_child
    (h : ValidShape source boundary start targets slots)
    (hc : hole ∈ children slots) :
    hole.boundary = boundary ∧
      source[hole.lowerIndex]? = some (hole.targetField.1, hole.sourceSpec) ∧
      ∃ position, hole.upperIndex = start + position ∧
        targets[position]? = some hole.targetField := by
  have hm := child_mem_slots hc
  obtain ⟨position, hp⟩ := List.mem_iff_getElem?.mp hm
  obtain ⟨target, ht, hv⟩ := validShape_indexed h hp
  rcases hv with ⟨hb, hi, htarget, hl, _⟩
  subst target
  exact ⟨hb, lookupIndexed_occurrence source hl, position, hi, ht⟩

/-- Native diagnostic success admits zero children, as does unavailability. -/
def admittedChildren : Except Failure (List (Slot Meta Ty)) → List (Hole Meta Ty)
  | .error _ => []
  | .ok slots => children slots

theorem failed_shape_no_children
    {failure : Failure}
    (h : shape boundary source index targets = .error failure) :
    admittedChildren (shape boundary source index targets) = [] := by rw [h]; rfl

/-- This flag describes the two record-specific semantic exits only, assuming
the native allocation/readback/receipt operations themselves are available. -/
def rustOk : Except Failure (List (Slot Meta Ty)) → Bool
  | .ok _ => true
  | .error (.diagnosticMissing _) => true
  | .error (.unavailablePresence _ _) => false

def diagnostic : Except Failure (List (Slot Meta Ty)) → Option Nat
  | .error (.diagnosticMissing index) => some index
  | _ => none

theorem missing_is_diagnostic_not_admission
    (h : shape boundary source index targets = .error (.diagnosticMissing missing)) :
    rustOk (shape boundary source index targets) = true ∧
      diagnostic (shape boundary source index targets) = some missing ∧
      admittedChildren (shape boundary source index targets) = [] ∧
      ∀ slots, shape boundary source index targets ≠ .ok slots := by
  simp [h, rustOk, diagnostic, admittedChildren]

theorem unavailable_is_not_rustOk
    (h : shape boundary source index targets = .error (.unavailablePresence lower upper)) :
    rustOk (shape boundary source index targets) = false ∧
      diagnostic (shape boundary source index targets) = none ∧
      admittedChildren (shape boundary source index targets) = [] := by
  simp [h, rustOk, diagnostic, admittedChildren]

/-- Reverse admissions with front enqueue restore the original sibling order. -/
def frontEnqueue (admissions queue : List α) : List α :=
  admissions.foldl (fun rest child => child :: rest) queue

theorem frontEnqueue_eq (admissions queue : List α) :
    frontEnqueue admissions queue = admissions.reverse ++ queue := by
  induction admissions generalizing queue with
  | nil => rfl
  | cons child rest ih =>
      simp [frontEnqueue, List.reverse_cons, List.append_assoc] at ih ⊢

theorem reverse_admission_order (siblings queue : List α) :
    frontEnqueue siblings.reverse queue = siblings ++ queue := by
  rw [frontEnqueue_eq, List.reverse_reverse]

def fillSlot (resolve : Meta → Ty → Ty → Option Cast) :
    Slot Meta Ty → Option (FieldPlan Ty Cast)
  | .absent _ target => some (.absent target)
  | .child hole =>
      (resolve hole.boundary hole.sourceSpec.ty hole.targetField.2.ty).map
        (FieldPlan.convert hole.targetField hole.sourceSpec)

def fill (resolve : Meta → Ty → Ty → Option Cast) :
    List (Slot Meta Ty) → Option (List (FieldPlan Ty Cast))
  | [] => some []
  | slot :: slots => do
      let entry ← fillSlot resolve slot
      let rest ← fill resolve slots
      pure (entry :: rest)

theorem shapeField_fill
    (h : shapeField boundary source index target = .ok slot) :
    fillSlot resolve slot =
      compileField (signature source) (fun _ => false) (resolve boundary) target := by
  have valid := shapeField_valid h
  cases slot with
  | absent i t =>
      rcases valid with ⟨_, rfl, hs, ho⟩
      simp [fillSlot, compileField, hs, ho]
  | child hole =>
      rcases valid with ⟨hb, _, ht, hl, hp⟩
      have hs : signature source target.1 = some hole.sourceSpec := by
        simpa [hl] using (lookupIndexed_signature source target.1).symm
      simp [fillSlot, compileField, hb, ht, hs, hp]

/-- Exact compiler agreement uses one fixed boundary-scoped resolver. -/
theorem shape_fill_compile
    (h : shape boundary source index targets = .ok slots) :
    fill resolve slots = compile (signature source) (fun _ => false) (resolve boundary) targets := by
  induction targets generalizing index slots with
  | nil => cases h; rfl
  | cons target targets ih =>
      cases he : shapeField boundary source index target with
      | error failure => simp [shape, he] at h
      | ok slot =>
          cases ht : shape boundary source (index + 1) targets with
          | error failure => simp [shape, he, ht] at h
          | ok rest =>
              simp only [shape, he, ht, Except.ok.injEq] at h
              cases h
              simp only [fill, compile, shapeField_fill he, ih ht]

theorem filled_compile
    (shaped : shape boundary source index targets = .ok slots)
    (filled : fill resolve slots = some plan) :
    compile (signature source) (fun _ => false) (resolve boundary) targets = some plan := by
  rw [← shape_fill_compile shaped]; exact filled

theorem filled_run_preserves
    (shaped : shape boundary source index targets = .ok slots)
    (filled : fill resolve slots = some plan)
    (inputTyped : ViewTyped typed (signature source) input)
    (childSound : ChildSound typed (resolve boundary) child)
    (run : Run child input plan trace output) :
    ViewTyped typed (signature targets) (visible output) := by
  apply compiled_run_preserves (filled_compile shaped filled) inputTyped _ childSound run
  intro label impossible
  contradiction

theorem filled_run_survivors
    (shaped : shape boundary source index targets = .ok slots)
    (filled : fill resolve slots = some plan)
    (inputTyped : ViewTyped typed (signature source) input)
    (run : Run child input plan trace output) (label : Nat) :
    (visible output label).isSome =
      ((input label).isSome && (signature targets label).isSome) :=
  run_survivors (compile_sound (filled_compile shaped filled)) inputTyped run label

namespace Witness

/-- The genuine formal uses one shared interpretation for r+/r- and i+/i-. -/
def formalFields (required incoming : Ty) : List (Field Ty) :=
  [(0, ⟨required, false⟩), (1, ⟨incoming, true⟩)]

def formalSlots (boundary : Meta) (required incoming : Ty) : List (Slot Meta Ty) :=
  [.child ⟨boundary, 0, 0, ⟨required, false⟩, (0, ⟨required, false⟩)⟩,
   .child ⟨boundary, 1, 1, ⟨incoming, true⟩, (1, ⟨incoming, true⟩)⟩]

def identityResolve [DecidableEq Ty] : Meta → Ty → Ty → Option Unit :=
  fun _ a b => if a = b then some () else none

def formalPlan (required incoming : Ty) : List (FieldPlan Ty Unit) :=
  [.convert (0, ⟨required, false⟩) ⟨required, false⟩ (),
   .convert (1, ⟨incoming, true⟩) ⟨incoming, true⟩ ()]

theorem formal_shape (boundary : Meta) (required incoming : Ty) :
    shape boundary (formalFields required incoming) 0 (formalFields required incoming) =
      .ok (formalSlots boundary required incoming) := by
  simp [shape, shapeField, lookupIndexed, formalFields, formalSlots]

theorem formal_fill [DecidableEq Ty] (boundary : Meta) (required incoming : Ty) :
    fill identityResolve (formalSlots boundary required incoming) = some (formalPlan required incoming) := by
  simp [fill, fillSlot, identityResolve, formalSlots, formalPlan]

theorem formal_compiles [DecidableEq Ty] (boundary : Meta) (required incoming : Ty) :
    compile (signature (formalFields required incoming)) (fun _ => false)
      (identityResolve boundary) (formalFields required incoming) = some (formalPlan required incoming) :=
  filled_compile (formal_shape boundary required incoming) (formal_fill boundary required incoming)

theorem identity_child_sound [DecidableEq Ty] (boundary : Meta) (typed : Value → Ty → Prop) :
    ChildSound typed (identityResolve boundary) (PureChild (Event := Event) (fun (_ : Unit) value => value)) := by
  intro a b cast value trace result resolved hv executed
  simp only [identityResolve] at resolved
  split at resolved
  next equal =>
    subst b
    rcases executed with ⟨_, rfl⟩
    exact hv
  next => contradiction

theorem formal_normal_preserves [DecidableEq Ty]
    (boundary : Meta) (required incoming : Ty)
    (inputTyped : ViewTyped typed (signature (formalFields required incoming)) input) :
    ViewTyped typed (signature (formalFields required incoming))
      (visible (execute (fun (_ : Unit) value => value) input (formalPlan required incoming))) := by
  exact filled_run_preserves (formal_shape boundary required incoming)
    (formal_fill boundary required incoming) inputTyped
    (identity_child_sound (Event := Unit) boundary typed) (execute_runs _ _ _)

theorem original_upper_index_gap (boundary : Meta) (payload : Ty) :
    shape boundary [(1, ⟨payload, false⟩)] 0
      [(0, ⟨payload, true⟩), (1, ⟨payload, false⟩)] =
    .ok [.absent 0 (0, ⟨payload, true⟩),
      .child ⟨boundary, 0, 1, ⟨payload, false⟩, (1, ⟨payload, false⟩)⟩] := by
  simp [shape, shapeField, lookupIndexed]

theorem first_duplicate_source (first second : Ty) :
    lookupIndexed [(7, ⟨first, true⟩), (7, ⟨second, false⟩)] 7 = some (0, ⟨first, true⟩) := by
  simp [lookupIndexed]

theorem diagnostic_discards_prefix (boundary : Meta) (payload : Ty) :
    shape boundary [(0, ⟨payload, false⟩)] 0
      [(0, ⟨payload, false⟩), (1, ⟨payload, false⟩)] =
      .error (.diagnosticMissing 1) := by
  simp [shape, shapeField, lookupIndexed]

theorem presence_unavailable (boundary : Meta) (payload : Ty) :
    shape boundary [(0, ⟨payload, true⟩)] 0 [(0, ⟨payload, false⟩)] =
      .error (.unavailablePresence 0 0) := by
  simp [shape, shapeField, lookupIndexed]

end Witness
end YulangClosure.NativeRecordPlan
