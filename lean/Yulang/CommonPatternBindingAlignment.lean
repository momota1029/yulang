import Yulang.CaseDataTerms

/-!
# Name-based alignment of pattern output environments

Reordering is confined to an or-pattern interface. Written-order processing
inside either branch remains a separate obligation. The concrete data-leaf
evaluation theorem preserves the whole logged return/error observation.
-/

namespace Yulang.CommonPatternBindingAlignment

def lookup (name : Nat) : List (Nat × A) → Option A
  | [] => none
  | (current, value) :: rest => if name = current then some value else lookup name rest

def reorder (names : List Nat) (bindings : List (Nat × A)) : List (Nat × A) :=
  match names with
  | [] => []
  | name :: rest => match lookup name bindings with
      | none => reorder rest bindings
      | some value => (name, value) :: reorder rest bindings

theorem lookup_values (name : Nat) (bindings : CaseValues.Bindings F) :
    lookup name bindings = CaseValues.lookup name bindings := by
  induction bindings with
  | nil => rfl
  | cons binding rest ih =>
      rcases binding with ⟨current, value⟩
      simp only [lookup, CaseValues.lookup, ih]

theorem lookup_isSome (name : Nat) (bindings : List (Nat × A)) :
    (lookup name bindings).isSome = true ↔ name ∈ bindings.map Prod.fst := by
  induction bindings with
  | nil => simp [lookup]
  | cons binding rest ih =>
      rcases binding with ⟨current, value⟩
      by_cases same : name = current <;> simp [lookup, same, ih]

theorem lookup_reorder (name : Nat) (names : List Nat) (bindings : List (Nat × A)) :
    lookup name (reorder names bindings) = if name ∈ names then lookup name bindings else none := by
  induction names with
  | nil => simp [reorder, lookup]
  | cons current rest ih =>
      cases found : lookup current bindings with
      | none =>
          by_cases same : name = current
          · subst name; simp [reorder, found, ih]
          · simp [reorder, found, ih, same]
      | some value =>
          by_cases same : name = current
          · subst name; simp [reorder, found, lookup]
          · simp [reorder, found, lookup, ih, same]

theorem reorder_names (names : List Nat) (bindings : List (Nat × A))
    (available : ∀ name ∈ names, name ∈ bindings.map Prod.fst) :
    (reorder names bindings).map Prod.fst = names := by
  induction names with
  | nil => rfl
  | cons current rest ih =>
      have found : (lookup current bindings).isSome = true :=
        (lookup_isSome current bindings).mpr (available current List.mem_cons_self)
      cases selected : lookup current bindings with
      | none => rw [selected] at found; cases found
      | some value =>
          simp only [reorder, selected, List.map_cons, List.cons.injEq, true_and]
          exact ih (fun name member => available name (List.mem_cons_of_mem _ member))

def LookupEq (first last : List (Nat × A)) : Prop := ∀ name, lookup name first = lookup name last

theorem reorder_lookup_eq (names : List Nat) (bindings : List (Nat × A))
    (retained : ∀ name ∈ bindings.map Prod.fst, name ∈ names) : LookupEq (reorder names bindings) bindings := by
  intro name
  rw [lookup_reorder]
  split
  · rfl
  · rename_i absent
    cases selected : lookup name bindings with
    | none => rfl
    | some value =>
        have present := (lookup_isSome name bindings).mp (by simp [selected])
        exact False.elim (absent (retained name present))

theorem lookup_append (name : Nat) (first last : List (Nat × A)) :
    lookup name (first ++ last) = (lookup name first).orElse (fun _ => lookup name last) := by
  induction first with
  | nil => rfl
  | cons binding rest ih =>
      rcases binding with ⟨current, value⟩
      by_cases same : name = current <;> simp [lookup, same, ih]

theorem LookupEq.append {first last : List (Nat × A)} (same : LookupEq first last) (outer : List (Nat × A)) :
    LookupEq (first ++ outer) (last ++ outer) := by
  intro name
  simp only [lookup_append, same name]

theorem LookupEq.cons {first last : List (Nat × A)} (same : LookupEq first last) (name : Nat) (value : A) :
    LookupEq ((name, value) :: first) ((name, value) :: last) := by
  intro current
  simp only [lookup, same current]

/-- Every concrete named data expression, including computed lets and errors,
has exactly the same value/error and full source trace under equal lookups. -/
theorem data_eval_lookup_eq (expression : CaseDataTerms.Expr F)
    (first last : CaseValues.Bindings F) (same : LookupEq first last) :
    CaseDataTerms.eval first expression = CaseDataTerms.eval last expression := by
  induction expression generalizing first last with
  | value | emptyRecord | nil => rfl
  | var name => simp only [CaseDataTerms.eval, ← lookup_values, same name]
  | pair left right ihl ihr | record name left right ihl ihr
      | recordDefault name left right ihl ihr | cons left right ihl ihr =>
      simp only [CaseDataTerms.eval, ihl first last same, ihr first last same]
  | fst child ih | snd child ih | field name child ih | variant tag child ih
      | nominal typeId ctorId child ih =>
      simp only [CaseDataTerms.eval, ih first last same]
  | letE name value body ihv ihb =>
      simp only [CaseDataTerms.eval, ihv first last same]
      congr 2
      funext value
      exact ihb _ _ (same.cons name value)

theorem data_eval_reorder (expression : CaseDataTerms.Expr F) (names : List Nat)
    (bindings outer : CaseValues.Bindings F)
    (retained : ∀ name ∈ bindings.map Prod.fst, name ∈ names) :
    CaseDataTerms.eval (reorder names bindings ++ outer) expression =
      CaseDataTerms.eval (bindings ++ outer) expression :=
  data_eval_lookup_eq expression _ _ ((reorder_lookup_eq names bindings retained).append outer)

def mapValues (f : A → B) (bindings : List (Nat × A)) : List (Nat × B) :=
  bindings.map fun binding => (binding.1, f binding.2)

theorem lookup_mapValues (f : A → B) (name : Nat) (bindings : List (Nat × A)) :
    lookup name (mapValues f bindings) = (lookup name bindings).map f := by
  induction bindings with
  | nil => rfl
  | cons binding rest ih =>
      rcases binding with ⟨current, value⟩
      change lookup name ((current, f value) :: mapValues f rest) =
        (lookup name ((current, value) :: rest)).map f
      by_cases same : name = current <;> simp only [lookup, same, ↓reduceIte, Option.map_some, ih]

theorem reorder_mapValues (f : A → B) (names : List Nat) (bindings : List (Nat × A)) :
    reorder names (mapValues f bindings) = mapValues f (reorder names bindings) := by
  induction names with
  | nil => rfl
  | cons name rest ih =>
      simp only [reorder, lookup_mapValues]
      cases found : lookup name bindings with
      | none => exact ih
      | some value => exact congrArg (List.cons (name, f value)) ih

def LookupHolds : Option (CaseValues.Ty F) → Option (CaseValues.Value F) → Prop
  | none, none => True
  | some type, some value => type value
  | _, _ => False

theorem lookup_holds (typed : CaseValues.BindingsHold types values) (name : Nat) :
    LookupHolds (lookup name types) (lookup name values) := by
  induction typed with
  | nil => trivial
  | @cons type types values current value head tail ih =>
      by_cases same : name = current
      · simpa only [lookup, same, ↓reduceIte, LookupHolds] using head
      · simpa only [lookup, same, ↓reduceIte] using ih

/-- Type and actual-value lists are reordered by the same resolved names.
No type equivalence is substituted for literal binding identity. -/
theorem reorder_bindings_hold (names : List Nat) (typed : CaseValues.BindingsHold types values) :
    CaseValues.BindingsHold (reorder names types) (reorder names values) := by
  induction names with
  | nil => exact .nil
  | cons name rest ih =>
      have paired := lookup_holds typed name
      cases first : lookup name types <;> cases last : lookup name values
      all_goals rw [first, last] at paired
      · simpa only [reorder, first, last] using ih
      · cases paired
      · cases paired
      · simpa only [reorder, first, last] using CaseValues.BindingsHold.cons paired ih

theorem reorder_congr (names : List Nat) (first last : List (Nat × A))
    (same : ∀ name ∈ names, lookup name first = lookup name last) :
    reorder names first = reorder names last := by
  induction names with
  | nil => rfl
  | cons name rest ih =>
      have head := same name List.mem_cons_self
      have tail := ih (fun n member => same n (List.mem_cons_of_mem _ member))
      simp only [reorder, head]
      cases lookup name last <;> first | exact tail | exact congrArg (List.cons _) tail

theorem reorder_self (bindings : List (Nat × A)) (distinct : (bindings.map Prod.fst).Nodup) :
    reorder (bindings.map Prod.fst) bindings = bindings := by
  induction bindings with
  | nil => rfl
  | cons binding rest ih =>
      rcases binding with ⟨name, value⟩
      have apart := List.nodup_cons.mp distinct
      simp only [List.map_cons, reorder, lookup, ↓reduceIte]
      congr 1
      rw [reorder_congr (rest.map Prod.fst) ((name, value) :: rest) rest (by
        intro current member
        have different : current ≠ name := by intro equal; subst current; exact apart.1 member
        simp only [lookup, different, ↓reduceIte])]
      exact ih apart.2

theorem reorder_roundtrip (first last : List Nat) (bindings : List (Nat × A))
    (names : bindings.map Prod.fst = first) (distinct : first.Nodup)
    (retained : ∀ name ∈ first, name ∈ last) :
    reorder first (reorder last bindings) = bindings := by
  have same := reorder_lookup_eq last bindings (by simpa only [names] using retained)
  rw [reorder_congr first (reorder last bindings) bindings (fun name _ => same name), ← names]
  exact reorder_self bindings (names ▸ distinct)

theorem lookup_mem (name : Nat) (bindings : List (Nat × A)) (found : lookup name bindings = some value) :
    (name, value) ∈ bindings := by
  induction bindings with
  | nil => cases found
  | cons binding rest ih =>
      rcases binding with ⟨current, item⟩
      by_cases same : name = current
      · subst current
        have equal : item = value := by simpa [lookup] using found
        subst item
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih (by simpa [lookup, same] using found))

theorem reorder_mem (names : List Nat) (bindings : List (Nat × A)) : reorder names bindings ⊆ bindings := by
  induction names with
  | nil => intro binding member; cases member
  | cons name rest ih =>
      intro binding member
      cases found : lookup name bindings with
      | none => exact ih (by simpa only [reorder, found] using member)
      | some value =>
          simp only [reorder, found] at member
          rcases List.mem_cons.mp member with rfl | member
          · exact lookup_mem name bindings found
          · exact ih member

end Yulang.CommonPatternBindingAlignment
