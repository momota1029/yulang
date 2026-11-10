import Yulang.CommonRoleFiniteSourceRenaming

/-!
# Canonical allocation computed from finite source identities

The first occurrence in the computed support determines each allocated name.
The capacity counts occurrences, not distinct names; unused indices are allowed.
Canonicality preserves occurrence order, not arbitrary sibling permutations.
This is representation exactness for the existing scalar/one-binder fragment,
not extraction from a parser or a rule for sharing distinct invocations.
-/
namespace Yulang.CommonRoleComputedSourceAllocation
open Roles
open CommonRoleAssociatedClauseExtraction (Source Clause Equation lower row)
open CommonRoleNamedSourceEntry (Assumptions Derives Models names runSource)
open CommonRoleNamedSourceRenaming
open CommonRoleFiniteSourceRenaming (support CollisionFree)

def encode (src : Source) (input : Assumptions) (name : Nat) : Nat :=
  (support src input).idxOf name

def allocate (src : Source) (input : Assumptions) : Source × Assumptions :=
  (renameSource (encode src input) src, renameInput (encode src input) input)

/-- Every used identity fits in a finite capacity computed from source/input. -/
theorem encode_bound (src : Source) (input : Assumptions) (name : Nat)
    (member : name ∈ support src input) : encode src input name < (support src input).length :=
  List.idxOf_lt_length_of_mem member

/-- Decoding is exact even when the support contains repeated identities. -/
theorem decode_encode (src : Source) (input : Assumptions) (name : Nat)
    (member : name ∈ support src input) :
    (support src input)[encode src input name]'(encode_bound src input name member) = name :=
  List.getElem_idxOf (encode_bound src input name member)

/-- Collision freedom is proved for the computed map, never supplied by a caller. -/
theorem encode_safe (src : Source) (input : Assumptions) :
    CollisionFree (encode src input) src input := by
  intro a ha b hb same
  have left := decode_encode src input a ha
  have right := decode_encode src input b hb
  simp only [same] at left
  exact left.symm.trans right

theorem checked_allocation (src : Source) (input : Assumptions) :
    CommonRoleFiniteSourceRenaming.renameChecked (encode src input) src input =
      some (allocate src input) := by
  apply (CommonRoleFiniteSourceRenaming.rename_checked_exact _ _ _ _ _).mpr
  exact ⟨encode_safe src input, rfl, rfl⟩

/-- Exact evidence for every query, including unused names. Unlike an arbitrary
safe map, this allocator sends unused names to capacity, outside the used range. -/
theorem allocated_derives (env : AssocEnv) (roles : RoleDecls)
    (src : Source) (input : Assumptions) (name : Nat) (head : Inference.Base) :
    Derives env roles (allocate src input).1 (allocate src input).2
      (encode src input name) head ↔ Derives env roles src input name head := by
  constructor
  · intro derived
    obtain ⟨old, same, previous⟩ := CommonRoleFiniteSourceRenaming.derives_original
      (encode src input) (encode_safe src input) env roles _ head derived
    have oldMember := CommonRoleFiniteSourceRenaming.derives_supported env roles src input old head previous
    have bound := encode_bound src input old oldMember
    rw [same] at bound
    have member : name ∈ support src input := List.idxOf_lt_length_iff.mp bound
    exact encode_safe src input old oldMember name member same ▸ previous
  · exact derives_rename (encode src input) env roles src input name head

theorem allocated_models (env : AssocEnv) (roles : RoleDecls)
    (src : Source) (input : Assumptions) :
    Models env roles (allocate src input).1 (allocate src input).2 ↔
      Models env roles src input :=
  CommonRoleFiniteSourceRenaming.models_exact _ (encode_safe src input) env roles

/-- Rechecks and resaturates after automatic allocation; no map, package, state,
model, fuel or successful solver result is a caller input. -/
theorem allocated_readiness (env : AssocEnv) (roles : RoleDecls)
    (wf : WellFormed env.cores) (awf : AssocWellFormed env roles)
    (src : Source) (input : Assumptions) :
    runSource env roles wf (allocate src input).1 (allocate src input).2 =
      runSource env roles wf src input :=
  CommonRoleFiniteSourceRenaming.run_source_exact _ (encode_safe src input) env roles wf awf

private theorem names_rename_list (f : Nat → Nat) (src : Source) :
    names (renameSource f src) = (names src).map f := by
  simp [names, renameSource, renameClause, renameEquation, lower, row,
    List.map_append, List.map_flatMap, List.flatMap_map, List.flatMap_assoc, List.map_map, Function.comp_def]

/-- The support list itself, including order and repetitions, commutes with renaming. -/
theorem support_rename (f : Nat → Nat) (src : Source) (input : Assumptions) :
    support (renameSource f src) (renameInput f input) = (support src input).map f := by
  simp [support, names_rename_list, renameInput, List.map_map, Function.comp_def]

/-- Every name occurring in the allocated source or input is within capacity. -/
theorem allocated_name_bound (src : Source) (input : Assumptions) (name : Nat)
    (member : name ∈ support (allocate src input).1 (allocate src input).2) :
    name < (support src input).length := by
  change name ∈ support (renameSource (encode src input) src)
    (renameInput (encode src input) input) at member
  rw [support_rename] at member
  obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
  exact encode_bound src input old oldMember

private theorem idxOf_map_supported (xs : List Nat) (f : Nat → Nat) (name : Nat)
    (member : name ∈ xs) (safe : ∀ a ∈ xs, ∀ b ∈ xs, f a = f b → a = b) :
    (xs.map f).idxOf (f name) = xs.idxOf name := by
  induction xs with
  | nil => simp at member
  | cons a rest ih =>
    by_cases same : a = name
    · subst name
      simp
    · have different : f a ≠ f name := fun h => same (safe a (by simp) name member h)
      have tail : name ∈ rest := (List.mem_cons.mp member).resolve_left (Ne.symm same)
      have tailSafe : ∀ a ∈ rest, ∀ b ∈ rest, f a = f b → a = b := by
        intro a ha b hb
        exact safe a (by simp [ha]) b (by simp [hb])
      simp only [List.map_cons, List.idxOf_cons, beq_iff_eq,
        ite_eq_right different, ite_eq_right same]
      exact congrArg (· + 1) (ih tail tailSafe)

/-- The generated indices are independent of any collision-free numeric encoding
of the same ordered occurrences. Global injectivity is unnecessary. -/
theorem encode_rename (f : Nat → Nat) (src : Source) (input : Assumptions)
    (safe : CollisionFree f src input) (name : Nat) (member : name ∈ support src input) :
    encode (renameSource f src) (renameInput f input) (f name) = encode src input name := by
  unfold encode
  rw [support_rename]
  exact idxOf_map_supported _ f name member safe

private theorem rename_pair_congr (src : Source) (input : Assumptions)
    (f g : Nat → Nat) (equal : ∀ name ∈ support src input, f name = g name) :
    (renameSource f src, renameInput f input) = (renameSource g src, renameInput g input) := by
  apply Prod.ext
  · apply List.map_congr_left
    intro c member
    have receiver := equal c.receiver (List.mem_append_left _
      ((CommonRoleNamedSourceEntry.names_member src _).mpr ⟨c, member, Or.inl rfl⟩))
    have equations : c.equations.map (renameEquation f) = c.equations.map (renameEquation g) := by
      apply List.map_congr_left
      intro e he
      have output := equal e.output (List.mem_append_left _
        ((CommonRoleNamedSourceEntry.names_member src _).mpr ⟨c, member, Or.inr ⟨e, he, rfl⟩⟩))
      simp [renameEquation, output]
    simp [renameClause, receiver, equations]
  · apply List.map_congr_left
    intro entry member
    have same := equal entry.1 (List.mem_append_right _ (List.mem_map.mpr ⟨entry, member, rfl⟩))
    simp [same]

private theorem rename_pair_comp (src : Source) (input : Assumptions) (f g : Nat → Nat) :
    (renameSource g (renameSource f src), renameInput g (renameInput f input)) =
      (renameSource (g ∘ f) src, renameInput (g ∘ f) input) := by
  simp [renameSource, renameClause, renameEquation, renameInput, List.map_map, Function.comp_def]

/-- Automatic allocation yields identical source/input pairs after any safe
renaming. It retains clause/equation/seed order, multiplicity and all non-name data. -/
theorem allocate_rename (f : Nat → Nat) (src : Source) (input : Assumptions)
    (safe : CollisionFree f src input) :
    allocate (renameSource f src) (renameInput f input) = allocate src input := by
  unfold allocate
  rw [rename_pair_comp]
  apply rename_pair_congr
  intro name member
  exact encode_rename f src input safe name member

/-- Repeated automatic allocation is a fixed point, not repeated freshness. -/
theorem allocate_idempotent (src : Source) (input : Assumptions) :
    allocate (allocate src input).1 (allocate src input).2 = allocate src input :=
  allocate_rename (encode src input) src input (encode_safe src input)

end Yulang.CommonRoleComputedSourceAllocation
