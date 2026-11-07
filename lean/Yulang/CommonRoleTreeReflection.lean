import Yulang.CanonicalComputability
import Yulang.CommonRoleSemanticPadding
import Yulang.CommonCanonicalShapes

/-!
# Reflection of Common pattern matching on finite tree inputs

Substitutions used by semantic role matching range over all Common types.
This module proves that such matches on an encoded finite tree have ordinary
finite-tree witnesses, and that range-restricted children preserve them.
-/

namespace Yulang.CommonRoleSemanticPadding

open CanonicalComputability (Data)

def encodeTree : Data → Common.Ty
  | .nil => .base .unit
  | .cons first last => Common.pair (encodeTree first) (encodeTree last)

def Pattern.instantiate (assignment : Nat → Data) : Pattern → Data
  | .var name => assignment name
  | .nil => .nil
  | .pair first last => .cons (first.instantiate assignment) (last.instantiate assignment)

/-- Every semantic source match has a finite-tree witness that also
interprets every range-restricted target. No shape restriction is placed on
the original Common substitution. -/
theorem pattern_match_reflects (source target : Pattern) (assignment : Nat → Common.Ty)
    (input : Data) (closed : RangeRestricted source target)
    (matchedSource : Common.Equivalent (source.eval assignment) (encodeTree input)) :
    ∃ replacement : Nat → Data,
      source.instantiate replacement = input ∧
      Common.Equivalent (target.eval assignment) (encodeTree (target.instantiate replacement)) := by
  have nilNotPair (first last : Common.Ty) :
      ¬ Common.Equivalent (.base .unit) (Common.pair first last) := by
    intro same
    have observed := (CommonCanonicalShapes.equivalent_iff_probes _ _).mp same
      0 0 ⟨fun _ => .bottom, fun _ => []⟩ (.base .unit)
    simp [Common.pair, Common.observeTy, CommonSyntax.Layer.evalAt,
      CommonSyntax.observe, CommonFinite.ProbeAt, CommonFinite.ProbeStep,
      CommonFinite.MaskedProbeStep] at observed
  have injective (first last : Data)
      (same : Common.Equivalent (encodeTree first) (encodeTree last)) : first = last := by
    induction first generalizing last with
    | nil =>
        cases last with
        | nil => rfl
        | cons first last => exact False.elim (nilNotPair _ _ same)
    | cons first tail ihf ihl =>
        cases last with
        | nil => exact False.elim (nilNotPair _ _ (Common.equivalent_symm same))
        | cons nextFirst nextLast =>
            obtain ⟨hf, hl⟩ := (CommonCanonicalShapes.pair_equivalent_iff _ _ _ _).mp same
            rw [ihf _ hf, ihl _ hl]
  have variables (pattern : Pattern) (tree : Data)
      (matched : Common.Equivalent (pattern.eval assignment) (encodeTree tree)) :
      ∀ name, pattern.occurrences name ≠ 0 →
        ∃ value : Data, Common.Equivalent (assignment name) (encodeTree value) := by
    induction pattern generalizing tree with
    | var index =>
        intro name used
        have same : name = index := by
          by_cases same : name = index
          · exact same
          · exact False.elim (used (by simp [Pattern.occurrences, same]))
        subst name
        exact ⟨tree, matched⟩
    | nil => intro name used; exact False.elim (used rfl)
    | pair first last ihf ihl =>
        cases tree with
        | nil => exact False.elim (nilNotPair _ _ (Common.equivalent_symm matched))
        | cons treeFirst treeLast =>
            obtain ⟨hf, hl⟩ := (CommonCanonicalShapes.pair_equivalent_iff _ _ _ _).mp matched
            intro name used
            by_cases leftUsed : first.occurrences name = 0
            · apply ihl treeLast hl name
              simpa [Pattern.occurrences, leftUsed] using used
            · exact ihf treeFirst hf name leftUsed
  classical
  let replacement : Nat → Data := fun name =>
    if h : source.occurrences name ≠ 0 then (variables source input matchedSource name h).choose
    else .nil
  have represented (name : Nat) (used : source.occurrences name ≠ 0) :
      Common.Equivalent (assignment name) (encodeTree (replacement name)) := by
    simpa [replacement, used] using (variables source input matchedSource name used).choose_spec
  have evaluate (pattern : Pattern)
      (restricted : RangeRestricted source pattern) :
      Common.Equivalent (pattern.eval assignment) (encodeTree (pattern.instantiate replacement)) := by
    induction pattern with
    | var name =>
        apply represented
        intro absent
        have impossible := restricted name absent
        simp [Pattern.occurrences] at impossible
    | nil => exact Common.equivalent_refl _
    | pair first last ihf ihl =>
        apply (CommonCanonicalShapes.pair_equivalent_iff _ _ _ _).mpr
        constructor
        · apply ihf
          intro name absent
          have both := restricted name absent
          simp only [Pattern.occurrences, Nat.add_eq_zero_iff] at both
          exact both.1
        · apply ihl
          intro name absent
          have both := restricted name absent
          simp only [Pattern.occurrences, Nat.add_eq_zero_iff] at both
          exact both.2
  refine ⟨replacement, ?_, evaluate target closed⟩
  exact injective _ _ (Common.equivalent_trans
    (Common.equivalent_symm (evaluate source (fun _ absent => absent))) matchedSource)

end Yulang.CommonRoleSemanticPadding
