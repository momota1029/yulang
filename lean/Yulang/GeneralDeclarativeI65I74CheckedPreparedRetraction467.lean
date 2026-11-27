import Yulang.GeneralDeclarativeI65I74PreparationFootprint467
import Yulang.GeneralDeclarativeI65I74ProjectionBatchInput464

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.CheckedPreparedRetraction467
open GeneralDeclarativeHead320 (Equation)
private abbrev Raw := GeneralDeclarativeHead320.State
open GeneralDeclarativeI65.I72.PreparationFootprint467
open GeneralDeclarativeI65.I72.NamedProjection464 (exactOrdinaryState exact_ordinary_snapshot_iff)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeGraphRows321 (observed)
open PresenceNormalForm (Atom)

def explicitProject (code : List (Nat × Nat)) (n : Nat) : Nat :=
  ((code.find? fun x => x.1 == n).map Prod.snd).getD n

def fixedPair (project : Nat → Nat) (p : Nat × Nat) : Bool :=
  decide (project p.1 = p.1 ∧ project p.2 = p.2)

def boundsIn : Atom Nat → Option (Nat × Nat)
  | .tyLe (.var a) (.var b) => some (a,b)
  | _ => none

def aliasesIn (row : Equation) : Option (Nat × Nat) :=
  match row.right with
  | .variable n => some (row.left,n)
  | _ => none

def boundGenerators (s : Raw) : List (Nat × Nat) :=
  s.normal.intervals ++
  (s.normal.ordinary.filterMap boundsIn) ++ (s.equations.filterMap aliasesIn)

def withMoreAtoms (s : Raw) (added : List (Atom Nat)) : Raw :=
  {s with normal := {s.normal with ordinary := s.normal.ordinary ++ added}}

def appendingSuffix (s t : Raw) : List (Atom Nat) :=
  t.normal.ordinary.drop s.normal.ordinary.length

def checkPreparedRetraction (s t : Raw) (wire : List (Nat × Nat)) (root : Nat) : Bool :=
  let map := explicitProject wire
  let added := appendingSuffix s t
  exactOrdinaryState (withMoreAtoms s added) t &&
    (boundGenerators s).all (fixedPair map) &&
    (added.filterMap boundsIn).all (fun xy => decide (map xy.1 = map xy.2)) &&
    fixesNamedScope s map root

def ExactPreparedRetraction (s t : Raw) (wire : List (Nat × Nat)) (root : Nat) : Prop :=
  let p := explicitProject wire
  ∃ added : List (Atom Nat), t = withMoreAtoms s added ∧
    (∀ x ∈ s.normal.intervals, p x.1 = x.1 ∧ p x.2 = x.2) ∧
    (∀ a b, Atom.tyLe (.var a) (.var b) ∈ s.normal.ordinary → p a = a ∧ p b = b) ∧
    (∀ a b, (⟨a,.variable b⟩ : Equation) ∈ s.equations → p a = a ∧ p b = b) ∧
    (∀ a b, Atom.tyLe (.var a) (.var b) ∈ added → p a = p b) ∧
    (∀ n ∈ root :: observedFootprint s, p n = n)

theorem bounded_atom_pair_is_exact {a b : Nat} {l : List (Atom Nat)} :
    (a,b) ∈ l.filterMap boundsIn ↔ Atom.tyLe (.var a) (.var b) ∈ l := by
  constructor
  · intro contains
    obtain ⟨atom,mem,image⟩ := List.mem_filterMap.mp contains
    cases atom with
    | tyLe x y =>
      cases x <;> cases y <;> simp [boundsIn] at image
      obtain ⟨rfl,rfl⟩ := image
      exact mem
    | rowLe x y => simp [boundsIn] at image
  · intro mem
    exact List.mem_filterMap.mpr ⟨_,mem,rfl⟩

theorem explicit_variable_row_pair_is_exact {a b : Nat} {l : List Equation} :
    (a,b) ∈ l.filterMap aliasesIn ↔ (⟨a,.variable b⟩ : Equation) ∈ l := by
  constructor
  · intro contains
    obtain ⟨⟨own,code⟩,mem,image⟩ := List.mem_filterMap.mp contains
    cases code <;> simp [aliasesIn] at image
    obtain ⟨rfl,rfl⟩ := image
    exact mem
  · intro mem
    exact List.mem_filterMap.mpr ⟨_,mem,rfl⟩

theorem exact_finite_preparation_retraction_check
    (s t : Raw) (wire : List (Nat × Nat)) (root : Nat) :
    checkPreparedRetraction s t wire root = true ↔ ExactPreparedRetraction s t wire root := by
  unfold checkPreparedRetraction ExactPreparedRetraction
  simp only [Bool.and_eq_true,exact_ordinary_snapshot_iff,List.all_eq_true,fixedPair,
    decide_eq_true_eq,fixesNamedScope]
  constructor
  · rintro ⟨⟨⟨same,generators⟩,collapse⟩,pin⟩
    refine ⟨_,same.symm,?_,?_,?_,?_,pin⟩
    · intro x mem
      exact generators x (by simp [boundGenerators,mem])
    · intro a b atom
      have h := bounded_atom_pair_is_exact.mpr atom
      exact generators (a,b) (by simp [boundGenerators,h])
    · intro a b atom
      have h := explicit_variable_row_pair_is_exact.mpr atom
      exact generators (a,b) (by simp [boundGenerators,h])
    · intro a b atom
      exact collapse (a,b) (bounded_atom_pair_is_exact.mpr atom)
  · rintro ⟨added,same,intervals,generators,aliases,newAtoms,fixed⟩
    have suffix : appendingSuffix s t = added := by simp [appendingSuffix,same,withMoreAtoms]
    refine ⟨⟨⟨by rw [suffix]; exact same.symm,?_⟩,?_⟩,fixed⟩
    · rintro ⟨a,b⟩ used
      simp only [boundGenerators,List.mem_append] at used
      rcases used with (old|bound)|alias
      · exact intervals _ old
      · exact generators _ _ (bounded_atom_pair_is_exact.mp bound)
      · exact aliases _ _ (explicit_variable_row_pair_is_exact.mp alias)
    · rintro ⟨a,b⟩ used
      rw [suffix] at used
      exact newAtoms _ _ (bounded_atom_pair_is_exact.mp used)

theorem finite_retraction_certificate_supplies_exact_generators
    {s t : Raw} {wire : List (Nat × Nat)} {root : Nat}
    (check : checkPreparedRetraction s t wire root = true) :
    s.equations = t.equations ∧ OrdinaryRetraction s t (explicitProject wire) ∧
      fixesNamedScope s (explicitProject wire) root = true := by
  obtain ⟨added,same,intvs,oldAtoms,oldRows,newAtoms,fixed⟩ :=
    (exact_finite_preparation_retraction_check ..).mp check
  have row : s.equations = t.equations := by rw [same]; rfl
  have itv : s.normal.intervals = t.normal.intervals := by rw [same]; rfl
  have atoms : t.normal.ordinary = s.normal.ordinary ++ added := by rw [same]; rfl
  let r := ordinary_retraction_of_collapsing_appended_atoms (project := explicitProject wire)
    row itv atoms (fun mem => intvs _ mem) (fun mem => oldAtoms _ _ mem)
    (fun mem => oldRows _ _ mem) (fun mem => newAtoms _ _ mem)
  exact ⟨row,r,List.all_eq_true.mpr (fun n mem => decide_eq_true (fixed n mem))⟩

theorem certified_prepare_maps_raw_k2_at_the_same_original_query
    {s t : Raw} {wire : List (Nat × Nat)} {root : Nat}
    (check : checkPreparedRetraction s t wire root = true) :
    AliasCycle s (observed s) root ↔ AliasCycle t (observed t) root := by
  obtain ⟨row,r,pin⟩ := finite_retraction_certificate_supplies_exact_generators check
  exact actual_original_cycle_same_if_finite_pinned_names_fixed r row pin

end Yulang.GeneralDeclarativeI65.I72.CheckedPreparedRetraction467
