import Yulang.GeneralDeclarativeI65I74WhereLegacy450
import Yulang.GeneralDeclarativeI65I74SplitEscapeFinite446

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WhereSites450.OriginalCohorts451
open Yulang.GeneralDeclarativeI65
open GeneralDeclarativeHead320 (Equation)
abbrev Raw := GeneralDeclarativeHead320.State
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeLowerKnown321 (alias_refl alias_symm)
open GeneralDeclarativeWitnessRank350 (rank atom)
open List410 (colour ExactEscapeWire aliasRow)
open SplitEscape446 (rawLimit root_inside446 write_name_inside446 flatEnd
  bound_support_from_actual_rows446 BoundSupport boundGrades bound_grade_monotone446
  equal_active_grades_are_exact_SCC446 active_grade_bounded446)
abbrev Al := GeneralDeclarativeLowerKnown321.Alias

structure HasSideSeparation (s : Raw) (l r : Nat) (w : ExactEscapeWire) : Prop where
  boundMonotone : ∀ a b, Bound s.normal a b → rank w.ranks a ≤ rank w.ranks b
  flatAlias : ∀ row ∈ s.equations, ∀ n, row.right = .variable n → w.side row.left = w.side n
  unequalSide : w.side l ≠ w.side r

def checkSeparation (s : Raw) (l r : Nat) (w : ExactEscapeWire) : Bool :=
  ((s.normal.ordinary.all (atom (rank w.ranks)) &&
    s.normal.intervals.all (fun e => decide (rank w.ranks e.1 ≤ rank w.ranks e.2))) &&
    s.equations.all (aliasRow w.side)) && decide (w.side l ≠ w.side r)

theorem check_side_sep_exact450 {s : Raw} {l r} {w : ExactEscapeWire} :
    checkSeparation s l r w = true ↔ HasSideSeparation s l r w := by
  unfold checkSeparation
  constructor
  · intro ok
    obtain ⟨outer,neq⟩ := Bool.and_eq_true_iff.mp ok
    obtain ⟨ordered,flat⟩ := Bool.and_eq_true_iff.mp outer
    obtain ⟨atoms,intervals⟩ := Bool.and_eq_true_iff.mp ordered
    refine ⟨?_,?_,of_decide_eq_true neq⟩
    · intro a b t
      induction t with
      | interval present => exact of_decide_eq_true (List.all_eq_true.mp intervals _ present)
      | constraint present => exact of_decide_eq_true (List.all_eq_true.mp atoms _ present)
      | refl => exact Nat.le_refl _
      | trans _ _ left right => exact Nat.le_trans left right
    · intro e seen n form
      have valid := List.all_eq_true.mp flat e seen
      unfold aliasRow at valid
      rw [form] at valid
      exact of_decide_eq_true valid
  · intro valid
    refine Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr ⟨?_,?_⟩,?_⟩,decide_eq_true valid.unequalSide⟩
    · apply List.all_eq_true.mpr
      intro active inRows
      cases active with
      | rowLe => rfl
      | tyLe a b =>
        cases a <;> cases b <;>
          first | rfl | exact decide_eq_true (valid.boundMonotone _ _ (.constraint inRows))
    · apply List.all_eq_true.mpr
      rintro ⟨x,y⟩ observed
      exact decide_eq_true (valid.boundMonotone _ _ (.interval observed))
    · apply List.all_eq_true.mpr
      intro observed inRows
      unfold aliasRow
      split
      · rename_i index form
        exact decide_eq_true (valid.flatAlias _ inRows _ form)
      · rfl

theorem separation_only_excludes_raw_alias450 {s : Raw} {l r} {w : ExactEscapeWire}
    (valid : HasSideSeparation s l r w) : ¬Al s l r := by
  have cut : ∀ a b, Al s a b → w.side a = w.side b := by
    intro a b same
    induction same with
    | bounds h j =>
      exact congrArg (colour w.palette)
        (Nat.le_antisymm (valid.boundMonotone _ _ h) (valid.boundMonotone _ _ j))
    | forward h => exact valid.flatAlias _ h _ rfl
    | backward h => exact (valid.flatAlias _ h _ rfl).symm
    | trans _ _ first next => exact first.trans next
  exact fun h => valid.unequalSide (cut l r h)

noncomputable def classBit (s : Raw) (l n : Nat) : Nat := by
  classical
  exact if Al s l n then 0 else 1

theorem alias_does_not_change_class_bit450 {s : Raw} {l x y} (sames : Al s x y) :
    classBit s l x = classBit s l y := by
  classical
  have rel : Al s l x ↔ Al s l y :=
    ⟨fun h => .trans h sames,fun h => .trans h (alias_symm sames)⟩
  unfold classBit
  simp only [rel]

noncomputable def classPalette (s : Raw) (l limit grade : Nat) : Nat := by
  classical
  exact if found : ∃ i : Fin limit, rank (boundGrades s.normal limit) i.val = grade
    then classBit s l (Classical.choose found).val else 1

noncomputable def sepFinite (s : Raw) (l r : Nat) : ExactEscapeWire :=
  let n := max (rawLimit s l) (rawLimit s r)
  ⟨boundGrades s.normal n, List.ofFn (fun i : Fin (2^n + 1) => classPalette s l n i.val)⟩

theorem sep_reads_exact_raw_class450 {s : Raw} {l r p}
    (pInside : p < max (rawLimit s l) (rawLimit s r)) :
    (sepFinite s l r).side p = classBit s l p := by
  classical
  let n := max (rawLimit s l) (rawLimit s r)
  let a := rank (boundGrades s.normal n) p
  have tiny : a < 2 ^ n + 1 := active_grade_bounded446 pInside
  have inGrades : ∃ i : Fin n, rank (boundGrades s.normal n) i.val = a :=
    ⟨⟨p,pInside⟩,rfl⟩
  change colour (List.ofFn fun i : Fin (2^n + 1) => classPalette s l n i.val) a = _
  unfold colour
  simp only [List.getElem?_ofFn,dite_eq_left tiny,Option.getD_some]
  change classPalette s l n a = _
  unfold classPalette
  rw [dite_eq_left inGrades]
  obtain ⟨there,back⟩ := equal_active_grades_are_exact_SCC446
    (Classical.choose inGrades).isLt pInside (Classical.choose_spec inGrades)
  exact alias_does_not_change_class_bit450 (.bounds there back)

theorem negative_raw_alias_has_finite_side_certificate450 (s : Raw) (l r : Nat)
    (no : ¬Al s l r) : HasSideSeparation s l r (sepFinite s l r) := by
  classical
  let n := max (rawLimit s l) (rawLimit s r)
  let ltMax : rawLimit s l ≤ n := Nat.le_max_left _ _
  have support : BoundSupport s.normal n := by
    refine ⟨?_,?_⟩
    · intro a b used
      exact ((bound_support_from_actual_rows446 s l).interval a b used).imp
        (Nat.lt_of_lt_of_le · ltMax) (Nat.lt_of_lt_of_le · ltMax)
    · intro a b used
      exact ((bound_support_from_actual_rows446 s l).atom a b used).imp
        (Nat.lt_of_lt_of_le · ltMax) (Nat.lt_of_lt_of_le · ltMax)
  refine ⟨fun a b h => bound_grade_monotone446 support h,?_,?_⟩
  · intro e seen name code
    have ownerInside : e.left < n := Nat.lt_of_lt_of_le (write_name_inside446 (site := l) seen List.mem_cons_self) ltMax
    have foundInside : name < n := Nat.lt_of_lt_of_le (write_name_inside446 (site := l) seen
      (List.mem_cons_of_mem _ (List.mem_append_left _ (by simp [flatEnd,code])))) ltMax
    rw [sep_reads_exact_raw_class450 ownerInside,sep_reads_exact_raw_class450 foundInside]
    have row : (⟨e.left,.variable name⟩ : Equation) ∈ s.equations := by
      cases e; dsimp at code ⊢; subst_vars; exact seen
    exact alias_does_not_change_class_bit450 (.forward row)
  · rw [sep_reads_exact_raw_class450 (Nat.lt_of_lt_of_le (root_inside446 s l) ltMax),
      sep_reads_exact_raw_class450 (Nat.lt_of_lt_of_le (root_inside446 s r) (Nat.le_max_right _ _))]
    simp [classBit,alias_refl,no]

theorem cooked_raw_alias_complement_has_precise_finite_witness450 (s : Raw) (l r : Nat) :
    (¬Al s l r) ↔ ∃ w, checkSeparation s l r w = true :=
  ⟨fun no => ⟨_,check_side_sep_exact450.mpr (negative_raw_alias_has_finite_side_certificate450 s l r no)⟩,
    fun ⟨_,yes⟩ => separation_only_excludes_raw_alias450 (check_side_sep_exact450.mp yes)⟩

abbrev RolePoint := Nat × Nat

def RawSame (s : Raw) (left right : RolePoint) : Prop :=
  left.1 = right.1 ∧ Al s left.2 right.2

inductive ExactPairWire where
  | linked (w : GeneralDeclarativeWitnessCycle350.Link)
  | otherRole
  | separate (w : ExactEscapeWire)

def checkRawPair (s : Raw) (l r : RolePoint) : ExactPairWire → Option Bool
  | .linked w => if l.1 == r.1 && GeneralDeclarativeWitnessCycle350.checksLink s l.2 r.2 w
      then some true else none
  | .otherRole => if l.1 == r.1 then none else some false
  | .separate w => if checkSeparation s l.2 r.2 w then some false else none

theorem exact_raw_pair_true450 (s : Raw) (l r : RolePoint) :
    (∃ wire, checkRawPair s l r wire = some true) ↔ RawSame s l r := by
  constructor
  · rintro ⟨w,h⟩
    cases w with
    | linked w =>
      simp only [checkRawPair] at h
      split at h
      · rename_i good
        obtain ⟨role,path⟩ := Bool.and_eq_true_iff.mp good
        exact ⟨eq_of_beq role,GeneralDeclarativeWitnessCycle350.link path⟩
      · cases h
    | otherRole => simp only [checkRawPair] at h; split at h <;> cases h
    | separate w => simp only [checkRawPair] at h; split at h <;> cases h
  · rintro ⟨role,path⟩
    obtain ⟨w,yes⟩ := alias_wire_from_actual_derivation450 path
    exact ⟨.linked w,by simp [checkRawPair,role,yes]⟩

theorem exact_raw_pair_false450 (s : Raw) (l r : RolePoint) :
    (∃ wire, checkRawPair s l r wire = some false) ↔ ¬RawSame s l r := by
  constructor
  · rintro ⟨w,h⟩
    cases w with
    | linked w => simp only [checkRawPair] at h; split at h <;> cases h
    | otherRole =>
      simp only [checkRawPair] at h
      split at h
      · cases h
      · rename_i neq
        exact fun e => neq (by simp [e.1])
    | separate w =>
      simp only [checkRawPair] at h
      split at h
      · rename_i good
        exact fun e => separation_only_excludes_raw_alias450 (check_side_sep_exact450.mp good) e.2
      · cases h
  · intro different
    by_cases roles : l.1 = r.1
    · have no : ¬Al s l.2 r.2 := fun e => different ⟨roles,e⟩
      obtain ⟨w,yes⟩ := (cooked_raw_alias_complement_has_precise_finite_witness450 s l.2 r.2).mp no
      exact ⟨.separate w,by simp [checkRawPair,yes]⟩
    · exact ⟨.otherRole,by simp [checkRawPair,roles]⟩


open SplitEscape446 (mask bitValue mask_mono446 mask_eq_at_each_name446)

theorem rawSame_refl (s : Raw) (p : RolePoint) : RawSame s p p :=
  ⟨rfl,alias_refl _⟩
theorem rawSame_symm {s : Raw} {p q : RolePoint} (h : RawSame s p q) : RawSame s q p :=
  ⟨h.1.symm,alias_symm h.2⟩
theorem rawSame_trans {s : Raw} {p q r : RolePoint} (h : RawSame s p q) (j : RawSame s q r) :
    RawSame s p r := ⟨h.1.trans j.1,.trans h.2 j.2⟩

noncomputable def classBits (s : Raw) (pts : List RolePoint) (p : RolePoint) (i : Nat) : Bool := by
  classical
  exact match pts[i]? with
  | none => false
  | some q => decide (RawSame s p q)

noncomputable def classKey (s : Raw) (pts : List RolePoint) (p : RolePoint) : Nat :=
  mask (List.range pts.length) (classBits s pts p)

theorem key_reflects_raw_pair450 {s : Raw} {pts : List RolePoint} {p q : RolePoint}
    (atRight : q ∈ pts) : classKey s pts p = classKey s pts q ↔ RawSame s p q := by
  classical
  constructor
  · intro eq
    obtain ⟨i,indexed⟩ := List.mem_iff_getElem?.mp atRight
    have inRange := List.mem_range.mpr (List.getElem?_eq_some_iff.mp indexed).choose
    have bits := mask_eq_at_each_name446 (List.range pts.length) _ _ eq i inRange
    simpa [classBits,indexed,rawSame_refl] using bits
  · intro h
    have bits (i : Nat) : classBits s pts p i = classBits s pts q i := by
      cases found : pts[i]? with
      | none => simp [classBits,found]
      | some x =>
        have same : RawSame s p x ↔ RawSame s q x :=
          ⟨fun hx => rawSame_trans (rawSame_symm h) hx,rawSame_trans h⟩
        simp [classBits,found,same]
    apply Nat.le_antisymm <;> apply mask_mono446 <;> intro x _ t
    · exact (bits x).symm ▸ t
    · exact (bits x) ▸ t

abbrev Labeled := RolePoint × Nat

def readClassRow (s : Raw) (a : Labeled) : List Labeled → List ExactPairWire → Bool
  | [],[] => true
  | b::bs,w::ws =>
    (checkRawPair s a.1 b.1 w == some (a.2 == b.2)) && readClassRow s a bs ws
  | _,_ => false

def ClassRow (s : Raw) (a : Labeled) (row : List Labeled) : Prop :=
  ∀ b ∈ row, a.2 = b.2 ↔ RawSame s a.1 b.1

theorem one_raw_matrix_row_has_exact_finite_certificate450 (s : Raw) (a : Labeled) (row : List Labeled) :
    (∃ ws, readClassRow s a row ws = true) ↔ ClassRow s a row := by
  induction row with
  | nil =>
    exact ⟨fun _ b h => (List.not_mem_nil h).elim,fun _ => ⟨[],rfl⟩⟩
  | cons first rest ih =>
    constructor
    · rintro ⟨ws,yes⟩ b mem
      cases ws with
      | nil => cases yes
      | cons front tail =>
        obtain ⟨pair,later⟩ := Bool.and_eq_true_iff.mp yes
        rcases List.mem_cons.mp mem with rfl|remaining
        · have checked := eq_of_beq pair
          by_cases eq : a.2 = b.2
          · have strong : checkRawPair s a.1 b.1 front = some true := by simpa [eq] using checked
            exact ⟨fun _ => (exact_raw_pair_true450 ..).mp ⟨front,strong⟩,fun _ => eq⟩
          · have differs : (a.2 == b.2) = false := by
              cases result : (a.2 == b.2)
              · rfl
              · exact (eq (eq_of_beq result)).elim
            rw [differs] at checked
            have strong : checkRawPair s a.1 b.1 front = some false := checked
            exact ⟨fun h => (eq h).elim,fun h => ((exact_raw_pair_false450 ..).mp ⟨front,strong⟩ h).elim⟩
        · exact ih.mp ⟨tail,later⟩ b remaining
    · intro all
      have firstExact := all first List.mem_cons_self
      have restOK : ClassRow s a rest := fun b bt => all b (List.mem_cons_of_mem _ bt)
      obtain ⟨tail,exactTail⟩ := ih.mpr restOK
      by_cases eq : a.2 = first.2
      · obtain ⟨front,exactFront⟩ := (exact_raw_pair_true450 ..).mpr (firstExact.mp eq)
        exact ⟨front::tail,by simp [readClassRow,eq,exactFront,exactTail]⟩
      · obtain ⟨front,exactFront⟩ := (exact_raw_pair_false450 ..).mpr (fun same => eq (firstExact.mpr same))
        exact ⟨front::tail,by simp [readClassRow,eq,exactFront,exactTail]⟩

def RawMatrix (s : Raw) (all rows : List Labeled) : Prop :=
  ∀ a ∈ rows, ClassRow s a all

def readRawMatrix (s : Raw) (all : List Labeled) : List Labeled → List (List ExactPairWire) → Bool
  | [],[] => true
  | a::as,w::ws => readClassRow s a all w && readRawMatrix s all as ws
  | _,_ => false

theorem all_raw_classes_have_exact_finite_matrix450 (s : Raw) (all rows : List Labeled) :
    (∃ ws, readRawMatrix s all rows ws = true) ↔ RawMatrix s all rows := by
  induction rows with
  | nil => exact ⟨fun _ a h => (List.not_mem_nil h).elim,fun _ => ⟨[],rfl⟩⟩
  | cons first rest ih =>
    constructor
    · rintro ⟨ws,yes⟩ a mem
      cases ws with
      | nil => cases yes
      | cons front tail =>
        obtain ⟨pair,later⟩ := Bool.and_eq_true_iff.mp yes
        rcases List.mem_cons.mp mem with rfl|remaining
        · exact (one_raw_matrix_row_has_exact_finite_certificate450 ..).mp ⟨front,pair⟩
        · exact ih.mp ⟨tail,later⟩ a remaining
    · intro exactAll
      obtain ⟨front,good⟩ := (one_raw_matrix_row_has_exact_finite_certificate450 ..).mpr
        (exactAll first List.mem_cons_self)
      obtain ⟨tail,valid⟩ := ih.mpr (fun a inside => exactAll a (List.mem_cons_of_mem _ inside))
      exact ⟨front::tail,Bool.and_eq_true_iff.mpr ⟨good,valid⟩⟩

theorem finite_whole_raw_class_table450 (s : Raw) (pts : List RolePoint) :
    ∃ labeled : List Labeled,
      labeled.map Prod.fst = pts ∧
      RawMatrix s labeled labeled ∧ ∃ ws, readRawMatrix s labeled labeled ws = true := by
  let labeled := pts.map fun p => (p,classKey s pts p)
  have exactAll : RawMatrix s labeled labeled := by
    intro a included b also
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp included
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp also
    exact key_reflects_raw_pair450 hy
  exact ⟨labeled,by simp [labeled,List.map_map,Function.comp_def],exactAll,
    (all_raw_classes_have_exact_finite_matrix450 ..).mpr exactAll⟩

end Yulang.GeneralDeclarativeI65.I72.WhereSites450.OriginalCohorts451
