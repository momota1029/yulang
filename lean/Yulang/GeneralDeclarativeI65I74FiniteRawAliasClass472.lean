import Yulang.GeneralDeclarativeI65I74SplitEscapeFinite446
import Yulang.GeneralDeclarativeI65I74WhereCycleWire450

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ObservationRawAlias471
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeLowerKnown321 (alias_refl alias_symm)
open GeneralDeclarativeWitnessRank350 (rank atom)
open List410 (ExactEscapeWire aliasRow colour)
open SplitEscape446
open GeneralNominalCenteredHeadMatExpressions (Expr)
private abbrev Raw := GeneralDeclarativeHead320.State
private abbrev Al := GeneralDeclarativeLowerKnown321.Alias

/-- A separate alias-side cut. It has no raw structural graph cycle guard;
its input to observation extraction merely says which names can coincide
via existing bounds and flats. Regular equality is still separate. -/
structure RefutesAlias (s : Raw) (a b : Nat) (wire : ExactEscapeWire) : Prop where
  order : ∀ u v, Bound s.normal u v → rank wire.ranks u ≤ rank wire.ranks v
  side : ∀ row ∈ s.equations, ∀ n, row.right = .variable n → wire.side row.left = wire.side n
  cut : wire.side a ≠ wire.side b

theorem checked_side_is_constant_on_alias {s a b wire u v} (h : RefutesAlias s a b wire)
    (eq : Al s u v) : wire.side u = wire.side v := by
  induction eq with
  | bounds f l => exact congrArg (colour wire.palette) (Nat.le_antisymm (h.order _ _ f) (h.order _ _ l))
  | forward hit => exact h.side _ hit _ rfl
  | backward hit => exact (h.side _ hit _ rfl).symm
  | trans _ _ one two => exact one.trans two

def checkRefutesAlias (s : Raw) (a b : Nat) (w : ExactEscapeWire) : Bool :=
  s.normal.ordinary.all (atom (rank w.ranks)) &&
  s.normal.intervals.all (fun e => decide (rank w.ranks e.1 ≤ rank w.ranks e.2)) &&
  s.equations.all (aliasRow w.side) && decide (w.side a ≠ w.side b)

theorem side_check_exact {s a b w} :
    checkRefutesAlias s a b w = true ↔ RefutesAlias s a b w := by
  constructor
  · intro yes
    obtain ⟨⟨⟨checks,intervals⟩,flats⟩,diff⟩ :=
      (Bool.and_eq_true_iff.mp (show checkRefutesAlias s a b w = true from yes)).imp
        (fun ab => (Bool.and_eq_true_iff.mp ab).imp (Bool.and_eq_true_iff.mp) id) id
    refine ⟨?_,?_,of_decide_eq_true diff⟩
    · intro a b typed
      induction typed with
      | interval goes => exact of_decide_eq_true (List.all_eq_true.mp intervals _ goes)
      | constraint goes => exact of_decide_eq_true (List.all_eq_true.mp checks _ goes)
      | refl => exact Nat.le_refl _
      | trans _ _ l r => exact Nat.le_trans l r
    · intro e stored n isVar
      have checked := List.all_eq_true.mp flats e stored
      unfold aliasRow at checked
      rw [isVar] at checked
      exact of_decide_eq_true checked
  · intro h
    simp only [checkRefutesAlias,Bool.and_eq_true]
    refine ⟨⟨⟨?_,?_⟩,?_⟩,decide_eq_true h.cut⟩
    · apply List.all_eq_true.mpr
      intro constraint raw
      cases constraint with
      | rowLe => rfl
      | tyLe lo hi =>
        cases lo <;> cases hi <;>
          first | rfl | exact decide_eq_true (h.order _ _ (.constraint raw))
    · exact List.all_eq_true.mpr (fun _ row => decide_eq_true (h.order _ _ (.interval row)))
    · apply List.all_eq_true.mpr
      intro e stored
      unfold aliasRow
      split
      · rename_i n eq
        exact decide_eq_true (h.side _ stored _ eq)
      · rfl

def limit (s : Raw) (a b : Nat) : Nat := max (rawLimit s a) (b + 1)

theorem limit_support (s : Raw) (a b : Nat) : BoundSupport s.normal (limit s a b) := by
  have old := bound_support_from_actual_rows446 s a
  constructor
  · intro x y edge
    exact ⟨Nat.lt_of_lt_of_le (old.1 _ _ edge).1 (Nat.le_max_left ..),
      Nat.lt_of_lt_of_le (old.1 _ _ edge).2 (Nat.le_max_left ..)⟩
  · intro x y edge
    exact ⟨Nat.lt_of_lt_of_le (old.2 _ _ edge).1 (Nat.le_max_left ..),
      Nat.lt_of_lt_of_le (old.2 _ _ edge).2 (Nat.le_max_left ..)⟩

noncomputable def aliasColour (s : Raw) (a x : Nat) : Nat :=
  @ite Nat (Al s a x) (Classical.propDecidable _) 0 1

theorem alias_colour_constant {s a u v} (near : Al s u v) :
    aliasColour s a u = aliasColour s a v := by
  classical
  have rel : Al s a u ↔ Al s a v :=
    ⟨fun ty => .trans ty near,fun ty => .trans ty (alias_symm near)⟩
  unfold aliasColour
  rw [propext rel]

noncomputable def classColour (s : Raw) (a size k : Nat) : Nat := by
  classical
  exact if seen : ∃ v : Fin size, rank (boundGrades s.normal size) v.val = k then
    aliasColour s a (Classical.choose seen).val else 2

noncomputable def reifySide (s : Raw) (a b : Nat) : ExactEscapeWire :=
  let size := limit s a b
  ⟨boundGrades s.normal size,List.ofFn fun i : Fin (2 ^ size + 1) => classColour s a size i.val⟩

theorem reified_side_agrees_on_actual_names {s a b n} (inside : n < limit s a b) :
    (reifySide s a b).side n = aliasColour s a n := by
  classical
  let size := limit s a b
  let grade := rank (boundGrades s.normal size) n
  have fits : grade < 2 ^ size + 1 := active_grade_bounded446 inside
  have seen : ∃ i : Fin size, rank (boundGrades s.normal size) i.val = grade := ⟨⟨n,inside⟩,rfl⟩
  change colour (List.ofFn fun i : Fin (2 ^ size + 1) => classColour s a size i.val) grade = _
  unfold colour
  simp only [List.getElem?_ofFn,dite_eq_left fits,Option.getD_some]
  change classColour s a size grade = _
  unfold classColour
  rw [dite_eq_left seen]
  have pair := equal_active_grades_are_exact_SCC446 (Classical.choose seen).isLt inside
    (Classical.choose_spec seen)
  exact alias_colour_constant (.bounds pair.1 pair.2)

theorem raw_no_alias_iff_finite_side_cut {s : Raw} {a b : Nat} :
    (∃ w, checkRefutesAlias s a b w = true) ↔ ¬Al s a b := by
  constructor
  · rintro ⟨w,yes⟩ near
    have side := side_check_exact.mp yes
    exact side.cut (checked_side_is_constant_on_alias side near)
  · intro distinct
    classical
    refine ⟨reifySide s a b,side_check_exact.mpr ⟨?_,?_,?_⟩⟩
    · exact fun u v step => bound_grade_monotone446 (limit_support s a b) step
    · intro e stored n shape
      have l : e.left < limit s a b :=
        Nat.lt_of_lt_of_le (write_name_inside446 (site := a) stored List.mem_cons_self)
          (Nat.le_max_left ..)
      have rr : n < limit s a b := by
        apply Nat.lt_of_lt_of_le (write_name_inside446 (site := a) stored _) (Nat.le_max_left ..)
        exact List.mem_cons_of_mem _ (List.mem_append_left _ (by simp [flatEnd,shape]))
      rw [reified_side_agrees_on_actual_names l,reified_side_agrees_on_actual_names rr]
      exact alias_colour_constant (.forward (by simpa [←shape] using stored))
    · have l : a < limit s a b := Nat.lt_of_lt_of_le (root_inside446 s a) (Nat.le_max_left ..)
      have r : b < limit s a b := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right ..)
      rw [reified_side_agrees_on_actual_names l,reified_side_agrees_on_actual_names r]
      simp [aliasColour,alias_refl,distinct]

theorem nontrivial_alias_target_lies_in_finite_support {s : Raw} {a b : Nat}
    (alias : Al s a b) (different : a ≠ b) (root : Nat) :
    b < rawLimit s root := by
  induction alias with
  | bounds first _ =>
    have ho := nontrivial_bound_inside_support446 (bound_support_from_actual_rows446 s root) first
    exact (ho.resolve_left different).2
  | forward stored =>
    exact write_name_inside446 stored (List.mem_cons_of_mem _ (List.mem_append_left _ (by simp [flatEnd])))
  | backward stored =>
    exact write_name_inside446 stored List.mem_cons_self
  | @trans start via finish _ _ first second =>
    by_cases close : via = finish
    · have seen := first (different ∘ (·.trans close))
      simpa [close] using seen
    · exact second close

def checkIsolatedName (s : Raw) (site : Nat) (w : ExactEscapeWire) : Bool :=
  (List.range (rawLimit s site)).all fun b =>
    if b = site then true else checkRefutesAlias s site b w

theorem raw_isolated_name_iff_one_finite_side_table {s : Raw} {site : Nat} :
    (∃ w, checkIsolatedName s site w = true) ↔ ∀ b, Al s site b → site = b := by
  constructor
  · rintro ⟨w,passed⟩ b alias
    by_cases same : site = b
    · exact same
    · have seen := nontrivial_alias_target_lies_in_finite_support alias same site
      have read := List.all_eq_true.mp passed b (List.mem_range.mpr seen)
      have guard : checkRefutesAlias s site b w = true := by
        simpa [Ne.symm same] using read
      exact ((raw_no_alias_iff_finite_side_cut.mp ⟨w,guard⟩) alias).elim
  · intro original
    classical
    refine ⟨reifySide s site site,List.all_eq_true.mpr ?_⟩
    intro other present
    by_cases same : other = site
    · simp [same]
    · simp only [ite_eq_right same]
      have otherIn : other < limit s site site :=
        Nat.lt_of_lt_of_le (List.mem_range.mp present) (Nat.le_max_left ..)
      have noAlias : ¬Al s site other := fun hit => same (original other hit).symm
      apply side_check_exact.mpr
      refine ⟨fun u v step => bound_grade_monotone446 (limit_support s site site) step,?_,?_⟩
      · intro row present n shape
        have l : row.left < limit s site site :=
          Nat.lt_of_lt_of_le (write_name_inside446 (site := site) present List.mem_cons_self) (Nat.le_max_left ..)
        have rr : n < limit s site site := by
          apply Nat.lt_of_lt_of_le (write_name_inside446 (site := site) present _) (Nat.le_max_left ..)
          exact List.mem_cons_of_mem _ (List.mem_append_left _ (by simp [flatEnd,shape]))
        rw [reified_side_agrees_on_actual_names l,reified_side_agrees_on_actual_names rr]
        exact alias_colour_constant (.forward (by simpa [←shape] using present))
      · have l : site < limit s site site :=
          Nat.lt_of_lt_of_le (root_inside446 s site) (Nat.le_max_left ..)
        rw [reified_side_agrees_on_actual_names l,reified_side_agrees_on_actual_names otherIn]
        simp [aliasColour,alias_refl,noAlias]

private def exampleRaw : Raw := ⟨⟨[],[(7,8),(8,7)]⟩,[⟨7,.variable 8⟩]⟩
private def sideWire : ExactEscapeWire :=
  ⟨(List.range 10).map fun n => if n = 4 then 1 else 0,[1,0]⟩

theorem actual_unrelated_nontrivial_alias_does_not_block_a_local_owner :
    checkIsolatedName exampleRaw 4 sideWire = true ∧
    Al exampleRaw 7 8 ∧
    ¬∃ w, checkIsolatedName exampleRaw 7 w = true := by
  have alias : Al exampleRaw 7 8 := .forward (List.mem_cons_self)
  exact ⟨by decide +kernel,alias,fun no =>
    (by decide : 7 ≠ 8) ((raw_isolated_name_iff_one_finite_side_table.mp no) _ alias)⟩

end Yulang.GeneralDeclarativeI65.I72.ObservationRawAlias471
namespace Yulang.GeneralDeclarativeI65.I72.ObservationRawAlias471
open SplitEscape446 (boundAtomNames rawLimit rawNames cap mem_below_cap446 writeNames flatEnd)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeBounds319 (Bound)
open List410 (ExactEscapeWire)

def boundNames (attrs : GeneralDeclarativeWhere319.State) : List Nat :=
  attrs.ordinary.flatMap boundAtomNames ++ attrs.intervals.flatMap (fun i => [i.1,i.2])

def onlyFlatKeys (eq : Equation) : List Nat :=
  match eq.right with
  | .variable n => [eq.left,n]
  | _ => []

def aliasKeys (s : Raw) : List Nat := boundNames s.normal ++ s.equations.flatMap onlyFlatKeys

theorem nonidentity_bound_target_is_an_actual_key {s a b} (h : Bound s a b) (nonidentity : a ≠ b) :
    b ∈ boundNames s := by
  induction h with
  | interval given =>
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨_,given,List.mem_cons_of_mem _ List.mem_cons_self⟩)
  | constraint given =>
    exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨_,given,List.mem_cons_of_mem _ List.mem_cons_self⟩)
  | refl => exact (nonidentity rfl).elim
  | @trans start via finish _ _ first second =>
    by_cases close : via = finish
    · have seen := first (nonidentity ∘ (·.trans close))
      simpa [close] using seen
    · exact second close

theorem nonidentity_alias_target_is_an_actual_key {s a b} (h : Al s a b) (nonidentity : a ≠ b) :
    b ∈ aliasKeys s := by
  induction h with
  | bounds first _ =>
    exact List.mem_append_left _ (nonidentity_bound_target_is_an_actual_key first nonidentity)
  | forward stored =>
    exact List.mem_append_right _
      (List.mem_flatMap.mpr ⟨_,stored,List.mem_cons_of_mem _ List.mem_cons_self⟩)
  | backward stored =>
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨_,stored,List.mem_cons_self⟩)
  | @trans start via finish _ _ first second =>
    by_cases close : via = finish
    · have seen := first (nonidentity ∘ (·.trans close))
      simpa [close] using seen
    · exact second close

theorem each_alias_key_is_in_old_support {s : Raw} {root x : Nat} (key : x ∈ aliasKeys s) :
    x < rawLimit s root := by
  apply mem_below_cap446
  apply List.mem_cons_of_mem
  rcases List.mem_append.mp key with bound | flat
  · rcases List.mem_append.mp bound with atoms | interval
    · exact List.mem_append_left _ atoms
    · exact List.mem_append_right _ (List.mem_append_left _ interval)
  · obtain ⟨eq,atEq,within⟩ := List.mem_flatMap.mp flat
    apply List.mem_append_right _
    apply List.mem_append_right _
    apply List.mem_flatMap.mpr
    refine ⟨eq,atEq,?_⟩
    cases value : eq.right <;> simp [onlyFlatKeys,value] at within
    rcases within with first | fresh
    · exact first ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ (by simp [flatEnd,value,fresh]))

def isolatedByKeys (s : Raw) (site : Nat) (w : ExactEscapeWire) : Bool :=
  (aliasKeys s).all fun b => if b = site then true else checkRefutesAlias s site b w

theorem exact_isolation_needs_no_inactive_payload_names {s : Raw} {site : Nat} :
    (∃ w, isolatedByKeys s site w = true) ↔ ∀ b, Al s site b → site = b := by
  constructor
  · rintro ⟨w,pass⟩ b known
    by_cases same : site = b
    · exact same
    · have hit := List.all_eq_true.mp pass b (nonidentity_alias_target_is_an_actual_key known same)
      have checked : checkRefutesAlias s site b w = true := by simpa [Ne.symm same] using hit
      exact ((raw_no_alias_iff_finite_side_cut.mp ⟨w,checked⟩) known).elim
  · intro release
    obtain ⟨w,ok⟩ := raw_isolated_name_iff_one_finite_side_table.mpr release
    exact ⟨w,List.all_eq_true.mpr (fun _ present =>
      List.all_eq_true.mp ok _ (List.mem_range.mpr (each_alias_key_is_in_old_support present)))⟩

end Yulang.GeneralDeclarativeI65.I72.ObservationRawAlias471
namespace Yulang.GeneralDeclarativeI65.I72.ObservationRawAlias471
open GeneralDeclarativeWitnessCycle350 (Link checksLink link)
open WhereSites450 (alias_wire_from_actual_derivation450)
open List410 (ExactEscapeWire)
open GeneralDeclarativeLowerKnown321 (alias_refl)
open SplitEscape446

structure ClassWire where
  connected : List (Nat × Link)
  others : ExactEscapeWire

def connectedKeys (w : ClassWire) : List Nat := w.connected.map Prod.fst

def checkWholeClass (s : Raw) (site : Nat) (w : ClassWire) : Bool :=
  decide (site ∈ connectedKeys w) &&
  w.connected.all (fun pair => checksLink s site pair.1 pair.2) &&
  (aliasKeys s).all (fun slot =>
    if slot ∈ connectedKeys w then true else checkRefutesAlias s site slot w.others)

theorem checked_class_is_exact_for_every_name {s : Raw} {site} {w : ClassWire}
    (ok : checkWholeClass s site w = true) :
    ∀ b, b ∈ connectedKeys w ↔ Al s site b := by
  obtain ⟨⟨center,edges⟩,others⟩ :=
    (Bool.and_eq_true_iff.mp (show checkWholeClass s site w = true from ok)).imp Bool.and_eq_true_iff.mp id
  intro b
  constructor
  · intro listed
    obtain ⟨⟨i,trace⟩,stored,rfl⟩ := List.mem_map.mp listed
    exact link (List.all_eq_true.mp edges _ stored)
  · intro related
    by_cases entered : b ∈ connectedKeys w
    · exact entered
    · have notSelf : site ≠ b := by
        intro same
        subst b
        exact entered (of_decide_eq_true center)
      have actual := List.all_eq_true.mp others b (nonidentity_alias_target_is_an_actual_key related notSelf)
      have why : checkRefutesAlias s site b w.others = true := by simpa [entered] using actual
      exact ((raw_no_alias_iff_finite_side_cut.mp ⟨_,why⟩) related).elim

theorem separating_table_refutes_any_other_active_name {s : Raw} {site x}
    (found : x ∈ aliasKeys s) (apart : ¬Al s site x) :
    checkRefutesAlias s site x (reifySide s site site) = true := by
  classical
  apply side_check_exact.mpr
  refine ⟨fun u v step => bound_grade_monotone446 (limit_support s site site) step,?_,?_⟩
  · intro row stored n shape
    have l : row.left < limit s site site :=
      Nat.lt_of_lt_of_le (write_name_inside446 (site := site) stored List.mem_cons_self)
        (Nat.le_max_left ..)
    have rr : n < limit s site site := by
      apply Nat.lt_of_lt_of_le (write_name_inside446 (site := site) stored _) (Nat.le_max_left ..)
      exact List.mem_cons_of_mem _ (List.mem_append_left _ (by simp [flatEnd,shape]))
    rw [reified_side_agrees_on_actual_names l,reified_side_agrees_on_actual_names rr]
    exact alias_colour_constant (.forward (by simpa [←shape] using stored))
  · have l : site < limit s site site :=
      Nat.lt_of_lt_of_le (root_inside446 s site) (Nat.le_max_left ..)
    have other : x < limit s site site :=
      Nat.lt_of_lt_of_le (each_alias_key_is_in_old_support found) (Nat.le_max_left ..)
    rw [reified_side_agrees_on_actual_names l,reified_side_agrees_on_actual_names other]
    simp [aliasColour,alias_refl,apart]

theorem complete_finite_old_alias_class_exists (s : Raw) (site : Nat) :
    ∃ w, checkWholeClass s site w = true := by
  classical
  let keys := (site :: aliasKeys s).filter fun x => decide (Al s site x)
  have marked (i : Nat) (present : i ∈ keys) : Al s site i :=
    of_decide_eq_true (List.mem_filter.mp present).2
  let rows := keys.attach.map fun x =>
    (x.val,Classical.choose (alias_wire_from_actual_derivation450 (marked x.val x.property)))
  let w : ClassWire := ⟨rows,reifySide s site site⟩
  have literal : connectedKeys w = keys := by
    unfold connectedKeys w rows
    simp
  have checked (p : Nat × Link) (present : p ∈ rows) : checksLink s site p.1 p.2 = true := by
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp present
    exact Classical.choose_spec (alias_wire_from_actual_derivation450 (marked x.val x.property))
  refine ⟨w,?_⟩
  simp only [checkWholeClass,Bool.and_eq_true]
  refine ⟨⟨decide_eq_true (by rw [literal]; simp [keys,alias_refl]),
    List.all_eq_true.mpr checked⟩,List.all_eq_true.mpr ?_⟩
  intro x listed
  rw [literal]
  by_cases near : Al s site x
  · have admitted : x ∈ keys := by simp [keys,listed,near]
    simp [admitted]
  · have outside : x ∉ keys := fun stuck => near (marked _ stuck)
    rw [ite_eq_right outside]
    exact separating_table_refutes_any_other_active_name listed near

private def classExample : Raw :=
  ⟨⟨[],[(7,8),(8,7)]⟩,[⟨7,.variable 8⟩,⟨3,.variable 5⟩]⟩

private def proofFor7 : ExactEscapeWire :=
  ⟨(List.range 10).map (fun i => if i = 7 || i = 8 then 1 else 0),[1,0]⟩

theorem literal_class_checks_actual_links_and_rejects_omitted_member :
    checkWholeClass classExample 7 ⟨[(7,.same),(8,.forward 0)],proofFor7⟩ = true ∧
    checkWholeClass classExample 7 ⟨[(7,.same)],proofFor7⟩ = false ∧
    checkWholeClass classExample 7 ⟨[(7,.same),(8,.forward 0),(3,.same)],proofFor7⟩ = false := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

end Yulang.GeneralDeclarativeI65.I72.ObservationRawAlias471
