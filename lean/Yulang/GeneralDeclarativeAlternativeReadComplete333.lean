import Yulang.GeneralDeclarativeAlternativeSpineComplete333
import Yulang.GeneralDeclarativeAlternativeRead333

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeAlternativeReadComplete333
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeAlternativeView333 (Offer Index Covers exact_offer)
open GeneralDeclarativeAlternativeSpine333 (LiteralAt peel_keeps literals)
open GeneralDeclarativeAlternativeSpineComplete333 (literal_plan)
open GeneralDeclarativeAlternativeRead333 (Result ArgResult FieldResult read readArgs readFields
  structured expansions nonBinder_complete normalized recordChoices tailOK Reader FieldReader)
open GeneralDeclarativeInlineTrace331 (Read Args Fields TailCode)
open GeneralDeclarativeInlineSpine331 (Closed)
open GeneralDeclarativeNestedTail332 (peel)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeOrderedRecord326 (order exact_order)
open GeneralDeclarativeRecordMaterial330 (tailExpr)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open CommonRoleCanonicalRows (Row normalize normalize_unique)

open GeneralDeclarativeAlternativeNeeds333 (Need Filled Planned Eventually eventually_one
  eventually_step eventually_pair finiteIndex)

abbrev AllRead (src : Index s) (h : Read s mode raw wanted sites) :=
  Eventually (fun n => (⟨sites,h⟩ : Result s mode raw wanted) ∈ read src n mode raw wanted)
abbrev AllArgs (src : Index s) (h : Args s mode raw wanted sites) :=
  Eventually (fun n => (⟨sites,h⟩ : ArgResult s mode raw wanted) ∈ readArgs src n mode raw wanted)
abbrev AllFields (src : Index s) (h : Fields s mode raw wanted sites) :=
  Eventually (fun n => (⟨sites,h⟩ : FieldResult s mode raw wanted) ∈ readFields src n mode raw wanted)

theorem field_labels {s : State} (known : Fields s mode raw written sites) :
    raw.map Prod.fst = written.map Prod.fst := by
  induction written generalizing raw sites with
  | nil => cases known; rfl
  | cons a as ih =>
    cases known with
    | cons _ rest => simp [ih rest]

theorem correct_labels {s : State} (selected : order (normalize row) keys = some chosen)
    (known : Fields s mode chosen written sites) : written.map Prod.fst = keys :=
  (field_labels known).symm.trans ((exact_order (normalize_unique row) selected).1)

theorem tail_shape (h : TailCode tail) : ∀ k a b, tail ≠ .record k a b := by
  cases h <;> intro _ _ _ bad <;> cases bad

theorem tail_present (h : TailCode tail) : tailOK tail = some ⟨h⟩ := by cases h <;> rfl

theorem exposed_in {s : State} {src : Index s}
    (safe : ∀ n, wanted ≠ .variable n) (route : Alias s n owner)
    (stored : (⟨owner,body⟩ : Equation) ∈ s.equations)
    (chosen : (⟨owner,body,route,stored⟩ : Offer s n) ∈ src n)
    {hit : Result s mode body wanted} (sub : hit ∈ read src fuel mode body wanted) :
    (⟨hit.val,.expose safe route stored hit.property⟩ : Result s mode (.variable n) wanted) ∈
      read src (fuel+1) mode (.variable n) wanted := by
  apply List.mem_append_right
  simp only [expansions,dite_eq_left (nonBinder_complete safe)]
  exact List.mem_flatMap.mpr ⟨⟨owner,body,route,stored⟩,chosen,List.mem_map.mpr ⟨hit,sub,rfl⟩⟩

theorem replace_plan {src : Index s} (next : Reader s) (fields : FieldReader s)
    (a b : Row Expr × Expr) (same : a = b)
    (old : withTail a.1 a.2 = target) (now : withTail b.1 b.2 = target) :
    recordChoices src fuel next fields mode raw a old =
      recordChoices src fuel next fields mode raw b now := by
  cases same
  rfl

theorem record_in {s : State} {src : Index s} {mode : GeneralNominalMaterialization.Mode}
    (rawShape : Closed s raw actual terminal) (keys : List Nat) (written : Row Expr)
    (unique : keys.Nodup) (someKeys : keys ≠ [])
    (selects : order (normalize actual) keys = some picked)
    (writtenKeys : written.map Prod.fst = keys) (ending : TailCode tail)
    {a : FieldResult s mode picked written} {b : Result s mode (tailExpr actual keys terminal) tail}
    (seen : (⟨(actual,terminal),rawShape⟩ : LiteralAt s raw) ∈ literals src fuel raw)
    (one : a ∈ readFields src fuel mode picked written)
    (two : b ∈ read src fuel mode (tailExpr actual keys terminal) tail) :
    (⟨a.val++b.val,.record rawShape unique someKeys selects a.property ending b.property⟩ :
      Result s mode raw (withTail written tail)) ∈ read src (fuel+1) mode raw (withTail written tail) := by
  subst keys
  cases written with
  | nil => exact (someKeys rfl).elim
  | cons entry later =>
    obtain ⟨k,v⟩ := entry
    apply List.mem_append_left
    have pretty : peel (withTail ((k,v)::later) tail) = ((k,v)::later,tail) :=
      peel_keeps tail (tail_shape ending) _
    simp only [withTail] at pretty ⊢
    simp only [structured]
    rw [replace_plan (read src fuel) (readFields src fuel) _ _ pretty _
      (rfl : withTail ((k,v)::later) tail = Expr.record k v (withTail later tail))]
    simp only [recordChoices,dite_eq_left (And.intro unique someKeys),tail_present ending]
    refine List.mem_flatMap.mpr ⟨⟨(actual,terminal),rawShape⟩,seen,?_⟩
    dsimp only
    split
    · rename_i absent
      rw [selects] at absent
      cases absent
    · rename_i actual rowPrinted
      cases Option.some.inj (rowPrinted.symm.trans selects)
      exact List.mem_flatMap.mpr ⟨a,one,List.mem_map.mpr ⟨b,two,rfl⟩⟩


/-- Completeness for each independently derived InlineTrace (including
mixed per-occurrence spelling choices), assuming all its authorized
rows can be found. The returned depth is a witness bound for this
finite positive read, not for solver execution or rejection. -/
theorem read_plan {s : State} (h : Read s mode raw wanted used) :
    Planned (fun src => AllRead src h) := by
  refine Read.rec
    (motive_1 := fun _ _ _ _ h => Planned (fun src => AllRead src h))
    (motive_2 := fun _ _ _ _ h => Planned (fun src => AllArgs src h))
    (motive_3 := fun _ _ _ _ h => Planned (fun src => AllFields src h))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro mode raw binder
    apply Planned.pure
    intro src
    apply eventually_one
    intro n
    apply List.mem_append_left
    exact List.mem_cons_self
  · intro target site owner body used mode safe link backed nested ih
    let edge : Need s := ⟨site,⟨owner,body,link,backed⟩⟩
    apply ih.add edge
    intro src chosen known
    apply eventually_step known
    intro k fits
    exact exposed_in safe link backed chosen fits
  · intro mode raw targets used tag h ih
    apply ih.map
    intro src known
    apply eventually_step known
    intro fuel seen
    apply List.mem_append_left
    simp only [structured]
    exact List.mem_map.mpr ⟨⟨used,h⟩,seen,rfl⟩
  · intro raw targets used mode tag h ih
    apply ih.map
    intro src known
    apply eventually_step known
    intro fuel seen
    apply List.mem_append_left
    simp only [structured]
    exact List.mem_map.mpr ⟨⟨used,h⟩,seen,rfl⟩
  · intro mode raw target used tag h ih
    apply ih.map
    intro src known
    apply eventually_step known
    intro fuel seen
    apply List.mem_append_left
    simp only [structured]
    exact List.mem_map.mpr ⟨⟨used,h⟩,seen,rfl⟩
  · intro mode a x b y first last h j ih jh
    apply (ih.both jh).map
    intro src known
    apply eventually_step (eventually_pair known.1 known.2)
    intro fuel hits
    apply List.mem_append_left
    exact List.mem_flatMap.mpr ⟨_,hits.1,List.mem_map.mpr ⟨_,hits.2,rfl⟩⟩
  · intro input actual stop keys picked mode written first tail last
      rawRead unique someKeys orders fields terminal tailRead ih jh
    apply ((literal_plan rawRead).both (ih.both jh)).map
    intro src avail
    have available : Eventually (fun f =>
        (⟨(actual,stop),rawRead⟩ : LiteralAt s input) ∈ literals src f input) := by
      obtain ⟨b,here⟩ := avail.1
      refine ⟨b,fun f enough => ?_⟩
      obtain ⟨a,known,same⟩ := here f enough
      cases (Subtype.ext same : a = ⟨(actual,stop),rawRead⟩)
      exact known
    apply eventually_step (eventually_pair available (eventually_pair avail.2.1 avail.2.2))
    intro fuel hits
    exact record_in rawRead keys written unique someKeys orders (correct_labels orders fields)
      terminal hits.1 hits.2.1 hits.2.2
  · intro mode
    apply Planned.pure
    intro src
    apply eventually_one
    intro k
    exact List.mem_cons_self
  · intro mode a b first ra rb rest one two ih jh
    apply (ih.both jh).map
    intro src known
    apply eventually_step (eventually_pair known.1 known.2)
    intro fuel hits
    exact List.mem_flatMap.mpr ⟨_,hits.1,List.mem_map.mpr ⟨_,hits.2,rfl⟩⟩
  · intro mode
    apply Planned.pure
    intro src
    apply eventually_one
    intro k
    exact List.mem_cons_self
  · intro mode a b first ra rb rest label one two ih jh
    apply (ih.both jh).map
    intro src known
    apply eventually_step (eventually_pair known.1 known.2)
    intro fuel hits
    simp only [readFields]
    exact List.mem_flatMap.mpr ⟨_,hits.1,List.mem_map.mpr ⟨_,hits.2,rfl⟩⟩


theorem read_complete {s : State} {src : Index s} (covers : Covers src)
    (h : Read s mode raw wanted used) : AllRead src h := (read_plan h).from_cover covers

theorem normalized_plan {s : State}
    (printed : translate c i (GeneralDeclarationPatterns.normalize pat) = some code)
    (witness : Read s mode raw code used) :
    Planned (fun src : Index s => Eventually (fun f => used ∈ normalized src f c i mode raw pat)) := by
  apply (read_plan witness).map
  intro src available
  obtain ⟨depth,arrives⟩ := available
  refine ⟨depth,fun f enough => ?_⟩
  change used ∈ normalized src f c i mode raw pat
  unfold normalized
  rw [printed]
  exact List.mem_map.mpr ⟨⟨used,witness⟩,arrives f enough,rfl⟩

/-- Every independently justified positive normalized read has a
finite, sufficient, ordinary source table. No model or universal
alias closure is part of the existence statement. -/
theorem normalized_finite {s : State}
    (printed : translate c i (GeneralDeclarationPatterns.normalize pat) = some code)
    (witness : Read s mode raw code used) :
    ∃ needed : List (Need s), Eventually (fun f =>
      used ∈ normalized (finiteIndex needed) f c i mode raw pat) :=
  (normalized_plan printed witness).finite

theorem normalized_complete {s : State} {src : Index s} (covers : Covers src)
    (printed : translate c i (GeneralDeclarationPatterns.normalize pat) = some code)
    (witness : Read s mode raw code used) :
    Eventually (fun f => used ∈ normalized src f c i mode raw pat) :=
  (normalized_plan printed witness).from_cover covers

end Yulang.GeneralDeclarativeAlternativeReadComplete333
