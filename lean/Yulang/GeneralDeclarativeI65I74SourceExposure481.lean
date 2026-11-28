import Yulang.GeneralDeclarativeI65I74AliasClassDescription472
import Yulang.GeneralDeclarativeI65I74EventFootprintSound478
import Yulang.GeneralDeclarativeInlineTrace331

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.SourceExposure481
open GeneralDeclarativeHead320 (Equation)
private abbrev RawState := GeneralDeclarativeHead320.State

open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeInlineTrace331 (Read)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open ObservationAliasHead472 (Catalogue checkedAlias checked_alias_really_links_old_names)
open ObservationRawAlias471 (complete_finite_old_alias_class_exists checked_class_is_exact_for_every_name)
open InputCoordinates475 (SourceIndexPair478)

abbrev authoredView (s : RawState) (table : Table) : RawState :=
  ⟨s.normal,table.authored⟩

def notBinder : Expr → Bool
  | .variable _ => false
  | _ => true

theorem notBinder_exact (code : Expr) : notBinder code = true ↔ ∀ n, code ≠ .variable n := by
  cases code <;> simp [notBinder]

structure ExposureWire where
  ordinals : SourceIndexPair478
  aliasData : Catalogue

def readExposure (s : RawState) (table : Table) (site : Nat) (code : Expr)
    (w : ExposureWire) : Option Equation := do
  let raw ← s.equations[w.ordinals.raw]?
  let author ← table.authored[w.ordinals.author]?
  if notBinder code = true ∧ raw = author ∧
      checkedAlias (authoredView s table) w.aliasData site raw.left = true then
    some raw
  else none

def ExactExposure (s : RawState) (table : Table) (site : Nat) (code : Expr)
    (indices : SourceIndexPair478) (row : Equation) : Prop :=
  s.equations[indices.raw]? = some row ∧ table.authored[indices.author]? = some row ∧
    (∀ n, code ≠ .variable n) ∧ GeneralDeclarativeLowerKnown321.Alias (authoredView s table) site row.left

theorem exposure_read_reflects_literal_origin (s : RawState) (table : Table) (site : Nat)
    (code : Expr) (w : ExposureWire) (row : Equation)
    (out : readExposure s table site code w = some row) :
    ExactExposure s table site code w.ordinals row := by
  unfold readExposure at out
  cases raw : s.equations[w.ordinals.raw]? with
  | none => simp [raw,bind,Option.bind] at out
  | some found =>
    cases source : table.authored[w.ordinals.author]? with
    | none => simp [raw,source,bind,Option.bind] at out
    | some authored =>
      simp only [raw,source,bind,Option.bind] at out
      split at out
      · rename_i good
        have exactRow := Option.some.inj out
        subst row
        exact ⟨raw,good.2.1 ▸ source,(notBinder_exact _).mp good.1,
          checked_alias_really_links_old_names good.2.2⟩
      · cases out

theorem literal_origin_reifies_a_checked_exposure (s : RawState) (table : Table) (site : Nat)
    (code : Expr) (indices : SourceIndexPair478) (row : Equation)
    (exactAt : ExactExposure s table site code indices row) :
    ∃ w : ExposureWire, w.ordinals = indices ∧ readExposure s table site code w = some row := by
  obtain ⟨raw,source,openCode,same⟩ := exactAt
  obtain ⟨w,good⟩ := complete_finite_old_alias_class_exists (authoredView s table) site
  have found := (checked_class_is_exact_for_every_name good row.left).mpr same
  let wire : ExposureWire := ⟨indices,[(site,w)]⟩
  refine ⟨wire,rfl,?_⟩
  simp [wire,readExposure,raw,source,bind,Option.bind,(notBinder_exact _).mpr openCode,
    checkedAlias,good,found]

theorem one_source_exposure_reads_in_the_same_authored_view
    {s : RawState} {table : Table} {site : Nat} {code : Expr} {w : ExposureWire}
    {row : Equation} {mode} {uses}
    (opened : readExposure s table site code w = some row)
    (next : Read (authoredView s table) mode row.right code uses) :
    Read (authoredView s table) mode (.variable site) code uses := by
  obtain ⟨_,source,openCode,same⟩ := exposure_read_reflects_literal_origin _ _ _ _ _ _ opened
  exact .expose openCode same (List.mem_of_getElem? source) next

theorem every_independent_authored_alias_exposure_has_finite_index_data
    {s : RawState} {table : Table} (linked : Attached s table) {site : Nat}
    {code : Expr} {row : Equation} (source : row ∈ table.authored)
    (openCode : ∀ n, code ≠ .variable n)
    (same : GeneralDeclarativeLowerKnown321.Alias (authoredView s table) site row.left) :
    ∃ w : ExposureWire, readExposure s table site code w = some row := by
  obtain ⟨a,atAuthor⟩ := List.mem_iff_getElem?.mp source
  obtain ⟨r,atRaw⟩ := List.mem_iff_getElem?.mp (linked.authored source)
  obtain ⟨w,_,run⟩ := literal_origin_reifies_a_checked_exposure s table site code ⟨r,a⟩ row
    ⟨atRaw,atAuthor,openCode,same⟩
  exact ⟨w,run⟩

/-- Records only consecutive applications of the existing source-variable
exposure rule. A successful trail is not an authority to navigate any
constructor child or inspect an unvisited source location. -/
inductive ExactExposureTrail (s : RawState) (table : Table) (code : Expr) :
    Expr → List (SourceIndexPair478 × Equation) → Expr → Prop where
  | done : ExactExposureTrail s table code input [] input
  | cons : ExactExposure s table name code index row →
      ExactExposureTrail s table code row.right rest result →
      ExactExposureTrail s table code (.variable name) ((index,row)::rest) result

def readExposureTrail (s : RawState) (table : Table) (code : Expr) :
    Expr → List ExposureWire → Option (List (SourceIndexPair478 × Equation) × Expr)
  | input,[] => some ([],input)
  | .variable site,w::tail => do
      let row ← readExposure s table site code w
      let (checked,result) ← readExposureTrail s table code row.right tail
      some ((w.ordinals,row)::checked,result)
  | _,_ => none

theorem exposure_trail_replays_the_exact_ordinal_row_sequence
    (s : RawState) (table : Table) (code input : Expr) (ws : List ExposureWire)
    (reads : List (SourceIndexPair478 × Equation)) (result : Expr)
    (ok : readExposureTrail s table code input ws = some (reads,result)) :
    ExactExposureTrail s table code input reads result ∧ reads.map Prod.fst = ws.map (·.ordinals) := by
  induction ws generalizing input reads result with
  | nil =>
    simp only [readExposureTrail, Option.some.injEq, Prod.mk.injEq] at ok
    obtain ⟨rfl,rfl⟩ := ok
    exact ⟨.done,rfl⟩
  | cons w ws ih =>
    cases input <;> try contradiction
    case «variable» site =>
      unfold readExposureTrail at ok
      cases head : readExposure s table site code w with
      | none => simp [head,bind,Option.bind] at ok
      | some row =>
        cases later : readExposureTrail s table code row.right ws with
        | none => simp [head,later,bind,Option.bind] at ok
        | some output =>
          obtain ⟨rows,last⟩ := output
          simp only [head,later,bind,Option.bind,Option.some.injEq,Prod.mk.injEq] at ok
          obtain ⟨rfl,rfl⟩ := ok
          obtain ⟨tail,same⟩ := ih _ _ _ later
          exact ⟨.cons (exposure_read_reflects_literal_origin s table site code w row head) tail,
            by simp [same]⟩

theorem exact_exposure_trail_reifies_finite_data
    {s : RawState} {table : Table} {code input reads result}
    (logical : ExactExposureTrail s table code input reads result) :
    ∃ ws, readExposureTrail s table code input ws = some (reads,result) := by
  induction logical with
  | done => exact ⟨[],rfl⟩
  | @cons name index row rest result exactAt studied ih =>
    obtain ⟨w,same,here⟩ := literal_origin_reifies_a_checked_exposure s table name code index row exactAt
    obtain ⟨ws,later⟩ := ih
    exact ⟨w::ws,by simp [readExposureTrail,here,later,same,bind,Option.bind]⟩

theorem every_read_exposure_trail_precomposes_existing_authored_read
    {s : RawState} {table : Table} {code input reads result mode uses}
    (logical : ExactExposureTrail s table code input reads result)
    (read : Read (authoredView s table) mode result code uses) :
    Read (authoredView s table) mode input code uses := by
  induction logical with
  | done => exact read
  | cons one _ ih =>
    exact .expose one.2.2.1 one.2.2.2 (List.mem_of_getElem? one.2.1) (ih read)
end Yulang.GeneralDeclarativeI65.I72.SourceExposure481
