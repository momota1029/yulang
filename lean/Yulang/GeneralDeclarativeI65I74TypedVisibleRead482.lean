import Yulang.GeneralDeclarativeI65I74AuthoredFullRead482
import Yulang.GeneralDeclarativeI65I74SourceExposureMeaning481
import Yulang.GeneralDeclarativeInlineFootprint331

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWitnessOrigins350 (Table Attached support visible_iff)
open GeneralDeclarativeOrigins321 (restriction)
open GeneralDeclarativeInlineTrace331 (Read)
open GeneralDeclarativeInlineFootprint331 (trace)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalMaterialization (Mode)
open GeneralDeclarativeTermWalk322 (Occurrence)
private abbrev Before := GeneralDeclarativeHead320.State

/-- Internal read view only. Original authority remains in the attached
table; a completed row is not turned into a source-origin fact. -/
def visibleReadView (t : Table) : Table := ⟨GeneralDeclarativeWitnessOrigins350.visible t,[],[]⟩

theorem visible_read_view_reflects_existing_authority {s : Before} {t : Table}
    (auth : Attached s t) (row : Equation) :
    row ∈ (authoredView s (visibleReadView t)).equations ↔
    row ∈ (restriction (support auth)).equations :=
  (visible_iff auth row).symm

def visible_projected_rows_are_existing_physical_equations {s : Before} {t : Table}
    (auth : Attached s t) : Attached s (visibleReadView t) := by
  refine ⟨?_,fun _ absent => False.elim (List.not_mem_nil absent)⟩
  intro row member
  change row ∈ t.authored ++ (t.produced.filter (fun q => t.released.contains q.2)).map Prod.fst at member
  rcases List.mem_append.mp member with authored | finished
  · exact auth.authored authored
  · obtain ⟨r,present,eq⟩ := List.mem_map.mp finished
    rw [←eq]
    exact auth.produced r (List.mem_filter.mp present).1

/-- This equivalence only transports the C331 typing proof. It does not
establish whose completed output authorized a specific selected site. -/
theorem read_with_genuine_completed_and_source_support_iff_finite_visible_read
    {s : Before} {t : Table} (auth : Attached s t)
    {mode : Mode} {raw code : Expr} {uses : List Occurrence} :
    (∃ wire, runReadCard s (visibleReadView t) mode raw code wire = some uses) ↔
    Read (restriction (support auth)) mode raw code uses := by
  rw [authored_read_card_iff (visible_projected_rows_are_existing_physical_equations auth)]
  constructor
  · intro withView
    obtain ⟨rows,resident,usingRead⟩ := trace withView
    exact usingRead (restriction (support auth)) rfl (fun r found =>
      (visible_read_view_reflects_existing_authority auth r).mp (resident found))
  · intro withSupport
    obtain ⟨rows,resident,usingRead⟩ := trace withSupport
    exact usingRead (authoredView s (visibleReadView t)) rfl (fun r found =>
      (visible_read_view_reflects_existing_authority auth r).mpr (resident found))

theorem every_read_view_ordinal_is_source_or_completed_output {s : Before} {t : Table}
    (auth : Attached s t) (i : Nat) (row : Equation)
    (stored : (visibleReadView t).authored[i]? = some row) :
    row ∈ s.equations ∧
      (row ∈ t.authored ∨ ∃ issuer, (row,issuer) ∈ t.produced ∧ issuer ∈ t.released) := by
  have existsIn : row ∈ GeneralDeclarativeWitnessOrigins350.visible t := List.mem_of_getElem? stored
  refine ⟨(visible_projected_rows_are_existing_physical_equations auth).authored existsIn,?_⟩
  change row ∈ t.authored ++ (t.produced.filter (fun q => t.released.contains q.2)).map Prod.fst at existsIn
  rcases List.mem_append.mp existsIn with source | issued
  · exact .inl source
  · obtain ⟨⟨r,issuer⟩,present,rfl⟩ := List.mem_map.mp issued
    obtain ⟨production,live⟩ := List.mem_filter.mp present
    exact .inr ⟨issuer,production,by simpa using live⟩


inductive ReadRowAuthority where
  | authored (ordinal : Nat)
  | completed (ordinal owner : Nat)
  deriving DecidableEq

private def producedMarks (released : List Nat) (rows : List (Equation × Nat))
    (start : Nat) : List (ReadRowAuthority × Equation) :=
  ((rows.zipIdx start).filter (fun p => released.contains p.1.2)).map
    (fun p => (.completed p.2 p.1.2,p.1.1))

def visibleWithAuthority (t : Table) : List (ReadRowAuthority × Equation) :=
  (t.authored.zipIdx.map (fun p => (.authored p.2,p.1))) ++ producedMarks t.released t.produced 0

theorem visibleWithAuthority_erases_to_exact_input_view (t : Table) :
    (visibleWithAuthority t).map Prod.snd = (visibleReadView t).authored := by
  change _ = t.authored ++ (t.produced.filter (fun p => t.released.contains p.2)).map Prod.fst
  have eraseProduced (rows : List (Equation × Nat)) (offset : Nat) :
      (producedMarks t.released rows offset).map Prod.snd =
        (rows.filter (fun p => t.released.contains p.2)).map Prod.fst := by
    induction rows generalizing offset with
    | nil => rfl
    | cons q tail ih =>
      simp only [producedMarks, List.zipIdx_cons, List.filter_cons]
      split
      · simp only [List.map_cons]
        exact congrArg (List.cons q.1) (ih (offset+1))
      · exact ih (offset+1)
  simp only [visibleWithAuthority, List.map_append, eraseProduced, List.map_map]
  change (t.authored.zipIdx.map Prod.fst) ++ _ = _
  rw [List.zipIdx_map_fst]

def ReadRowAuthority.Valid (t : Table) (row : Equation) : ReadRowAuthority → Prop
  | .authored index => t.authored[index]? = some row
  | .completed index owner => t.produced[index]? = some (row,owner) ∧ owner ∈ t.released

theorem each_projected_view_slot_has_original_ordinal_authority
    (t : Table) (i : Nat) (row : Equation) (stored : (visibleReadView t).authored[i]? = some row) :
    ∃ label, (visibleWithAuthority t)[i]? = some (label,row) ∧ label.Valid t row := by
  rw [←visibleWithAuthority_erases_to_exact_input_view, List.getElem?_map] at stored
  cases read : (visibleWithAuthority t)[i]? with
  | none => simp [read] at stored
  | some pair =>
    rcases pair with ⟨tag,storedRow⟩
    simp only [read,Option.map_some,Option.some.injEq] at stored
    subst storedRow
    refine ⟨tag,rfl,?_⟩
    have member := List.mem_of_getElem? read
    unfold visibleWithAuthority at member
    rcases List.mem_append.mp member with authored | released
    · obtain ⟨⟨item,n⟩,present,equal⟩ := List.mem_map.mp authored
      change (ReadRowAuthority.authored n,item) = (tag,row) at equal
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj equal
      exact List.mk_mem_zipIdx_iff_getElem?.mp present
    · obtain ⟨⟨⟨item,k⟩,n⟩,present,equal⟩ := List.mem_map.mp released
      change (ReadRowAuthority.completed n k,item) = (tag,row) at equal
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj equal
      obtain ⟨recorded,completed⟩ := List.mem_filter.mp present
      exact ⟨List.mk_mem_zipIdx_iff_getElem?.mp recorded,by simpa using completed⟩


end Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
