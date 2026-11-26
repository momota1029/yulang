import Yulang.GeneralDeclarativeI65I74PendingAssociatedRawGraph434

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.PendingAssociated434
open GeneralDeclarativeI65
open GeneralDeclarativeWitnessDeclaredState357 (point)
open GeneralDeclarativeLowerKnown321 (Ready Delayed knows_row)
open GeneralDeclarativeWitnessOrigins350 (Table Attached support)
open GeneralDeclarativeOrigins321 (from_source)
open Checker408 (Problem Result)

/-- An independently authored source occurrence arrives for the same
literal A = list B row. This is a pair of complete snapshots, not a claim
about a solver step. No other written row or completed-owner flag changes. -/
structure AddedIndependentSource434 {s q} (o : OriginalPendingWhere434 s q)
    (t : I72.State) where
  actual : Origin
  sourceList : t.core.origins = [o.episode.seed,actual]
  distinctIssuer : actual.issuer ≠ o.episode.seed.issuer
  originalInput : actual.slot = o.episode.a
  exactSourceSyntax : actual.endpoint = sourceInput434 o.episode.key o.episode.b
  keepRawGraph : t.core.current.ordinary = s.core.current.ordinary

def independentlyAuthoredTable434 {s q} (o : OriginalPendingWhere434 s q) : Table :=
  ⟨[outerRow434 o.episode.key o.episode.seed.slot o.episode.a,
    retainedOutput434 o.episode.key o.episode.a o.episode.b],
    [(retainedOutput434 o.episode.key o.episode.a o.episode.b,o.episode.seed.slot)],[]⟩

def added_independent_source_attachment434 {s q t} {o : OriginalPendingWhere434 s q}
    (delta : AddedIndependentSource434 o t) :
    Attached t.core.current.ordinary (independentlyAuthoredTable434 o) where
  authored := fun row h => by
    rw [delta.keepRawGraph,o.episode.exactRows]
    exact List.mem_append_left [untouchedOutput434 o.episode.b] h
  produced := fun pair h => by
    obtain rfl := List.mem_singleton.mp h
    rw [delta.keepRawGraph,o.episode.exactRows]
    exact List.mem_cons_of_mem _ List.mem_cons_self

/-- Independent source syntax reopens the input without adding a
completed producer, dropping the retained equation or changing K2.
This does not guess which candidates or dictionaries would win. -/
theorem independent_source_reopens_literal_head_without_releasing434
    {s q t} {o : OriginalPendingWhere434 s q} (delta : AddedIndependentSource434 o t) :
    Ready (support (added_independent_source_attachment434 delta)) q.demand ∧
    ¬ Delayed (support (added_independent_source_attachment434 delta)) q.demand ∧
    (RootCycle t q ↔ RootCycle s q) := by
  have ready : Ready (support (added_independent_source_attachment434 delta)) q.demand := by
    intro arg h
    rw [o.episode.targetArg] at h
    obtain rfl := List.mem_singleton.mp h
    refine ⟨.nominal o.episode.key 1,knows_row
      (code := .nominal o.episode.key [.variable o.episode.b]) ?_ rfl⟩
    exact from_source (support (added_independent_source_attachment434 delta))
      (List.mem_cons_of_mem _ List.mem_cons_self)
  exact ⟨ready,(GeneralDeclarativeLowerKnown321.ready_iff_not_delayed _ _).mp ready,
    by simp only [RootCycle,delta.keepRawGraph]⟩

theorem independent_source_never_reuses_old_unfinished_pending_entry434
    {s q t} {o : OriginalPendingWhere434 s q} (delta : AddedIndependentSource434 o t)
    (r : Result) (proofData : Wire) :
    check ⟨t,q⟩ r (.pendingAssociated proofData) = false := by
  cases read : check ⟨t,q⟩ r (.pendingAssociated proofData) with
  | false => rfl
  | true =>
    obtain ⟨other,_,_⟩ := checked_pending_reads_actual_original_episode434 read
    have orig := other.original.episode.onlySeed
    change t.core.origins = [_] at orig
    rw [delta.sourceList] at orig
    have lengths := congrArg List.length orig
    simp at lengths

end Yulang.GeneralDeclarativeI65.I72.PendingAssociated434
