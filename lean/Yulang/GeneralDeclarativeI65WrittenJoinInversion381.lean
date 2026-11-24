import Yulang.GeneralDeclarativeI65WrittenJoinEvents381
import Yulang.GeneralDeclarativeNormalizeCovered322

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open CommonRoleOutermostResolver (Frontier)
open GeneralDeclarativeWitnessClassifyVariance357 (Rule roleView)
open GeneralDeclarativeWitnessDeclaredState357 (Joined)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralNominalCenteredHeadWFSource
  (Coverage PatternCovered PatternsCovered ConstructorUse constructor_interpreted)
open GeneralDeclarativeNormalizeCovered322 (normalize_covered)
open GeneralDeclarativeWitnessConstructorModes357 (SourceMode)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeDemand320 (Demand)

/-- Raw authored head and caller-visible singleton, with no body,
checker result, release, or selected occurrence in its fields. -/
structure WrittenJoinHeadScope381 (s : State) where
  request : Request
  row : Declaration
  single : (roleView s.current request.demand.role).declarations = [row]
  head : Joined s.current request.demand row

/-- The exact authored covariant nominal constructor at this visible
head cannot be silently routed through the older ordinary-only C357
constructor. This is a disjointness proof, not a bridge to that rule
and not a rejection result when another shape has no evidence. -/
theorem written_join_excludes_ordinary_coverage381
    {s : State} (known : WrittenJoinHeadScope381 s)
    (ordinary : Coverage (roleView s.current known.request.demand.role)
      (interpretation s.current.environment.source.snapshot)) : False := by
  have visible : known.row ∈ (roleView s.current known.request.demand.role).declarations := by
    rw [known.single]
    exact List.mem_cons_self
  have covered := (ordinary.1 known.row visible).1
  rw [known.head.head] at covered
  have raw : PatternCovered (roleView s.current known.request.demand.role).constructors
      (interpretation s.current.environment.source.snapshot) known.head.written := covered.1
  have normalized := normalize_covered raw
  rw [known.head.normalized] at normalized
  have oldUse : ConstructorUse (roleView s.current known.request.demand.role).constructors
      (interpretation s.current.environment.source.snapshot) known.head.name 1 :=
    normalized.1.1
  have mode := known.head.use.sourced
  rw [known.head.co] at mode
  cases mode with
  | declared _ noPrim noInvariant =>
    rcases constructor_interpreted oldUse with ⟨p,primitive⟩ | invariant
    · change GeneralSourceMetadataRows291.primitives s.current.environment.source.snapshot
        known.head.name = some p at primitive
      rw [noPrim] at primitive
      cases primitive
    · change GeneralSourceMetadataRows291.invariants s.current.environment.source.snapshot
        known.head.name = true at invariant
      rw [noInvariant] at invariant
      cases invariant

/-- Converse at one source node in the already established authored
join scope. Invert the actual C357 rule, retain its literal children,
and use unique visible row identity. The returned event comes from
this derivation, not from model equivalence. The head scope has
no body, compiler result, or preselected occurrence. -/
theorem invert_actual_C357_at_written_join381
    {s : State} (scope : WrittenJoinHeadScope381 s) {result : Frontier Demand}
    (derived : Rule s.current scope.request.demand result) :
    ∃ event : WrittenJoinEvent381 s,
      event.request = scope.request ∧ event.row = scope.row ∧
      result = .selected event.row.id event.demands ∧
      ActualWrittenJoin381 s event.request (.selected event.row.id
        (children event.request event.demands)) event := by
  cases derived with
  | ordinary _ legacy _ =>
    exact (written_join_excludes_ordinary_coverage381 scope legacy).elim
  | join chosen =>
    let event : WrittenJoinEvent381 s := ⟨scope.request,_,_,chosen⟩
    have row := (List.cons.inj (chosen.single.symm.trans scope.single)).1
    exact ⟨event,rfl,row,rfl,.authored event⟩

end Yulang.GeneralDeclarativeI65
