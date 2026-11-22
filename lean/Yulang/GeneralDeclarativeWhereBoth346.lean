import Yulang.GeneralDeclarativeWhereAttributed346

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWhereBoth346
open GeneralDeclarations (Registry)
open GeneralNominalCenters (Plan Site)
open GeneralWhereOriginDelta318 (Cell)
open GeneralWhereVersionInstall317 (Journal InstallStep Models install emitted)
open GeneralWhereVersionCompiler317 (child schema)
open GeneralDeclarativeWhereEndpoint346 (At)
open GeneralDeclarativeCommitPosition344 (clauses signature source_at)
open GeneralWhereOriginSchema318 (pick)
open GeneralWhereOriginDescriptor318 (argument)
open GeneralVersionedEndpointAddress315 (atCell Side)
open GeneralNominalVersionedPlans231 (variables)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeWhere319 (Capture)

def polar {p : Plan rs} (c : Cell p) (side : Side) : Cell p := {c with side := side}

/-- Every materialized compound argument has both exact address
receipts at the same child position. Its actual center is taken from
that committed site, not from either of the two endpoint names. -/
theorem paired {r : Registry} {before : Journal rs} {ctx : GeneralNominalCandidates.Context}
    {p : Plan rs} (step : InstallStep r before (install before ctx p))
    (c : Cell p) (m : Assignment) (valid : Models (install before ctx p) m) :
    ∃ (ord : Nat) (site : Site rs) (i : Fin (rs site.occurrence.demand.role).arity) (cap : Capture),
      i.val = c.index ∧ cap.lower = (polar c .lower).row.target ∧
      cap.center = site.center i ∧ cap.upper = (polar c .upper).row.target ∧
      At before (install before ctx p) p (polar c .lower) ord site ∧
      At before (install before ctx p) p (polar c .upper) ord site ∧
      CommonNominalFullCarrier.Subtype (m cap.lower).1 (m cap.center).1 ∧
      CommonNominalFullCarrier.Subtype (m cap.center).1 (m cap.upper).1 := by
  obtain ⟨ord,site,old,_⟩ := GeneralDeclarativeWhereEndpoint346.from_step step c m valid
  obtain ⟨note,known,equal⟩ := old.canonical
  obtain ⟨actual,atNote,exactSite⟩ := source_at p old.emittedHere
  have same : note = actual := Option.some.inj (known.symm.trans atNote)
  subst actual
  subst site
  let sig := signature p note
  have good : c.index < note.val.arguments.length := equal.symm ▸ (List.getElem?_eq_some_iff.mp c.located).1
  let i : Fin (rs note.val.role).arity := ⟨c.index,by rw [← sig.1]; exact good⟩
  have wherePat : note.val.arguments[i.val]? = some c.pattern := by
    change note.val.arguments[c.index]? = _
    rw [equal]; exact c.located
  have args := argument sig i wherePat c.compound c.translated
  have typed := valid.1.1.2.2.2.1 _
    (List.mem_iff_getElem?.mpr ⟨_,old.physical⟩) i
  rw [args] at typed
  have each (side : Side) : At before (install before ctx p) p (polar c side) ord (child p note.val sig) := by
    refine ⟨old.stamp,old.physical,old.emittedHere,old.childHere,⟨note,known,equal⟩,equal ▸ rfl,?_,
      (polar c side).written.1⟩
    refine ⟨i,rfl,?_⟩
    rw [args]
    change pick side (atCell p .lower note.val.id c.index c.expression,
      atCell p .upper note.val.id c.index c.expression) = atCell p side c.clause.id c.index c.expression
    rw [equal]
    cases side <;> rfl
  let cap : Capture := ⟨(polar c .lower).row.target,(child p note.val sig).center i,(polar c .upper).row.target⟩
  refine ⟨ord,child p note.val sig,i,cap,rfl,rfl,rfl,rfl,each .lower,each .upper,?_⟩
  unfold GeneralNominalCaptureMerges.Fits at typed
  rw [congrArg GeneralDeclarations.Clause.id equal] at typed
  exact typed

end Yulang.GeneralDeclarativeWhereBoth346
