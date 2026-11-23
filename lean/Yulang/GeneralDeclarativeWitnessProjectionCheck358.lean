import Yulang.GeneralDeclarativeWitnessProjectionRule358

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessProjectionCheck358
open GeneralDeclarativeWitnessDeclaredState357 (Current WrittenBody context)
open GeneralDeclarativeWitnessAuthoredProjection358 (Source Recipe check_exact)
open GeneralDeclarativeWitnessProjectionRule358 (Selected Rule)
open GeneralDeclarativeWitnessClassifyVariance357 (roleView)
open GeneralDeclarativeWitnessJoinedCheck357 (Layout)
open GeneralDeclarativeWitnessCompiler350 (Wire printDemand decode retained map_injective trip_injective trip)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (normalizeArgs)

structure Certificate (src : Source) (s : Current) (d : Demand) (w : Wire) where
  impl : Declaration
  kids : List Demand
  chosen : Selected src s d impl kids
  printed : w.children = kids.map printDemand
  written : w.outputRows = chosen.body.finished.fixed

def replay (src : Source) (s : Current) (d : Demand) (r : Recipe) (binder : Nat) (l : Layout) (w : Wire) :
    Option (Certificate src s d w) :=
  match found : (roleView s d.role).declarations with
  | [impl] =>
    if raw : GeneralDeclarativeWitnessAuthoredProjection358.check src s.ordinary r = true then
      if actual : d.arguments.map trip = [trip r.outer] then
        if head : normalizeArgs impl.head = [.variant r.tag (.var binder)] then do
          let frame := context s d impl l.named [(binder,r.inner)] l.keep l.fallback l.via
          let accepted ← decode frame s.ordinary w
          let body : WrittenBody s d impl [(binder,r.inner)] accepted.compiled.kids :=
            ⟨l.named,l.keep,l.fallback,l.via,accepted.compiled,accepted.run,rfl,retained accepted⟩
          pure ⟨impl,accepted.compiled.kids,
            ⟨r,check_exact.mp raw,found,map_injective (fun h => trip_injective h) actual,binder,head,body⟩,
            accepted.printed,accepted.fixed⟩
        else none
      else none
    else none
  | _ => none

theorem rule {a s d w} (seen : Certificate a s d w) :
    Rule a s d (.selected seen.impl.id seen.kids) :=
  .projection seen.chosen

end Yulang.GeneralDeclarativeWitnessProjectionCheck358
