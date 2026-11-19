import Yulang.GeneralRebaseSlotInequalities269
import Yulang.FiniteWorklistRelative269
import Yulang.GeneralNominalVersionedJournal232

namespace Yulang.GeneralRebaseJournalInequalities269
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenters (Site)
open GeneralRebaseSlotInequalities269 (pairOf by_atom)
open CommonNominalFullCarrier
open FiniteWorklist (Path)

def Between (state : State roles) (a b : Nat) : Prop :=
 ∀ model, Models state model → Subtype (model a).1 (model b).1

def fromRaw (state : GeneralNominalState.State) : List (Nat × Nat) :=
 let names := fun (pair : Fin state.base.slots × Fin state.base.slots) =>
   (state.base.source pair.1,state.base.source pair.2)
 state.ordinary.filterMap pairOf ++ state.base.intervals.map names ++
  (state.base.ordinary.filterMap pairOf).map names

theorem fromRaw_sound (state : GeneralNominalState.State) (model : Assignment)
 (valid : GeneralNominalState.Models state model) (a b : Nat) (listed : (a,b) ∈ fromRaw state) :
 Subtype (model a).1 (model b).1 := by
 simp only [fromRaw,List.mem_append,List.mem_map,List.mem_filterMap] at listed
 rcases listed with ((⟨atom,found,pair⟩ | ⟨⟨first,last⟩,interval,keys⟩) | ⟨⟨first,last⟩,⟨atom,found,pair⟩,keys⟩)
 · exact by_atom model pair (valid.2.2 atom found)
 · cases keys
   exact valid.1.2.2 _ interval
 · cases keys
   exact by_atom (GeneralNominalCommonBridge.assignment state.base model) pair (valid.1.1 atom found)

def centerEdges (site : Site roles) : List (Nat × Nat) :=
 (List.finRange (roles site.occurrence.demand.role).arity).flatMap fun i =>
  let pair := site.occurrence.demand.arguments i
  [(pair.1,site.center i),(site.center i,pair.2)]

theorem center_sound (site : Site roles) (model : Assignment) (valid : site.Holds model)
 (a b : Nat) (listed : (a,b) ∈ centerEdges site) : Subtype (model a).1 (model b).1 := by
 obtain ⟨index,_,edges⟩ := List.mem_flatMap.mp listed
 simp only [List.mem_cons,List.not_mem_nil,or_false] at edges
 rcases edges with same | same <;> cases same
 · exact (valid index).1
 · exact (valid index).2

def edges (state : State roles) : List (Nat × Nat) :=
 fromRaw state.core.erased.current.context.state ++ fromRaw state.core.erased.source.state ++
  state.core.sites.flatMap centerEdges

theorem edges_sound (state : State roles) (a b : Nat) (listed : (a,b) ∈ edges state) : Between state a b := by
 intro model valid
 simp only [edges,List.mem_append,List.mem_flatMap] at listed
 rcases listed with ((now | src) | ⟨site,onList,bit⟩)
 · exact fromRaw_sound _ model valid.1.1 a b now
 · exact fromRaw_sound _ model valid.1.2.1 a b src
 · exact center_sound site model (valid.1.2.2.2.1 site onList) a b bit

def adj (pairs : List (Nat × Nat)) (a : Nat) : List Nat :=
 pairs.filterMap fun p => if p.1 = a then some p.2 else none

theorem adj_exact (pairs : List (Nat × Nat)) (a b : Nat) :
 b ∈ adj pairs a ↔ (a,b) ∈ pairs := by
 simp only [adj,List.mem_filterMap]
 constructor
 · rintro ⟨⟨x,y⟩,onList,atPoint⟩
   by_cases same : x = a
   · subst x
     have equal : y = b := by simpa using atPoint
     subst y
     exact onList
   · simp [same] at atPoint
 · intro pair
   exact ⟨(a,b),pair,by simp⟩

def scope (pairs : List (Nat × Nat)) (a : Nat) : List Nat :=
 a :: pairs.flatMap (fun p => [p.1,p.2])

theorem scope_closed (pairs : List (Nat × Nat)) (a : Nat) :
 FiniteWorklistRelative269.Closed (adj pairs) (scope pairs a) := by
 intro i _ j edge
 have listed := (adj_exact pairs i j).mp edge
 exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨(i,j),listed,by simp⟩)

def prove (state : State roles) (a b : Nat) : Bool :=
 let pairs := edges state
 decide (b ∈ FiniteWorklist.reachable (adj pairs) (scope pairs a).length a)

theorem prove_exact (state : State roles) (a b : Nat) :
 prove state a b = true ↔ Path (adj (edges state)) a b := by
 unfold prove
 simpa only [decide_eq_true_eq] using
   (FiniteWorklistRelative269.reachable_exact _ _ (scope_closed (edges state) a) a b List.mem_cons_self)

theorem path_sound (state : State roles) (trace : Path (adj (edges state)) a b) : Between state a b := by
 intro model valid
 induction trace with
 | nil => exact subtype_refl _
 | cons edge _ ih =>
   exact subtype_trans (edges_sound state _ _ ((adj_exact ..).mp edge) model valid) ih

theorem prove_sound (state : State roles) (a b : Nat) (yes : prove state a b = true) : Between state a b :=
 path_sound state ((prove_exact state a b).mp yes)

end Yulang.GeneralRebaseJournalInequalities269
