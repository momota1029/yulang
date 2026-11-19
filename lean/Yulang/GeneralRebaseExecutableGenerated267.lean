import Yulang.GeneralRebaseExecutableAlias267
import Yulang.GeneralRebaseOccurrenceEq267

namespace Yulang.GeneralRebaseExecutableGenerated267
open GeneralNominalSaturationState (State Alias Generated)
open GeneralNominalDemandMerging (Site)
open GeneralSourceDictionaries (Occurrence)
open GeneralRebaseOccurrenceEq267 (same same_exact)
open GeneralRebaseExecutableAlias267 (aliased aliased_exact)
open FiniteWorklist (Path reachable)

def children (state : State roles) (source : Occurrence roles) : List (Occurrence roles) :=
 (state.edges.filter fun pair => same source pair.1).map Prod.snd

def aliases (state : State roles) (source : Occurrence roles) : List (Occurrence roles) :=
 (state.sites.filter fun site => same source site.occurrence).flatMap fun first =>
   (state.sites.filter fun last => aliased state first.occurrence.identity last.occurrence.identity).map Site.occurrence

def next (state : State roles) (source : Occurrence roles) : List (Occurrence roles) :=
 children state source ++ aliases state source

def support (state : State roles) (root : Occurrence roles) : List (Occurrence roles) :=
 root :: (state.edges.map Prod.snd ++ state.sites.map Site.occurrence)

theorem children_exact (state : State roles) (source dest : Occurrence roles) :
 dest ∈ children state source ↔ (source,dest) ∈ state.edges := by
 simp only [children,List.mem_map,List.mem_filter,same_exact]
 constructor
 · rintro ⟨⟨a,b⟩,⟨listed,same⟩,ends⟩
   cases same
   cases ends
   exact listed
 · intro listed
   exact ⟨(source,dest),⟨listed,rfl⟩,rfl⟩

theorem aliases_exact (state : State roles) (source dest : Occurrence roles) :
 dest ∈ aliases state source ↔
 ∃ first ∈ state.sites, ∃ last ∈ state.sites, first.occurrence = source ∧ last.occurrence = dest ∧
 Alias state first.occurrence.identity last.occurrence.identity := by
 simp only [aliases,List.mem_flatMap,List.mem_filter,List.mem_map,same_exact,aliased_exact]
 constructor
 · rintro ⟨first,⟨f,eq⟩,last,⟨l,linked⟩,ends⟩
   exact ⟨first,f,last,l,eq.symm,ends,linked⟩
 · rintro ⟨first,f,last,l,eq,ends,linked⟩
   exact ⟨first,⟨f,eq.symm⟩,last,⟨l,linked⟩,ends⟩

theorem support_closed (state : State roles) (root source : Occurrence roles) :
 next state source ⊆ support state root := by
 intro dest inside
 apply List.mem_cons_of_mem
 rcases List.mem_append.mp inside with child | alias
 · exact List.mem_append_left _ (List.mem_map.mpr ⟨(source,dest),(children_exact ..).mp child,rfl⟩)
 · obtain ⟨_,_,last,listed,_,ends,_⟩ := (aliases_exact ..).mp alias
   exact List.mem_append_right _ (List.mem_map.mpr ⟨last,listed,ends⟩)

theorem follow (state : State roles) (generated : Generated state root source) (edge : dest ∈ next state source) :
 Generated state root dest := by
 rcases List.mem_append.mp edge with child | alias
 · exact .child generated ((children_exact ..).mp child)
 · obtain ⟨first,f,last,l,starts,ends,linked⟩ := (aliases_exact ..).mp alias
   exact ends ▸ (Generated.alias (starts.symm ▸ generated) f l linked)

theorem path_sound (state : State roles) (path : Path (next state) source dest)
 (generated : Generated state root source) : Generated state root dest := by
 induction path with
 | nil _ => exact generated
 | cons edge _ ih => exact ih (follow state generated edge)

theorem path_complete (state : State roles) (proof : Generated state root dest) :
 Path (next state) root dest := by
 induction proof with
 | root => exact .nil _
 | child _ listed ih =>
   exact ih.append (.cons (List.mem_append_left _ ((children_exact ..).mpr listed)) (.nil _))
 | alias _ one two linked ih =>
   exact ih.append (.cons (List.mem_append_right _
     ((aliases_exact ..).mpr ⟨_,one,_,two,rfl,rfl,linked⟩)) (.nil _))

/-- The actual journal graph is enough dest enumerate all and only generated
occurrences; the result makes no assertion about either candidate viability
or how many source states a later install may create. -/
def discover (state : State roles) (root : Occurrence roles) : List (Occurrence roles) :=
 letI : DecidableEq (Occurrence roles) := GeneralRebaseOccurrenceEq267.occurrenceEq
 reachable (next state) (support state root).length root

theorem discover_exact (state : State roles) (root goal : Occurrence roles) :
 goal ∈ discover state root ↔ Generated state root goal := by
 letI : DecidableEq (Occurrence roles) := GeneralRebaseOccurrenceEq267.occurrenceEq
 have known := GeneralRebaseSupportedWorklist267.reachable_exact (next state) (support state root)
   (fun f _ => support_closed state root f) List.mem_cons_self goal
 exact known.trans ⟨fun path => path_sound state path .root,path_complete state⟩

end Yulang.GeneralRebaseExecutableGenerated267
