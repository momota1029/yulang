import Yulang.GeneralRebaseScalarAtoms271

namespace Yulang.GeneralRebaseScalarSnapshot271
open GeneralNominalState (State Models)
open GeneralNormalizedObservation (Head Snapshot)
open GeneralRebaseScalarAtoms271 (candidate checks)

def promote (state : State) (slot : Fin state.base.slots) :
 Head state.view.shapes state.base.slots :=
 match state.nominals slot, state.view.heads slot with
 | none,.deferred .unresolved =>
    match candidate state.base slot with
    | some b => .scalar b
    | none => state.view.heads slot
 | _,_ => state.view.heads slot

def view (state : State) : Snapshot state.base where
 kinds := state.view.kinds
 shapes := state.view.shapes
 shapes_injective := state.view.shapes_injective
 canonical := state.view.canonical
 heads := promote state
 checked := by
   intro slot term recorded
   unfold promote at recorded
   split at recorded
   · split at recorded
     · rename_i b found
       have e : Core.PresenceGeneration.TyTerm.base b = term := Option.some.inj recorded
       cases e
       exact checks state.base slot b found
     · exact state.view.checked slot term recorded
   · exact state.view.checked slot term recorded

theorem keeps_opaque (state : State) (slot : Fin state.base.slots) (d : GeneralNominalState.Descriptor state.base.slots)
 (known : state.nominals slot = some d) : (view state).heads slot = .deferred .unresolved := by
 change promote state slot = _
 simp only [promote,known]
 exact state.bodies_opaque slot d known

def enrich (state : State) : State :=
 {state with view := view state, bodies_opaque := keeps_opaque state}

theorem exact_models (state : State) (model : GeneralNominalCommonBridge.Assignment) :
 Models (enrich state) model ↔ Models state model := Iff.rfl

def context (old : GeneralNominalCandidates.Context) : GeneralNominalCandidates.Context :=
 {old with state := enrich old.state}

def journal (old : GeneralNominalCandidates.Context) (root : GeneralSourceDictionaries.Occurrence roles) :=
 GeneralNominalVersionedJournal232.initial (context old) root

theorem initial_models (old : GeneralNominalCandidates.Context) (root : GeneralSourceDictionaries.Occurrence roles)
 (model : GeneralNominalCommonBridge.Assignment) :
 GeneralNominalVersionedJournal232.Models (journal old root) model ↔
 GeneralNominalVersionedJournal232.Models (GeneralNominalVersionedJournal232.initial old root) model := by
 unfold journal
 rw [GeneralNominalVersionedJournal232.initial_models,GeneralNominalVersionedJournal232.initial_models]
 rfl

theorem initial_sites (old : GeneralNominalCandidates.Context) (root : GeneralSourceDictionaries.Occurrence roles) :
 (journal old root).core.sites = (GeneralNominalVersionedJournal232.initial old root).core.sites := rfl

end Yulang.GeneralRebaseScalarSnapshot271
