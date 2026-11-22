import Yulang.GeneralDeclarativeWhereRawExpr346

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWhereRawAtoms346
open GeneralNominalCenters (Plan)
open GeneralWhereOriginDelta318 (Cell)
open GeneralNominalVersionedPlans231 (variables)
open GeneralNominalVersionedExpressionFrame236 (variableSource)
open GeneralDictionaryBinderLocations (sourceSlot sourceSlot_exact)
open GeneralSourceState (State equationAtoms)
open GeneralNominalCommonBridge (Assignment assignment)
open GeneralDeclarativeWhereRawExpr346 (compile value_exact)
open Core.PresenceGeneration (TyTerm)
open PresenceNormalForm (Atom All)

def cell (s : State) {p : Plan rs} (c : Cell p) : Option (List (Atom (Fin s.slots))) := do
  let slot ← sourceSlot s c.row.target
  let rhs ← compile (fun name => sourceSlot s (variableSource p c.side.mode name)) c.expression
  return equationAtoms slot rhs

theorem cell_computed {s : State} {p : Plan rs} {c : Cell p}
    {atoms : List (Atom (Fin s.slots))} (ran : cell s c = some atoms) :
    ∃ (slot : Fin s.slots) (rhs : TyTerm (Fin s.slots)),
      sourceSlot s c.row.target = some slot ∧
      compile (fun name => sourceSlot s (variableSource p c.side.mode name)) c.expression = some rhs ∧
      atoms = equationAtoms slot rhs := by
  unfold cell at ran
  obtain ⟨slot,located,next⟩ := Option.bind_eq_some_iff.mp ran
  obtain ⟨term,compiled,eq⟩ := Option.bind_eq_some_iff.mp next
  exact ⟨slot,term,located,compiled,(Option.some.inj eq).symm⟩

theorem semantic_atoms (s : State) (slot : Fin s.slots) (rhs : TyTerm (Fin s.slots)) (m : Assignment) :
    All CommonNominalFullCarrier.model (assignment s m) (equationAtoms slot rhs) ↔
      CommonNominalFullCarrier.Equivalent (m (s.source slot)).1
        (rhs.eval CommonNominalFullCarrier.model (assignment s m)) := by
  constructor
  · intro h
    exact ⟨h _ List.mem_cons_self,h _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))⟩
  · intro h row present
    simp only [equationAtoms,List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with rfl|rfl
    · exact h.1
    · exact h.2

theorem exact_cell {s : State} {p : Plan rs} {c : Cell p}
    {atoms : List (Atom (Fin s.slots))} (ran : cell s c = some atoms) (m : Assignment) :
    All CommonNominalFullCarrier.model (assignment s m) atoms ↔ c.row.Holds (variables p m) m := by
  obtain ⟨slot,rhs,located,compiled,rfl⟩ := cell_computed ran
  rw [semantic_atoms s slot rhs m]
  change CommonNominalFullCarrier.Equivalent (m (s.source slot)).1
    (rhs.eval CommonNominalFullCarrier.model (assignment s m)) ↔
      CommonNominalFullCarrier.Equivalent (m c.row.target).1
        (GeneralNominalCenteredHeadMatExpressions.value (variables p m) c.side.mode c.expression)
  rw [(sourceSlot_exact ..).mp located,value_exact s c.side.mode c.expression compiled m]

def batch (s : State) {p : Plan rs} : List (Cell p) → Option (List (Atom (Fin s.slots)))
  | [] => some []
  | first :: later => do pure ((← cell s first) ++ (← batch s later))

theorem batch_exact {s : State} {p : Plan rs} {selected : List (Cell p)}
    {atoms : List (Atom (Fin s.slots))} (ran : batch s selected = some atoms) (m : Assignment) :
    All CommonNominalFullCarrier.model (assignment s m) atoms ↔ ∀ c ∈ selected,c.row.Holds (variables p m) m := by
  induction selected generalizing atoms with
  | nil =>
    have h : [] = atoms := Option.some.inj ran
    subst atoms
    simp [All]
  | cons first rest ih =>
    unfold batch at ran
    obtain ⟨one,head,next⟩ := Option.bind_eq_some_iff.mp ran
    obtain ⟨many,tail,eq⟩ := Option.bind_eq_some_iff.mp next
    have same : one ++ many = atoms := Option.some.inj eq
    subst atoms
    rw [PresenceNormalForm.all_append,exact_cell head m,ih tail]
    constructor
    · rintro ⟨current,later⟩ c contains
      rcases List.mem_cons.mp contains with rfl|contains
      · exact current
      · exact later c contains
    · intro all
      exact ⟨all _ List.mem_cons_self,fun c h => all c (List.mem_cons_of_mem _ h)⟩

end Yulang.GeneralDeclarativeWhereRawAtoms346
