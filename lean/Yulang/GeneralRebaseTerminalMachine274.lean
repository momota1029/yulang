import Yulang.GeneralRebaseTerminalRows274
import Yulang.GeneralRebaseCompoundOwnerBlock273

namespace Yulang.GeneralRebaseTerminalMachine274
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalAllocation (Bindings)
open GeneralRebaseCompoundOwnerBlock273 (Block PublicSlot compile loose point)
open GeneralRebaseCompoundSourceTypes273 (PublicSource Body)
open GeneralDictionaryJournalRefinement228Source (root)
open GeneralDictionaryOptionalInitial229 (declaration)

inductive Stage where
 | source | installed | observed | terminal
 deriving DecidableEq, Repr

inductive Event where
 | install (owner : Nat) (bindings : Bindings) (center : PublicSlot)
 | observe (owner : Nat) (bindings : Bindings) (center : PublicSlot)
 | service (owner : Nat)
 deriving Repr

def owner : Nat := GeneralNominalIdentities.pair root.identity declaration.id

/-- Old and new are the same logical owner. Observing the new binding does
not change the committed block; service overwrites it without an extra slot. -/
def committed : Stage → Option Block
 | .source => none
 | .installed | .observed => some loose
 | .terminal => some point

def pending : Stage → Option Block
 | .observed => some point
 | _ => none

def next : Stage → Event → Option Stage
 | .source,.install key bindings center =>
   if key = owner ∧ compile bindings center = some loose then some .installed else none
 | .installed,.observe key bindings center =>
   if key = owner ∧ compile bindings center = some point then some .observed else none
 | .observed,.service key =>
   if key = owner then some .terminal else none
 | _,_ => none

def Step (s t : Stage) : Prop := ∃ input, next s input = some t

def rank : Stage → Nat
 | .source => 3
 | .installed => 2
 | .observed => 1
 | .terminal => 0

theorem strict {s t : Stage} (step : Step s t) : rank t < rank s := by
 obtain ⟨input,h⟩ := step
 unfold next at h
 split at h <;> try contradiction
 all_goals split at h <;> try contradiction
 all_goals cases Option.some.inj h; decide

theorem accessible (s : Stage) : Acc (fun t s => Step s t) s := by
 have below := (measure rank).wf.apply s
 induction below with
 | intro current _ ih => exact .intro current (fun t step => ih t (strict step))

theorem terminal_halted (s : Stage) : ¬ Step .terminal s := fun given =>
 (Nat.not_lt_zero _) (strict given)

def Public (stage : Stage) (boundary : Assignment) : Prop :=
 PublicSource boundary ∧ (stage ≠ .source → Body boundary)

theorem initial (boundary : Assignment) : Public .source boundary ↔ PublicSource boundary := by
 simp [Public]

theorem after_install {stage : Stage} (post : stage ≠ .source) (boundary : Assignment) :
 Public stage boundary ↔ GeneralRebaseCompoundPublic273.Fixed boundary := by
 rw [GeneralRebaseCompoundSourceTypes273.restricted_exact]
 simp [Public,post]

def replay : Stage → List Event → Option Stage
 | stage,[] => some stage
 | stage,e::es => (next stage e).bind (fun f => replay f es)

def firstBindings : Bindings := [(0,4,2),(0,4,2)]
def pointBindings : Bindings := [(0,2,2),(0,2,2)]

def script : List Event := [.install owner firstBindings 2,.observe owner pointBindings 2,.service owner]

theorem standard_route : replay .source script = some .terminal := rfl

theorem no_early_service : next .installed (.service owner) = none := rfl

theorem no_wrong_owner : next .observed (.service (owner+1)) = none := rfl

theorem no_stale_observation : next .installed (.observe owner firstBindings 2) = none := rfl

theorem single_overwrite : committed .observed = some loose ∧ pending .observed = some point ∧
 committed .terminal = some point ∧ pending .terminal = none := ⟨rfl,rfl,rfl,rfl⟩

end Yulang.GeneralRebaseTerminalMachine274
