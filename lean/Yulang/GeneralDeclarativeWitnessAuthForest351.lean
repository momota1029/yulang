import Yulang.GeneralDeclarativeWitnessAuthNode351
import Yulang.GeneralDeclarativeWitnessCatalog351
import Yulang.GeneralDeclarativeWitnessForestEngine350

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessAuthForest351
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWitnessOrigins350 (Table Attached support)
open GeneralDeclarativeWitnessAuthNode351 (Anchor Node waiting replayNode)
open GeneralDeclarativeWitnessForest350 (Layout Fixed Code Codes extendSidecar)
open GeneralDeclarativeWitnessRecordReplay350 (Wire)
open GeneralDeclarativeExactOverlay337 (Holds ModelsExact)
open GeneralDeclarativeEndpointOverlay336 (Entry)
open GeneralDeclarativeTaggedDictionary340 (Rule)
open GeneralNominalCommonBridge (Assignment)
open GeneralSourceMetadataBareBundle291 (InputBundle compile)
open GeneralSourceMetadataBundle291 (SourceBundle registry)
open GeneralSourceMetadataRows291 (interpretation)
open CommonRoleOutermostResolver (Tree Resolves All₂)

structure Problem where
  writer : GeneralDeclarativeWitnessCatalog351.Anchor
  consumer : InputBundle
  target : Demand
  layout : List Nat → Demand → Layout

abbrev Problem.current (p : Problem) := p.writer.roles.current

structure Global (p : Problem) (t : Table) where
  bundle : SourceBundle
  canonical : compile p.consumer = some bundle
  live : Attached p.current t

def localProblem (p : Problem) (t : Table) (path : List Nat) (d : Demand) : Anchor :=
  let row := p.layout path d
  ⟨⟨p.consumer,p.current,d⟩,row.before,t,row.keep,row.fallback,row.targets⟩

abbrev rules {p : Problem} {t : Table} (env : Global p t) (es : List Entry) :=
  Rule (support env.live) es (registry env.bundle) (interpretation env.bundle.snapshot)
    (waiting env.live (registry env.bundle) (interpretation env.bundle.snapshot))

def reader {p : Problem} {t : Table} (g : Global p t) (path : List Nat) (d : Demand) (w : Wire) :
    Option (Node g.live g.bundle d) :=
  replayNode (localProblem p t path d) g.canonical g.live w

structure Replayed {p : Problem} {t : Table} (env : Global p t) (d : Demand) where
  tree : Tree
  sidecar : List Entry
  proof : ∀ b, sidecar ⊆ b → Resolves (rules env b) d tree
  fixed : List Fixed
  fixedMeaning : ∀ f ∈ fixed, f.Meaning p.current
  exactIn : ∀ m : Assignment, Models p.current m → ∀ e ∈ sidecar, Holds m e

structure ReplayedList {p : Problem} {t : Table} (env : Global p t) (ds : List Demand) where
  trees : List Tree
  sidecar : List Entry
  proof : ∀ b, sidecar ⊆ b → All₂ (Resolves (rules env b)) ds trees
  fixed : List Fixed
  fixedMeaning : ∀ f ∈ fixed, f.Meaning p.current
  exactIn : ∀ m : Assignment, Models p.current m → ∀ e ∈ sidecar, Holds m e

mutual
/-- The authoritative child inputs are exactly those emitted by the
compiler in sequence. The witness tree carries no replacement demands. -/
def replayTree {p : Problem} {t : Table} (env : Global p t) (path : List Nat) (d : Demand) :
    Code → Option (Replayed env d)
  | .node layoutHere child => do
    let head ← reader env path d layoutHere
    let tail ← replayList env path 0 head.kids child
    pure ⟨.selected head.decl.id tail.trees,head.sidecar ++ tail.sidecar,
      (fun b covers => .selected (.whole (extendSidecar head.selection
        (fun _ h => covers (List.mem_append_left _ h))))
        (tail.proof b (fun _ h => covers (List.mem_append_right _ h)))),
      ⟨path,d,head.fixed⟩ :: tail.fixed,
      (fun f h => (List.mem_cons.mp h).elim (fun same => same.symm ▸ head.meaning path) (tail.fixedMeaning f)),
      (fun m fit e included => (List.mem_append.mp included).elim
        (fun h => (head.models m fit).2 e h) (fun h => tail.exactIn m fit e h))⟩
termination_by w => sizeOf w

def replayList {p : Problem} {t : Table} (env : Global p t) (path : List Nat) (ordinal : Nat) (ds : List Demand) :
    Codes → Option (ReplayedList env ds)
  | .nil =>
    match ds with
    | [] => some ⟨[],[],fun _ _ => .nil,[],fun _ h => False.elim (List.not_mem_nil h),fun _ _ _ impossible => False.elim (List.not_mem_nil impossible)⟩
    | _ :: _ => none
  | .cons first more =>
    match ds with
    | [] => none
    | d :: ds => do
      let head ← replayTree env (path ++ [ordinal]) d first
      let tail ← replayList env path (ordinal+1) ds more
      pure ⟨head.tree :: tail.trees,head.sidecar ++ tail.sidecar,
        (fun b covers => .cons (head.proof b (fun _ h => covers (List.mem_append_left _ h)))
          (tail.proof b (fun _ h => covers (List.mem_append_right _ h)))),
        head.fixed ++ tail.fixed,
        (fun f h => (List.mem_append.mp h).elim (head.fixedMeaning f) (tail.fixedMeaning f)),
        (fun m fit e included => (List.mem_append.mp included).elim
          (head.exactIn m fit e) (tail.exactIn m fit e))⟩
termination_by w => sizeOf w
end

theorem resolves {p : Problem} {t : Table} {env : Global p t} {d : Demand} (r : Replayed env d) :
    Resolves (rules env r.sidecar) d r.tree := r.proof _ (fun _ h => h)

theorem models {p : Problem} {t : Table} {env : Global p t} {d : Demand} (r : Replayed env d)
    (m : Assignment) (fit : Models p.current m) : ModelsExact p.current r.sidecar m :=
  ⟨fit,r.exactIn m fit⟩

end Yulang.GeneralDeclarativeWitnessAuthForest351
