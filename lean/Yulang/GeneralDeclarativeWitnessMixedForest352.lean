import Yulang.GeneralDeclarativeWitnessTagBranch352
import Yulang.GeneralDeclarativeWitnessAuthForest351

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessMixedForest352
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWitnessOrigins350 (Table Attached support)
open GeneralDeclarativeWitnessAuthNode351 (Anchor Node waiting replayNode)
open GeneralDeclarativeWitnessTagBranch352 (LocalRoute)
open GeneralDeclarativeWitnessForest350 (Layout Fixed extendSidecar)
open GeneralDeclarativeExactOverlay337 (Holds ModelsExact)
open GeneralDeclarativeEndpointOverlay336 (Entry)
open GeneralDeclarativeExactDictionary337 (LocalNode Evidence)
open GeneralNominalCommonBridge (Assignment)
open GeneralSourceMetadataBareBundle291 (InputBundle compile)
open GeneralSourceMetadataBundle291 (SourceBundle registry)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarations (Declaration Checked)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralNominalCenteredHeadWFSource (Coverage)
open CommonRoleOutermostResolver (Tree Dictionary Frontier Result Resolves Summarizes All₂ Classify)

structure Problem where
  source : InputBundle
  current : State
  origins : Table
  target : Demand
  layout : List Nat → Demand → Layout

structure Global (p : Problem) where
  table : SourceBundle
  canonical : compile p.source = some table
  live : Attached p.current p.origins

def atNode (p : Problem) (path : List Nat) (d : Demand) : Anchor :=
  let coordinates := p.layout path d
  ⟨⟨p.source,p.current,d⟩,coordinates.before,p.origins,coordinates.keep,
    coordinates.fallback,coordinates.targets⟩

/-- Two positive fronts over the same source and state. A failed parse,
unsupported branch, or insufficient rank has no rule in this fragment;
none is used as a negative language verdict. -/
inductive Rule {p : Problem} (g : Global p) (es : List Entry) :
    Demand → Frontier Demand → Prop where
  | record : GeneralDeclarativeTaggedDictionary340.Rule (support g.live) es
      (registry g.table) (interpretation g.table.snapshot)
      (waiting g.live (registry g.table) (interpretation g.table.snapshot)) d step → Rule g es d step
  | tagged (yes : LocalRoute g.live g.table d) : Rule g es d (.selected yes.decl.id yes.kids)

theorem local_sound {p : Problem} {g : Global p}
    (h : Rule g es d (.selected key kids)) (checked : Checked (registry g.table))
    (covered : Coverage (registry g.table) (interpretation g.table.snapshot))
    (declared : Declared (registry g.table) d) (m : Assignment) (fit : ModelsExact p.current es m) :
    LocalNode (registry g.table) (interpretation g.table.snapshot) m d key kids ∧
      ∀ child ∈ kids, Declared (registry g.table) child := by
  cases h with
  | record original =>
    exact GeneralDeclarativeTaggedDictionary340.local_witness original checked covered declared fit
  | tagged direct => exact direct.meaning m fit.1

structure Branch {p : Problem} (g : Global p) (d : Demand) where
  decl : Declaration
  kids : List Demand
  sidecar : List Entry
  proves : ∀ es, sidecar ⊆ es → Rule g es d (.selected decl.id kids)
  fixed : List Equation
  meaning : ∀ path, (Fixed.mk path d fixed).Meaning p.current
  models : ∀ m : Assignment, Models p.current m → ModelsExact p.current sidecar m

inductive NodeCode where
  | record (w : GeneralDeclarativeWitnessRecordReplay350.Wire)
  | tagged (w : GeneralDeclarativeWitnessTagBranch352.Wire)

def read {p : Problem} (g : Global p) (path : List Nat) (d : Demand) :
    NodeCode → Option (Branch g d)
  | .record w => do
    let out ← replayNode (atNode p path d) g.canonical g.live w
    pure ⟨out.decl,out.kids,out.sidecar,
      fun _ wider => .record (.whole (extendSidecar out.selection wider)),
      out.fixed,out.meaning,out.models⟩
  | .tagged w => do
    let out ← GeneralDeclarativeWitnessTagBranch352.decode (atNode p path d) g.canonical g.live w
    pure ⟨out.decl,out.kids,[],fun _ _ => .tagged out,out.fixed,out.fixedMeaning,
      fun _m fit => ⟨fit,fun _ h => False.elim (List.not_mem_nil h)⟩⟩

structure Replayed {p : Problem} (g : Global p) (d : Demand) where
  tree : Tree
  sidecar : List Entry
  proof : ∀ es, sidecar ⊆ es → Resolves (Rule g es) d tree
  fixed : List Fixed
  fixedMeaning : ∀ f ∈ fixed, f.Meaning p.current
  exactIn : ∀ m : Assignment, Models p.current m → ∀ e ∈ sidecar, Holds m e

structure ReplayedList {p : Problem} (g : Global p) (ds : List Demand) where
  trees : List Tree
  sidecar : List Entry
  proof : ∀ es, sidecar ⊆ es → All₂ (Resolves (Rule g es)) ds trees
  fixed : List Fixed
  fixedMeaning : ∀ f ∈ fixed, f.Meaning p.current
  exactIn : ∀ m : Assignment, Models p.current m → ∀ e ∈ sidecar, Holds m e

mutual
inductive Code where
  | node (branch : NodeCode) (children : Codes)
inductive Codes where
  | nil
  | cons (first : Code) (rest : Codes)
end

mutual
def replayTree {p : Problem} (g : Global p) (path : List Nat) (d : Demand) :
    Code → Option (Replayed g d)
  | .node b cs => do
    let head ← read g path d b
    let tail ← replayList g path 0 head.kids cs
    pure ⟨.selected head.decl.id tail.trees,head.sidecar ++ tail.sidecar,
      (fun es covered => .selected (head.proves es (fun _ h => covered (List.mem_append_left _ h)))
        (tail.proof es (fun _ h => covered (List.mem_append_right _ h)))),
      ⟨path,d,head.fixed⟩ :: tail.fixed,
      (fun f h => (List.mem_cons.mp h).elim (fun eq => eq.symm ▸ head.meaning path) (tail.fixedMeaning f)),
      (fun m fit e x => (List.mem_append.mp x).elim
        (fun h => (head.models m fit).2 e h) (fun h => tail.exactIn m fit e h))⟩
termination_by c => sizeOf c

def replayList {p : Problem} (g : Global p) (path : List Nat) (idx : Nat) (ds : List Demand) :
    Codes → Option (ReplayedList g ds)
  | .nil =>
    match ds with
    | [] => some ⟨[],[],fun _ _ => .nil,[],fun _ h => False.elim (List.not_mem_nil h),
        fun _ _ _ h => False.elim (List.not_mem_nil h)⟩
    | _::_ => none
  | .cons one more =>
    match ds with
    | [] => none
    | d::ds => do
      let head ← replayTree g (path ++ [idx]) d one
      let tail ← replayList g path (idx+1) ds more
      pure ⟨head.tree :: tail.trees,head.sidecar ++ tail.sidecar,
        (fun es covered => .cons (head.proof es (fun _ x => covered (List.mem_append_left _ x)))
          (tail.proof es (fun _ x => covered (List.mem_append_right _ x)))),
        head.fixed ++ tail.fixed,
        (fun f x => (List.mem_append.mp x).elim (head.fixedMeaning f) (tail.fixedMeaning f)),
        (fun m fit e x => (List.mem_append.mp x).elim (head.exactIn m fit e) (tail.exactIn m fit e))⟩
termination_by c => sizeOf c
end

theorem resolves {p : Problem} {g : Global p} {d : Demand} (yes : Replayed g d) :
    Resolves (Rule g yes.sidecar) d yes.tree :=
  yes.proof _ (fun _ h => h)

theorem models {p : Problem} {g : Global p} {d : Demand} (yes : Replayed g d)
    (m : Assignment) (fit : Models p.current m) : ModelsExact p.current yes.sidecar m :=
  ⟨fit,yes.exactIn m fit⟩

end Yulang.GeneralDeclarativeWitnessMixedForest352
