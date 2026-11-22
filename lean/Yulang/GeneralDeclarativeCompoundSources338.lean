import Yulang.GeneralDeclarativeCompoundTree338
import Yulang.GeneralDeclarativeCompoundReadback338

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCompoundSources338
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeGrowth327 (Extends fits aliases trans)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeRecordSpine330 (Spine)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeInlineSpine331 (Closed)
open GeneralDeclarativeLowerKnown321 (Alias alias_refl)
open GeneralDeclarativeObserverGrowth330 (spine)
open GeneralDeclarativeExactSupport337 (endpointRows)
open GeneralDeclarativeEndpointOverlay336 (Entry)
open GeneralDeclarativeEndpointProgram336 (from_supported)
open GeneralDeclarativeCompoundEndpoints338 (from_row from_visible)
open GeneralDeclarativeCompoundPattern338 (peel layout layout_labels)
open GeneralDeclarativeCompoundBatch338 (Ticket minted minted_bounds authored_row)
open GeneralDeclarativeCompoundReadback338 (operandLow operandHigh stored_low stored_high)
open GeneralDeclarativeCompoundRoutes338 (dispatch_exact route)
open GeneralDeclarativeCompoundTree338 (World advance advance_grows Tree Forest Span Sound tree_exact)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarationPatterns (Pattern)
open CommonRoleCanonicalRows (normalize residual)

def Anchored (s : State) (n : Nat) (e : Expr) : Prop :=
  ∃ recorded, Alias s n recorded ∧ (⟨recorded,e⟩ : Equation) ∈ s.equations

def Anchors (s : State) (a : Capture) (lo hi : Expr) : Prop :=
  Anchored s a.lower lo ∧ Anchored s a.upper hi

theorem anchored_grows {s t : State} (grown : Extends s t) (found : Anchored s n e) : Anchored t n e := by
  obtain ⟨a,b,c⟩ := found
  exact ⟨a,aliases grown b,grown.equations c⟩

theorem anchors_grow {s t : State} (grown : Extends s t) (found : Anchors s n a b) : Anchors t n a b :=
  ⟨anchored_grows grown found.1,anchored_grows grown found.2⟩

theorem spine_alias {s : State} (e : Spine s n fs ending) (a : Alias s j n) : Spine s j fs ending := by
  cases e with
  | width link row => exact .width (.trans a link) row
  | exactEnd link row => exact .exactEnd (.trans a link) row
  | cons link row tail => exact .cons (.trans a link) row tail
  | inline link endProof row => exact .inline (.trans a link) endProof row
  | prefixed link row chain => exact .prefixed (.trans a link) row chain

theorem closed_grows {s t : State} (grown : Extends s t) (seen : Closed s e fs ending) :
    Closed t e fs ending := by
  induction seen with
  | terminal endProof => exact .terminal endProof
  | field _ ih => exact .field ih
  | name old => exact .name (spine grown old)

theorem anchored_spine {s : State} (f : Anchored s n e) (observed : Closed s e fs ending) :
    Spine s n fs ending := by
  obtain ⟨_,linked,row⟩ := f
  exact spine_alias (from_row row observed) linked

/-- Paired independent endpoint endProof. No actual center, jobs, slot
addresses, compiler receipt, or satisfying model is an index of this
judgment. All payload descendants are read through precisely the
literal source field after first-label visibility. -/
inductive Source (s : State) : Expr → Expr → Pattern → Prop where
  | binder : Source s lo hi (.var n)
  | record :
      peel pat = (fs,tail) → fs ≠ [] → (fs.map Prod.fst).Nodup →
      Closed s lo lower loEnd → Closed s hi upper hiEnd →
      (∀ k ∈ fs.map Prod.fst, ∃ payload, (k,payload) ∈ normalize lower) →
      (∀ k ∈ fs.map Prod.fst, ∃ payload, (k,payload) ∈ normalize upper) →
      (∀ f ∈ fs, ∀ a b, (f.1,a) ∈ normalize lower → (f.1,b) ∈ normalize upper → Source s a b f.2) →
      Source s (withTail (residual (fs.map Prod.fst) (normalize lower)) loEnd)
        (withTail (residual (fs.map Prod.fst) (normalize upper)) hiEnd) tail →
      Source s lo hi pat

theorem minted_valid {w : World done} (t : Ticket w.source a f)
    (active : e ∈ minted w.state w.reads keep t.jobs) :
    Bounds (advance w t keep).state e.2 :=
  fits (GeneralDeclarativeGrowth327.facts _ _) (minted_bounds active)

theorem minted_anchors {w : World done} (t : Ticket w.source a f)
    (active : e ∈ minted w.state w.reads keep t.jobs) :
    Anchors (restriction (advance w t keep).source) e.2 (operandLow e.1) (operandHigh e.1) :=
  ⟨⟨_,alias_refl _,authored_row t active (stored_low e)⟩,⟨_,alias_refl _,authored_row t active (stored_high e)⟩⟩

theorem pull_tasks {start : World done} {keep : List Nat} {tasks : List (Entry × Pattern)}
    (run : ∀ task ∈ tasks, ∀ w : World done, start.Grows w →
      ∃ v uses, Tree keep w task.1.2 task.2 v uses) :
    ∃ v uses, Forest keep start tasks v uses := by
  suffices aux : ∀ (tasks : List (Entry × Pattern)),
      (∀ task ∈ tasks, ∀ w : World done, start.Grows w → ∃ v uses, Tree keep w task.1.2 task.2 v uses) →
      ∀ current : World done, start.Grows current → ∃ v uses, Forest keep current tasks v uses by
    exact aux tasks run start (GeneralDeclarativeCompoundTree338.identity start keep).1
  intro ts
  induction ts with
  | nil => exact fun _ w _ => ⟨w,[],.nil⟩
  | cons task tail ih =>
    intro read w grows
    obtain ⟨mid,head,step⟩ := read task List.mem_cons_self w grows
    have move := (tree_exact step).1.1
    obtain ⟨v,rest,later⟩ := ih (fun t h => read t (List.mem_cons_of_mem _ h)) mid
      (GeneralDeclarativeCompoundTree338.together grows move)
    exact ⟨v,head++rest,.cons step later⟩

def Producer (src : State) (lo hi : Expr) (pat : Pattern) : Prop :=
  ∀ {done : Nat → Prop} (w : World done) (keep) (arg : Capture),
    Extends src (restriction w.source) → Anchors (restriction w.source) arg lo hi →
    Bounds w.state arg → ∃ v used, Tree keep w arg pat v used

theorem run_record {src : State} {lo hi : Expr}
    (split : peel pat = (fs,tail)) (nonempty : fs ≠ []) (distinct : (fs.map Prod.fst).Nodup)
    (left : Closed src lo lower loEnd) (right : Closed src hi upper hiEnd)
    (loSeen : ∀ k ∈ fs.map Prod.fst, ∃ x, (k,x) ∈ normalize lower)
    (hiSeen : ∀ k ∈ fs.map Prod.fst, ∃ x, (k,x) ∈ normalize upper)
    (kids : ∀ f ∈ fs, ∀ a b, (f.1,a) ∈ normalize lower → (f.1,b) ∈ normalize upper →
      Producer src a b f.2)
    (rest : Producer src (withTail (residual (fs.map Prod.fst) (normalize lower)) loEnd)
       (withTail (residual (fs.map Prod.fst) (normalize upper)) hiEnd) tail) :
    Producer src lo hi pat := by
  intro done w keep arg source sourceNames valid
  have lo := anchored_spine sourceNames.1 (closed_grows source left)
  have hi := anchored_spine sourceNames.2 (closed_grows source right)
  rw [← layout_labels fs] at distinct loSeen hiSeen
  obtain ⟨first,last,read⟩ := from_visible valid distinct lo hi loSeen hiSeen
  obtain ⟨jobs,computed⟩ := from_supported read fs.length
  let t : Ticket w.source arg fs := ⟨lower,upper,first,last,loEnd,hiEnd,jobs,read,computed⟩
  obtain ⟨tasks,finish,dispatched,_,receipts⟩ := route (old := w.reads) (keep := keep) t
  let stage := advance w t keep
  have stageSrc : Extends src (restriction stage.source) :=
    GeneralDeclarativeGrowth327.trans source (advance_grows t keep).2.2
  have taskReady : ∀ task ∈ tasks, ∀ next : World done, stage.Grows next →
      ∃ v uses, Tree keep next task.1.2 task.2 v uses := by
    intro task listed next grows
    obtain ⟨f,fHere,equal,readLo,readHi⟩ :=
      GeneralDeclarativeCompoundReadback338.child_operands t dispatched listed
    have mintedHere : task.1 ∈ minted w.state w.reads keep t.jobs := by
      rw [receipts]
      exact List.mem_append_left _ (List.mem_map.mpr ⟨task,listed,rfl⟩)
    have auth := anchors_grow grows.2.2 (minted_anchors t mintedHere)
    exact equal.symm ▸ kids f fHere _ _ readLo readHi next keep task.1.2
      (GeneralDeclarativeGrowth327.trans stageSrc grows.2.2) auth
      (fits grows.1 (minted_valid t mintedHere))
  obtain ⟨beforeTail,front,proof⟩ := pull_tasks taskReady
  have tailGrows := (GeneralDeclarativeCompoundTree338.forest_exact proof).1.1
  have tailMinted : finish ∈ minted w.state w.reads keep t.jobs := by
    rw [receipts]
    exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨tailLo,tailHi⟩ := GeneralDeclarativeCompoundReadback338.tail_recipe t tailMinted (dispatch_exact dispatched).2.2.2
  have anchored := anchors_grow tailGrows.2.2 (minted_anchors t tailMinted)
  rw [tailLo,tailHi] at anchored
  obtain ⟨endState,back,tailRead⟩ := rest beforeTail keep finish.2
    (GeneralDeclarativeGrowth327.trans stageSrc tailGrows.2.2) anchored
    (fits tailGrows.1 (minted_valid t tailMinted))
  exact ⟨endState,front++back,.record t nonempty split dispatched proof tailRead⟩

/-- Construct actual executable route steps from independently
supported endpoint expressions for the full finite nested record
fragment. The proof recurs over the input source judgment. -/
theorem compile (seen : Source src lo hi pat) : Producer src lo hi pat := by
  induction seen with
  | binder => exact fun _ _ _ _ _ ready => ⟨_,_,.binder ready⟩
  | record split nonempty distinct lo hi l h _ _ ihKids ihTail =>
    exact run_record split nonempty distinct lo hi l h ihKids ihTail

theorem exact {w : World done} (seen : Source (restriction w.source) lo hi pat) (keep : List Nat)
    (anchors : Anchors (restriction w.source) arg lo hi) (bounds : Bounds w.state arg) :
    ∃ final uses, Tree keep w arg pat final uses ∧
      GeneralDeclarativeCompoundTree338.TreeExact keep w pat final uses := by
  obtain ⟨endState,uses,witness⟩ := compile seen w keep arg
    (GeneralDeclarativeClauseBatch327.reflexive _) anchors bounds
  exact ⟨endState,uses,witness,tree_exact witness⟩

end Yulang.GeneralDeclarativeCompoundSources338
