import Yulang.GeneralDeclarativeWitnessStopped334

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessReobserve334
open GeneralDeclarations (Registry Declaration Checked)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeOrigins321 (Supported restriction backed_iff)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativeWitnessHead334 (Slice Argument Actuals)
open GeneralDeclarativeWitnessNode334 (Witness Generation)
open GeneralDeclarativeWitnessClassify334 (Rule selected_to_old)
open GeneralDeclarativeWitnessStopped334 (Retained selected_receipt)
open GeneralDeclarativeCurrentReceipt330 (Receipt complete)
open GeneralDeclarativeStableAttempt329 (Elected)
open GeneralDeclarativeInlineEndpoint331 (candidates)
open GeneralDeclarativeGrowth327 (Extends trans boundsOne derives)
open GeneralDeclarativeObserverGrowth330 (trace)
open GeneralDeclarativeInlineGrowth331 (extend)
open GeneralDeclarativeArityPlan330 (grow)
open CommonRoleOutermostResolver (All₂ Tree Dictionary Summarizes Classify)

/-- A usable observation embedding carries ordinary visibility and
source visibility separately. Old and new completion predicates need
not coincide; only actual usable reads must be retained. -/
structure ReaderGrowth {s t : State} (p : Supported s a) (q : Supported t b) : Prop where
  ordinary : Extends s t
  origins : ∀ row origin, p.derivesFrom row origin → q.derivesFrom row origin
  complete : ∀ n, a n → b n

/-- Re-base the old source evidence at the new completion predicate
without relabelling any old row or promoting unsupported writes. A prior
slice need only embed the rows it actually used in the earlier current
source view. To avoid demanding provenance for newly completed rows
outside that set, the reindexed base keeps just previously usable
origins; the old owner is still the owner in the new completion. -/
def keptBase {s : State} (p : Supported s a) (b : Nat → Prop) : Supported s b where
  derivesFrom := fun row origin => p.derivesFrom row origin ∧
    GeneralDeclarativeOrigins321.Available a origin
  ordinary := fun known => p.ordinary known.1

theorem kept_grows {s : State} (p : Supported s a) (more : ∀ n, a n → b n) :
    Extends (restriction p) (restriction (keptBase p b)) := by
  refine ⟨fun _ h => h,fun _ h => h,?_⟩
  intro row held
  obtain ⟨origin,known,ready⟩ := (backed_iff p row).mp held
  apply (backed_iff (keptBase p b) row).mpr
  refine ⟨origin,⟨known,ready⟩,?_⟩
  cases ready with
  | source => exact .source
  | completed old => exact .completed (more _ old)

theorem keeps_current {s t : State} {p : Supported s a} {q : Supported t b}
    (h : ReaderGrowth p q) (prior : Slice p) :
    Extends (restriction (keptBase prior.support b)) (restriction q) := by
  refine ⟨fun _ seen => h.ordinary.constraints (prior.allowed.constraints seen),
    fun _ seen => h.ordinary.intervals (prior.allowed.intervals seen),?_⟩
  intro row held
  obtain ⟨origin,⟨known,old⟩,_⟩ := (backed_iff (keptBase prior.support b) row).mp held
  have inBefore := prior.allowed.equations ((backed_iff prior.support row).mpr ⟨origin,known,old⟩)
  obtain ⟨proved,fromHere,ready⟩ := (backed_iff p row).mp inBefore
  apply (backed_iff q row).mpr
  refine ⟨proved,h.origins _ _ fromHere,?_⟩
  cases ready with
  | source => exact .source
  | completed owner => exact .completed (h.complete _ owner)

theorem swap_argument {s : State} {p : Supported s a} {z : Supported s b}
    (reads : Extends (restriction p) (restriction z))
    (old : Argument p c i keep before arg pat after spans) :
    Argument z c i keep before arg pat after spans := by
  cases old with
  | named one =>
    obtain ⟨code,seen,printed,old,located⟩ := one.reads
    exact .named ⟨one.args,code,seen,printed,trace reads old,located⟩
  | inline fit code held computed => exact .inline fit code (extend reads held) computed
  | projected fit code held => exact .projected fit code (grow reads held)

theorem swap_heads {s : State} {p : Supported s a} {z : Supported s b}
    (reads : Extends (restriction p) (restriction z))
    (old : Actuals p c i keep before args pats after spans) :
    Actuals z c i keep before args pats after spans := by
  induction old with
  | nil => exact .nil
  | cons first _ last => exact .cons (swap_argument reads first) last

/-- The ordinary receipt remains valid under new admitted ordinary
rows; this does not promote any of those rows to source support. -/
theorem receipt_grows {s t expected : State} (h : Extends s t) (r : Receipt expected s) :
    Receipt expected t :=
  ⟨fun _ seen => h.constraints (r.constraints seen),
    fun _ seen => boundsOne h (r.intervals _ seen),fun _ seen => derives h (r.rows _ seen)⟩

/-- Source-slice transport across monotone completion and recorded-origin growth.
The selected receipt replay
keeps the identical initial snapshot, the actual names and targets,
and the exact ordered list returned by compileBody. -/
def rebase {s t : State} {p : Supported s a} {q : Supported t b}
    (h : ReaderGrowth p q) (g : Generation p r i d impl kids) : Generation q r i d impl kids where
  slice := ⟨g.slice.base,keptBase g.slice.support b,trans g.slice.ordinary h.ordinary,
    keeps_current h g.slice⟩
  protect := g.protect
  fallback := g.fallback
  targets := g.targets
  named := g.named
  spans := g.spans
  source := swap_heads (kept_grows g.slice.support h.complete) g.source
  ordinary := g.ordinary
  compiled := g.compiled
  receipt := receipt_grows h.ordinary g.receipt

theorem rebase_literal {s t : State} {p : Supported s a} {q : Supported t b}
    (h : ReaderGrowth p q) (g : Generation p r i d impl kids) :
    (rebase h g).ordinary = g.ordinary ∧ (rebase h g).spans = g.spans ∧
      (rebase h g).targets = g.targets ∧ (rebase h g).named = g.named :=
  ⟨rfl,rfl,rfl,rfl⟩

/-- The replay format carries per-node emitter receipts from possibly
different ordinary snapshots, but gives no credit for a historical
election. Current election is checked with the actual current support
and same ordered requests. -/
inductive Journal {t : State} (q : Supported t a) (r : Registry) (i : Interpretation)
    (waiting : Demand → Declaration → Prop) : Demand → Tree → Prop
  | node {s : State} {beforeDone : Nat → Prop} {p : Supported s beforeDone} :
      ReaderGrowth p q → Generation p r i d impl kids →
      Elected t r i q (candidates q r i waiting) d impl →
      All₂ (Journal q r i waiting) kids children →
      Journal q r i waiting d (.selected impl.id children)

section
variable {t : State} {q : Supported t b} {r : Registry} {i : Interpretation}
variable {waiting : Demand → Declaration → Prop}

mutual
theorem current (checked : Checked r) (coverage : Coverage r i)
    (d : Demand) (tree : Tree) (declared : Declared r d)
    (entry : Journal q r i waiting d tree) : Retained q r i waiting d tree := by
  cases entry with
  | node growth saved now each =>
    let w : Witness q r i waiting _ _ _ := ⟨rebase growth saved,now⟩
    obtain ⟨frame,_,_,_⟩ := w.frame checked coverage declared
    have demanded := (complete checked coverage now.viable.1.1 now.viable.1.2 declared frame w.receipt).2.2
    exact .node w.toGeneration now.viable.1.1 (selected_to_old checked coverage declared (.selected w))
      (current_children checked coverage _ _ demanded each)
termination_by sizeOf tree

theorem current_children (checked : Checked r) (coverage : Coverage r i)
    (ds : List Demand) (ts : List Tree) (declared : ∀ d ∈ ds, Declared r d)
    (entries : All₂ (Journal q r i waiting) ds ts) : All₂ (Retained q r i waiting) ds ts := by
  cases entries with
  | nil => exact .nil
  | cons node tail =>
    exact .cons (current checked coverage _ _ (declared _ List.mem_cons_self) node)
      (current_children checked coverage _ _ (fun _ h => declared _ (List.mem_cons_of_mem _ h)) tail)
termination_by sizeOf ts
end

theorem successful_reobserve (checked : Checked r) (coverage : Coverage r i)
    (declared : Declared r d) (saved : Journal q r i waiting d tree) (out : Summarizes tree (.selected dict)) :
    Classify (Rule q r i waiting) d (.selected dict) ∧
      ∀ m, Models t m → Evidence r i m d dict :=
  selected_receipt checked coverage declared (current checked coverage _ _ declared saved) out

end
end Yulang.GeneralDeclarativeWitnessReobserve334
