import Yulang.ModuleScheduling
import Yulang.MethodResolutionLocality

/-!
# Selection snapshots produced by dependency-ready SCC compilation

`prepare` constructs a local snapshot from this SCC's source/key and the
completed artifacts of its ordered dependencies. `compile` then calls the
existing `MethodResolution.resolve` at every site. The arbitrary scheduler
actually passes artifacts produced earlier in its own execution to `prepare`;
neither the snapshots nor a common final store are supplied as assumptions.

Legality of a schedule and dependency-local purity of preparation imply equal
snapshots and selection answers for every two legal orders of the same nodes.
This advances the frozen-input locality theorem to a dependency DAG model.
It still does not extract SCCs from Yulang source or prove that the concrete
solver implements this pure preparation function with all dependencies known.
-/

namespace Yulang.MethodResolutionScheduling

open MethodResolution
open Methods (Selection)
open ModuleIncremental (Dependencies)
open ModuleScheduling (Store Legal canonical run)

universe u v
variable {Row : Type} {Export : Type u} {Source : Type v}

structure Snapshot (Row : Type) (Export : Type u) where
  exported : Export
  sites : List (Site Row)

structure Artifact (Row : Type) (Export : Type u) where
  snapshot : Snapshot Row Export
  answers : List (Selection Reference)

def compile (prepare : Source → List (Artifact Row Export) → Snapshot Row Export)
    (source : Source) (dependencies : List (Artifact Row Export)) : Artifact Row Export :=
  let snapshot := prepare source dependencies
  ⟨snapshot, snapshot.sites.map resolve⟩

def canonicalSnapshot (prepare : Source → List (Artifact Row Export) → Snapshot Row Export)
    (source : Nat → Source) (dependencies : Dependencies) (node : Nat) : Snapshot Row Export :=
  prepare (source node) ((dependencies node).map fun prior =>
    canonical (compile prepare) source dependencies prior.val)

theorem canonical_compiled (prepare : Source → List (Artifact Row Export) → Snapshot Row Export)
    (source : Nat → Source) (dependencies : Dependencies) (node : Nat) :
    canonical (compile prepare) source dependencies node =
      ⟨canonicalSnapshot prepare source dependencies node,
        (canonicalSnapshot prepare source dependencies node).sites.map resolve⟩ := by
  rw [ModuleScheduling.canonical_equation]
  rfl

def answerAt (artifacts : Store (Artifact Row Export)) (node position : Nat) : Option (Selection Reference) :=
  (artifacts node).bind fun artifact => artifact.answers[position]?

/-- Independent site-indexed selection judgment. An absent site has no
selected reference, while a present one uses the existing `Selects` rules. -/
def SelectsAt (snapshot : Snapshot Row Export) (position : Nat) (reference : Reference) : Prop :=
  ∃ site, snapshot.sites[position]? = some site ∧ Selects site reference

/-- Every legal execution computes its snapshots from its own dependency
artifacts and returns the canonical snapshot plus actual resolver outputs. -/
theorem run_artifacts_exact (prepare : Source → List (Artifact Row Export) → Snapshot Row Export)
    (source : Nat → Source) (dependencies : Dependencies) (order : List Nat)
    (legal : Legal dependencies [] order) :
    ∃ artifacts,
      run (compile prepare) source dependencies order (fun _ => none) = some (artifacts, order) ∧
      ∀ node ∈ order, artifacts node = some
        ⟨canonicalSnapshot prepare source dependencies node,
          (canonicalSnapshot prepare source dependencies node).sites.map resolve⟩ := by
  obtain ⟨artifacts, completed, valid⟩ := ModuleScheduling.run_legal (compile prepare) source dependencies
    [] order (fun _ => none) (ModuleScheduling.empty_exact (compile prepare) source dependencies) legal
  refine ⟨artifacts, completed, ?_⟩
  intro node member
  rw [valid node]
  simp only [List.mem_append, List.mem_reverse, List.not_mem_nil, or_false, member, ↓reduceIte,
    canonical_compiled]

theorem run_snapshots_and_answers (prepare : Source → List (Artifact Row Export) → Snapshot Row Export)
    (source : Nat → Source) (dependencies : Dependencies) (order : List Nat)
    (legal : Legal dependencies [] order) :
    ∃ artifacts,
      run (compile prepare) source dependencies order (fun _ => none) = some (artifacts, order) ∧
      ∀ node ∈ order,
        (artifacts node).map Artifact.snapshot = some (canonicalSnapshot prepare source dependencies node) ∧
        ∀ position, answerAt artifacts node position =
          ((canonicalSnapshot prepare source dependencies node).sites[position]?).map resolve := by
  obtain ⟨artifacts, completed, valid⟩ := run_artifacts_exact prepare source dependencies order legal
  refine ⟨artifacts, completed, ?_⟩
  intro node member
  constructor
  · simp only [valid node member, Option.map_some]
  · intro position
    simp only [answerAt, valid node member, Option.bind_some, List.getElem?_map]

/-- All successful selections, including the case where a site is absent,
are characterized by the original independent `Selects` judgment. -/
theorem run_selection_exact (prepare : Source → List (Artifact Row Export) → Snapshot Row Export)
    (source : Nat → Source) (dependencies : Dependencies) (order : List Nat)
    (legal : Legal dependencies [] order) :
    ∃ artifacts,
      run (compile prepare) source dependencies order (fun _ => none) = some (artifacts, order) ∧
      ∀ node ∈ order, ∀ position reference,
        answerAt artifacts node position = some (.unique reference) ↔
          SelectsAt (canonicalSnapshot prepare source dependencies node) position reference := by
  obtain ⟨artifacts, completed, valid⟩ := run_snapshots_and_answers prepare source dependencies order legal
  refine ⟨artifacts, completed, ?_⟩
  intro node member position reference
  rw [(valid node member).2 position]
  cases found : (canonicalSnapshot prepare source dependencies node).sites[position]? with
  | none => simp [SelectsAt, found]
  | some site => simp [SelectsAt, found, resolve_exact]

/-- The common table contains equal exported values, equal receiver/scope/
fallback facts, and equal missing/unique/ambiguous answers. These snapshots
are computed during execution, not required to agree before execution. -/
theorem schedule_independent (prepare : Source → List (Artifact Row Export) → Snapshot Row Export)
    (source : Nat → Source) (dependencies : Dependencies) (first last : List Nat)
    (firstLegal : Legal dependencies [] first) (lastLegal : Legal dependencies [] last)
    (sameNodes : ∀ node, node ∈ first ↔ node ∈ last) :
    ∃ artifacts,
      run (compile prepare) source dependencies first (fun _ => none) = some (artifacts, first) ∧
      run (compile prepare) source dependencies last (fun _ => none) = some (artifacts, last) ∧
      ∀ node ∈ first,
        (artifacts node).map Artifact.snapshot = some (canonicalSnapshot prepare source dependencies node) ∧
        ∀ position, answerAt artifacts node position =
          ((canonicalSnapshot prepare source dependencies node).sites[position]?).map resolve := by
  obtain ⟨artifacts, firstRun, lastRun⟩ := ModuleScheduling.schedule_independent
    (compile prepare) source dependencies first last firstLegal lastLegal sameNodes
  obtain ⟨computed, computedRun, values⟩ := run_snapshots_and_answers prepare source dependencies first firstLegal
  have same : artifacts = computed := (Prod.mk.inj (Option.some.inj (firstRun.symm.trans computedRun))).1
  subst computed
  exact ⟨artifacts, firstRun, lastRun, values⟩

theorem scheduled_once (prepare : Source → List (Artifact Row Export) → Snapshot Row Export)
    (source : Nat → Source) (dependencies : Dependencies) (order : List Nat)
    (legal : Legal dependencies [] order) (count : Nat) (within : ∀ node ∈ order, node < count) :
    ∃ artifacts calls,
      run (compile prepare) source dependencies order (fun _ => none) = some (artifacts, calls) ∧
      calls = order ∧ calls.Nodup ∧ calls.length ≤ count :=
  ModuleScheduling.run_once_bound (compile prepare) source dependencies order legal count within

end Yulang.MethodResolutionScheduling
