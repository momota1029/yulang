# Inference cutover: public API disposition inventory

Date: 2026-10-05. Frozen baseline: `a674fcf72`, branch
`research/simple-sub-intrusion`. Research inventory only; no successor API,
removal, freezing, canonical form, or implementation decision is selected.
All line locators below refer to that commit, not the changing working tree.

## Scope, method, and authority

M0 inventory artifact: independently reviewed by `regression_auditor` with no
blocking, major, or minor findings in exported-surface and workspace-consumer
coverage. Read committed Rust declarations, reexports, manifests, symbol and
call references, and focused tests. Verification budget is one output-only
`git diff --check`; no Cargo/build/test command or performance measurement.
Source and `tasks/current.md` were read with `git show a674fcf72:<path>`;
uncommitted task edits are not authority. External consumers and semantic
compatibility remain unverified; no API disposition is selected.

Classification:

- **A**: public Rust observation/construction contract. Preserve compatibility
  or intentionally version it through a later approved gate; this inventory
  does not select between those dispositions.
- **B**: hidden F5 representation, replaceable after governing proof/design
  gates while preserving the required observations it currently produces.
- **C**: test/research-only owner or observation. Preserve useful behavioral
  witnesses separately from representation assertions.
- **D**: unresolved authority/consumer identity. A public surface remains A
  even when external ecosystem use is unknown.

Governing sources inspected:

- `rules/design-authority.md`, `rules/orchestration-budget.md`,
  `rules/git-concurrency.md`.
- Committed `tasks/current.md`, Objective/Closed decisions: final supported
  well-typed capability and soundness/principality gates. Bounded experiments
  do not authorize production inference replacement.
- `notes/design/2026-09-20-directed-subtyping-integer-slice-draft.md`,
  Proposed first slice / Fact-authority registry / Required invariants.
- `notes/design/2026-09-21-oracle-aligned-f4-int-scheme-scc-draft.md`, §§3–5,
  §§12–13 public-path/counter obligations, and
  `notes/design/2026-09-21-f4-fact-store-counter-visibility-addendum.md`.
- `notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md`,
  public observation/term-lifetime/diagnostic amendments and §44 representative
  fact; `notes/design/2026-09-22-f5b-closed-finalization-term-owner-draft.md`,
  §§3–6 term transfer/clone/admission obligations.
- `notes/design/2026-10-04-scc-intrusion-cross-edit-rebuild-addendum.md`,
  Decision / Interface comparison boundary / Compatibility and gate.

The successor objective permits replacing F5's closed-scheme architecture.
That does not make an already exported Rust observation private. A language
acceptance contract and a public Rust shape are separate; `pub` alone proves
neither approved successor semantics nor a policy to freeze the current shape.
Current scoped Authoritative API obligations must be considered explicitly
when a later transition changes the surface.

## Workspace consumers and visibility

`yu-solver` is a normal library, version `0.1.0`, with `publish = false`
(`crates/yu-solver/Cargo.toml:1–17`). Five term types are root-reexported at
`crates/yu-solver/src/lib.rs:278`; all other public types below are directly
declared at the root. Module paths `term`, `scc` and the F5c modules are private.
No exported solver type is `#[doc(hidden)]` or `#[non_exhaustive]`. Public
enums permit exhaustive matches and construction of their public variants.
Struct fields are private; the unit `ArtifactMismatch` is constructible.
Traits, receiver/borrow lifetimes and result types are observable Rust shapes.

Pinned workspace search found **no Rust inference consumer outside
`crates/yu-solver`** and **no other manifest depending on `yu-solver`**.
`Cargo.toml:8` lists the package. `tools/xtask/src/main.rs:254,303,309` lists its
graph level and planned graph edges; the planned `yu-core -> yu-solver` edge
is tooling policy, not a current Rust call. `crates/yu-core/Cargo.toml:7` has
an empty dependency section. No committed solver integration-test, example or
benchmark directory exists at this revision. `Cargo.lock:802` is metadata.
External path/git consumers and users outside this workspace remain
**D/unknown**; `publish = false` does not establish their absence.

Signatures expose `yu_hir::{HirModule,HirOccurrenceId,DefinitionRootId}` and
`yu_types::{Leaf,ComponentKind}`. These names are used, not reexported by
`yu_solver`; their own contracts are dependencies, outside this owning-crate
declaration inventory. The final sections give every exported declaration and
a pinned source call-map. Shared-name method receiver attribution is explicitly
D where lexical search alone cannot establish its type.

## Public surface disposition

All 30 exported types, their listed explicit methods, 240 macro-generated
counter methods, 13 deprecated counter methods and public traits are **A**.
Their hidden backing state may separately be B. No type's absence of a local
production caller turns it into C.

| Family | Current observable contract | Classification boundary |
|---|---|---|
| `SolvedModule` | Artifact-bound frozen result; solve/hir/occurrences/errors/store/counters/projection_for/root_value_for | A wrapper/observations; private closed arena, schemes, maps and route records B |
| `ConstraintBatch` | collect/Clone/hir/ordered source occurrences/term lookup/component/root queries/counters | A; collection recipes, SCC plan and indexes B |
| `ConstraintStore`, `ConstraintTransaction` | from_batch/exclusive transaction/admit/separate record_provenance/read facts/provenance/term observations/counters | A; hash maps, allocation lanes and private route journal B |
| `Term`, `TermView`, `LiveVariableView`, `Polarity`, `TermLookupError` | Opaque copyable/hashable lineage handles, owner-borrowed exhaustive algebra, live-row ordinals, polarity, four Function ports, mismatch errors | A despite F5-specific representation observations; allocator/pages/TermNode B |
| Component/occurrence/cause/fact/receipt/provenance identity types | Artifact/source identity, ordered directed endpoints, canonical FactId, source cause separate from semantic key, exact-store single-consumption receipt | A; constructors of opaque structs and receipt tokens private/B |
| Projection/error enums and structs | Exhaustive variants, exact occurrence/cause/error kinds, Int/Unknown/Never and Empty/Unknown projections, structured availability failures | A; no complete public Function scheme result |
| `ProductionCounters` | Snapshot type/traits, exact accessor names and meanings, deprecated zeroes | A; private backing lanes B, test-only observation hooks C |

`ConstraintTransaction` has no public commit/abort/savepoint method. Its public
`admit` acts on the borrowed store immediately; the name does not promise a
deferred general transaction mechanism. Admission and separate provenance
consumption are distinct public operations. Private per-route transaction
atomicity must not be silently attributed to every use of the public wrapper.

The public `From<ConstraintError>` implementation at `lib.rs:3686–3697` maps
alien/consumed receipts to ReceiptMismatch, identity failures to
IdentityExhausted, and regards CrossKind as unreachable local error rather than
availability failure. Error enum traits/exhaustiveness and this conversion are
part of the public shape; no new availability semantics is selected here.

## Compatibility hidden behind SolvedModule

The following compatibility observations could be lost if private F5 storage
were removed without an explicit wrapper/API transition.

| Observation | Owning baseline locators in lib.rs unless stated | Focused dependency witnesses |
|---|---|---|
| Retain exact Arc<HirModule>, identity and deterministic total occurrence order including error/unsupported nodes | 7168, 15419, 15668–15675 | exact relations 18719; alpha/path order 18750; Unknown states 20112 |
| Owned occurrence lookup is total; foreign ID rejected; an owned unrepresented occurrence returns Unknown/Unknown | 15693–15707; finish 15419–15479 | Unknown intervals 20112; foreign/root/component witness 20685 |
| Exact integer and empty effect remain distinct from Unknown; supported Name/lambda effects and unsupported cases retain scoped outcomes | 15419–15479 | Name slots/order 18069; identity Function facts 20282; constant/name lambdas 20375; ineligible lambda with independent integer 20415 |
| Root projection reads the finalized scheme: Int→Int, Bottom→Never, quantified/recursive/Function/Union→Unknown | 15708–15748 | finalized roots 18792; unconstrained/error roots 17591; self/mutual cycles 18048; productive/unproductive Function recursion 20476 |
| Ordinary Never is not an error fallback; local failures permit independent components to solve | 3621–3630, 9731–9739 | local CrossKind 17778; brands/local failures 20820; independent source states 20112 |
| Errors preserve direct occurrence/cause and canonical first mismatch; diagnostic order follows direct fact admission | 3645–3677; F5 diagnostic amendments | mismatch order 21580; duplicate replay 21483; canonical kind/field order 21744; cyclic nearest-terminal witnesses 21851 |
| Frozen store exposes directed facts, IDs/order, source provenance and term observations | 15677–15679, 3393–3401, 2842–2909 | exact relations 18719; routed slot zero order 18069; exact per-use cause 17620; duplicate causes and receipt ownership 20820 |
| Public store is not a complete scheme/constraint interface: F5 §44 exposes only the first normalized Union member as a representative, keeping other members private | F5 design §44 | representative atomicity 28998; private member availability rollback 29231; incoming normalized members 27064 |
| Batch consumption/clone keeps collected opaque Term handles and lineage; independent branches/receipts stay isolated | 2971–2973; term.rs:729–764; term-owner amendment §§3/6 | lookup transfer 20726; disjoint postprefix pages 20790; foreign/absent handle 20685/20770 |
| TermView borrows its owner; no public interner/construction or view lifetime extension | term.rs:67–194; lib.rs:278 | compile-fail/trait probes term.rs:68–108; exhaustive-view probe term.rs:156–167 |
| Availability failure returns no module, with no partial/mixed publication | 15665–15667, 15419–15662 | foreign before publication 17744; receipt/identity failure 17826; finalization exhaustion 17848/17927; runtime reserve failure 22236 |
| Root/batch queries alter private atomic counts reflected in later snapshots; batch/solved counters return copies, store counters borrow | 1378–1401, 15680–15691, 15708–15732, 3399–3401 | F2 query probes 19354; clone counter contract 19521; scale helper 16600 |
| Deprecated finish-projector accessors return zero, never new measurements under old names | 2521–2580 | obsolete-accessor witness 17944 |

`root_value_for == Unknown` is not a public complete Function type; no public
`scheme_for`, generalized-interface getter, or cross-edit equality method
exists. Current research reconstruction consumes retained Function term ports
and linked store facts: `tests/research_function_realization.rs:426,456,461–489,1241`.
Those helpers do not establish whole-carrier denotation/interface completeness.

These are baseline observations/current scoped contracts. The successor's
waived inference-stage printing/phase parity does not decide retirement of the
Rust projection API or counter surface. An intentional change needs a recorded
disposition rather than fixture edits to match a replacement.

## Hidden and research boundaries

| Family | Class | Visibility / dependencies |
|---|---|---|
| InferenceSession, value/effect bounds, levels/non_generic metadata, pair/diagnostic memo, route journal and scratch | B | Private types, session starts near lib.rs:7204; solve() remains the public entry. Scoped semantics, live internal uses/barriers and atomic publication survive replacement of storage. |
| Closed arena/schemes/root positions/routed uses in SolvedModule | B | Private fields lib.rs:7172–7183; imported yu-types types not solver reexports; tests inspect them directly. No public scheme query. |
| DefinitionOrderId, CollectedDefinition/BodyStatus, DefinitionUseId/Cause/Use, CollectionLookupError | B | pub(crate) lib.rs:460–645; batch records/identity queries 1260–1289 pub(crate); opaque scheduling owners, not external API. |
| SccComponentId, SccPlan, batch SCC query family | B | Private scc module, pub(crate)/pub(super) owners; batch queries 1309–1376 pub(crate). Their data topology is not a successor requirement. |
| TermNode/Builder/Lineage/BranchTermArena/brands/pages and reserve/accounting lanes | B | Private or pub(crate). Public Term/TermView exposes selected results without exposing allocator/storage mutation. |
| F5c draft/generalization/normalization/substitution/materialization/replay/tree analysis modules | B | Private module paths at lib.rs:213–268. Public yu-types capability APIs require a separate owning-crate audit. |
| intrusion_transport module and finite parent/use overlay | C | Whole module cfg(test), lib.rs:211–212; no root reexport/production routing. Tests in src/tests/intrusion_transport.rs. |
| OrderingObserver/ExecutionEvent/SummaryObservation, ledgers/fault injection/capture hooks, synthetic batches/test term builder | C | cfg(test)/private owners. Internal tests can see representation unavailable to downstream consumers. |
| f5c_resource_probe and incoming_sample_trace hooks | C | Probe feature forwards a yu-types probe feature; solver hooks cfg(test) or cfg(all(test,feature)), not production public inference exports. |
| research_function_realization helpers | C consuming A/B | Retained store/term observations plus private metadata; research characterization, not a complete generalized public scheme. |
| External ecosystem and same-name receiver attribution | D | No local production consumer found. Locator appendix is a complete lexical candidate map, explicitly not typed receiver certification. |

## ProductionCounters contract boundary

The macro at lib.rs:2277 and invocation at 2279–2520 generates 240 public
`const fn accessor(&self) -> usize` methods. Thirteen explicit deprecated
methods return zero. Every method is listed individually below. Private fields
are B even when an owning test reads them directly; those direct private reads
are not public API calls.

Capacity/retained-byte fields model `capacity * size_of::<slot>()`, excluding
allocator metadata/control bytes/fragmentation (lib.rs:1962–1964). F4 §§12–13
explicitly preserve prior accessor names and meanings, including obsolete
deprecated zeroes. Successor counter replacement, compatibility adapters or
retirement are later design decisions. Do not silently repurpose names.
`fact_store_rebuilds` is a deliberate B boundary: no public accessor; it feeds
public `constraint_store_rebuilds` under the Authoritative visibility addendum.
Not every private F5b/F5c resource lane is an exported counter.

## Complete generalized interface / invalidation boundary

The cross-edit addendum allows rebuilding changed inference components. It
permits stopping downstream **inference** invalidation only after unchanged
**complete generalized canonical interface**, with dependent other inputs also
unchanged. The interface/equality must preserve every downstream-observable
generalized constraint, coupled effect, scope relationship and required evidence.

Fields, canonical form/equality, granularity, dependencies, SCC split/merge and
changed enclosing environments are open. Code-generation/non-inference artifact
reuse needs separate invalidation authority. This addendum grants no current
production implementation authority.

Neither the Int/Never/Unknown root summary, occurrence projections, F5 arena
identity nor representative public fact store is a proved complete canonical
interface. F5 §44's private Union constraints, quantifier/recursive sharing,
effects/scopes and required evidence can survive without appearing in that
summary/store. Comparing every public fact therefore does not itself close the
interface proof. SolvedModule is frozen for one exact HIR artifact, not an
editor inference cache.

The representation gate must define the interface/public compatibility boundary,
prove its equality/dependency relation and rebuild atomicity, and cover a body
edit with unchanged interface, changed interface, SCC split/merge, changed
enclosing non-generic state and reconstruction failure. These remain D/open;
this inventory does not choose an API or comparison algorithm.

## Declaration and exact locator appendices

All following locators use the frozen revision. Reproduce source with
`git show a674fcf72:<path>`. All committed Rust files under crates/tools were
searched. Method call rows include receiver calls and associated references,
including method pointers; multiline calls anchor the method token.

Shared selectors such as occurrence/kind/id/value/hir/occurrences/counters and
term_view are **lexical supersets**, including private/HIR/yu-types same-name
methods. Receiver identity for such candidates is D until narrow consumer
inspection. Unique solver API selectors and owner-qualified constructors can
be attributed directly. Renamed imports, macro-generated consumers, implicit
trait operations and external consumers are not certified absent.

### Path aliases

| Alias | Pinned path |
|---|---|
| `L` | `crates/yu-solver/src/lib.rs` |
| `T` | `crates/yu-solver/src/term.rs` |
| `S1` | `crates/yu-solver/src/f5c_binder_substitution.rs` |
| `S2` | `crates/yu-solver/src/f5c_draft.rs` |
| `S3` | `crates/yu-solver/src/f5c_draft_heap.rs` |
| `S4` | `crates/yu-solver/src/f5c_generalization.rs` |
| `S5` | `crates/yu-solver/src/f5c_generalization/flat_source_arena.rs` |
| `S6` | `crates/yu-solver/src/f5c_generalization/flat_walk_sink.rs` |
| `S7` | `crates/yu-solver/src/f5c_materialization.rs` |
| `S8` | `crates/yu-solver/src/f5c_normalization.rs` |
| `S9` | `crates/yu-solver/src/f5c_replay.rs` |
| `S10` | `crates/yu-solver/src/f5c_tree_analysis.rs` |
| `S11` | `crates/yu-solver/src/incoming_sample_trace.rs` |
| `S12` | `crates/yu-solver/src/intrusion_transport.rs` |
| `S13` | `crates/yu-solver/src/scc.rs` |
| `S14` | `crates/yu-solver/src/tests/f5c_binder_substitution.rs` |
| `S15` | `crates/yu-solver/src/tests/f5c_depth_limit.rs` |
| `S16` | `crates/yu-solver/src/tests/f5c_flat_walk_sink.rs` |
| `S17` | `crates/yu-solver/src/tests/f5c_generalization_transactions.rs` |
| `S18` | `crates/yu-solver/src/tests/f5c_materialization.rs` |
| `S19` | `crates/yu-solver/src/tests/f5c_replay.rs` |
| `S20` | `crates/yu-solver/src/tests/f5c_resource_probe.rs` |
| `S21` | `crates/yu-solver/src/tests/f5c_scratch_reserve.rs` |
| `S22` | `crates/yu-solver/src/tests/f5c_tree_analysis.rs` |
| `S23` | `crates/yu-solver/src/tests/f5c_value_exact_upper_route.rs` |
| `S24` | `crates/yu-solver/src/tests/f5c_work_meter.rs` |
| `S25` | `crates/yu-solver/src/tests/intrusion_transport.rs` |
| `S26` | `crates/yu-solver/src/tests/research_function_realization.rs` |

### Every exported type and declared traits

All rows A. Fields of non-unit structs are private. Trait list reflects source declarations; no stable Debug-text format is inferred.

| Type | Kind | Locator | Declared traits |
|---|---|---|---|
| `ComponentId` | enum | `L:360` | `Clone, Debug, Eq, Hash, PartialEq` |
| `ConstraintOccurrenceId` | struct | `L:391` | `Clone, Debug, Eq, Hash, PartialEq` |
| `CauseId` | struct | `L:415` | `Clone, Debug, Eq, Hash, PartialEq` |
| `ConstraintOccurrence` | struct | `L:428` | `Clone, Debug, Eq, PartialEq` |
| `Components` | struct | `L:450` | `Clone, Debug, Eq, PartialEq` |
| `CollectionAvailabilityError` | enum | `L:653` | `Clone, Copy, Debug, Eq, PartialEq` |
| `ConstraintBatch` | struct | `L:762` | `Clone, Debug` |
| `ArtifactMismatch` | struct | `L:1959` | `Clone, Copy, Debug, Eq, PartialEq` |
| `ProductionCounters` | struct | `L:1965` | `Clone, Debug, Default, Eq, PartialEq` |
| `FactId` | struct | `L:2842` | `Clone, Copy, Debug, Eq, Hash, PartialEq` |
| `AdmissionDelta` | enum | `L:2849` | `Clone, Copy, Debug, Eq, PartialEq` |
| `AdmissionReceipt` | struct | `L:2858` | `Clone, Debug` |
| `ProvenanceEdge` | struct | `L:2881` | `Clone, Debug, Eq, PartialEq` |
| `SemanticFact` | struct | `L:2894` | `Clone, Debug, Eq, PartialEq` |
| `ConstraintStore` | struct | `L:2914` | `Debug` |
| `ConstraintTransaction` | struct | `L:3464` | `none` |
| `ConstraintError` | enum | `L:3579` | `Clone, Copy, Debug, Eq, PartialEq` |
| `SolvedValue` | enum | `L:3621` | `Clone, Copy, Debug, Eq, PartialEq` |
| `SolvedEffect` | enum | `L:3627` | `Clone, Copy, Debug, Eq, PartialEq` |
| `SolvedProjection` | struct | `L:3632` | `Clone, Copy, Debug, Eq, PartialEq` |
| `SolverErrorKind` | enum | `L:3645` | `Clone, Copy, Debug, Eq, Hash, PartialEq` |
| `ValueShape` | enum | `L:3657` | `Clone, Copy, Debug, Eq, Hash, PartialEq` |
| `SolverError` | struct | `L:3663` | `Clone, Debug, Eq, PartialEq` |
| `SolveAvailabilityError` | enum | `L:3680` | `Clone, Copy, Debug, Eq, PartialEq` |
| `SolvedModule` | struct | `L:7168` | `Debug` |
| `Term` | struct | `T:111` | `Clone, Copy, Debug, Eq, Hash, PartialEq` |
| `TermLookupError` | enum | `T:126` | `Clone, Copy, Debug, Eq, Hash, PartialEq` |
| `LiveVariableView` | struct | `T:132` | `Clone, Copy, Debug, Eq, Hash, PartialEq` |
| `Polarity` | enum | `T:150` | `Clone, Copy, Debug, Eq, Hash, PartialEq` |
| `TermView` | enum | `T:170` | `Clone, Debug, Eq, PartialEq` |

### Every explicit public method

All rows A. Counter macro-generated methods appear individually next. Every shared selector is mapped once in the call appendix.

| Declaration | Locator | Signature |
|---|---|---|
| `ComponentId::occurrence` | `L:369` | `pub fn occurrence(&self) -> Option<&HirOccurrenceId>` |
| `ComponentId::definition_root` | `L:375` | `pub fn definition_root(&self) -> Option<&DefinitionRootId>` |
| `ComponentId::kind` | `L:381` | `pub const fn kind(&self) -> ComponentKind` |
| `ConstraintOccurrenceId::occurrence` | `L:402` | `pub fn occurrence(&self) -> &HirOccurrenceId` |
| `ConstraintOccurrenceId::source_ordinal` | `L:405` | `pub const fn source_ordinal(&self) -> u32` |
| `ConstraintOccurrenceId::local_slot` | `L:408` | `pub const fn local_slot(&self) -> u8` |
| `CauseId::occurrence` | `L:422` | `pub fn occurrence(&self) -> &ConstraintOccurrenceId` |
| `ConstraintOccurrence::id` | `L:435` | `pub fn id(&self) -> &ConstraintOccurrenceId` |
| `ConstraintOccurrence::lower` | `L:438` | `pub const fn lower(&self) -> Term` |
| `ConstraintOccurrence::upper` | `L:441` | `pub const fn upper(&self) -> Term` |
| `ConstraintOccurrence::cause` | `L:444` | `pub fn cause(&self) -> &CauseId` |
| `Components::value` | `L:668` | `pub fn value(&self) -> &ComponentId` |
| `Components::effect` | `L:671` | `pub fn effect(&self) -> &ComponentId` |
| `ConstraintBatch::collect` | `L:815` | `pub fn collect(hir: Arc<HirModule>) -> Result<Self, CollectionAvailabilityError>` |
| `ConstraintBatch::hir` | `L:1234` | `pub fn hir(&self) -> &Arc<HirModule>` |
| `ConstraintBatch::occurrences` | `L:1237` | `pub fn occurrences(&self) -> &[ConstraintOccurrence]` |
| `ConstraintBatch::term_view` | `L:1240` | `pub fn term_view(&self, term: Term) -> Result<TermView<'_>, TermLookupError>` |
| `ConstraintBatch::term_kind` | `L:1248` | `pub fn term_kind(&self, term: Term) -> Result<ComponentKind, TermLookupError>` |
| `ConstraintBatch::counters` | `L:1378` | `pub fn counters(&self) -> ProductionCounters` |
| `ConstraintBatch::components_for` | `L:1402` | `pub fn components_for( &self, occurrence: &HirOccurrenceId, ) -> Result<Option<Components>, ArtifactMismatch>` |
| `ConstraintBatch::root_value_component` | `L:1417` | `pub fn root_value_component( &self, root: &DefinitionRootId, ) -> Result<ComponentId, ArtifactMismatch>` |
| `ProductionCounters::adjacency_appends` | `L:2524` | `pub const fn adjacency_appends(&self) -> usize` |
| `ProductionCounters::adjacency_visits` | `L:2530` | `pub const fn adjacency_visits(&self) -> usize` |
| `ProductionCounters::maximum_fan_out` | `L:2534` | `pub const fn maximum_fan_out(&self) -> usize` |
| `ProductionCounters::solved_root_index_probes` | `L:2538` | `pub const fn solved_root_index_probes(&self) -> usize` |
| `ProductionCounters::solved_root_index_capacity` | `L:2542` | `pub const fn solved_root_index_capacity(&self) -> usize` |
| `ProductionCounters::solved_root_index_retained_bytes` | `L:2546` | `pub const fn solved_root_index_retained_bytes(&self) -> usize` |
| `ProductionCounters::bounds_workspace_capacity` | `L:2550` | `pub const fn bounds_workspace_capacity(&self) -> usize` |
| `ProductionCounters::bounds_workspace_retained_bytes` | `L:2554` | `pub const fn bounds_workspace_retained_bytes(&self) -> usize` |
| `ProductionCounters::fanout_index_capacity` | `L:2558` | `pub const fn fanout_index_capacity(&self) -> usize` |
| `ProductionCounters::fanout_index_retained_bytes` | `L:2562` | `pub const fn fanout_index_retained_bytes(&self) -> usize` |
| `ProductionCounters::solver_workspace_retained_bytes` | `L:2566` | `pub const fn solver_workspace_retained_bytes(&self) -> usize` |
| `ProductionCounters::failed_component_workspace_capacity` | `L:2572` | `pub const fn failed_component_workspace_capacity(&self) -> usize` |
| `ProductionCounters::failed_component_workspace_retained_bytes` | `L:2578` | `pub const fn failed_component_workspace_retained_bytes(&self) -> usize` |
| `FactId::index` | `L:2844` | `pub const fn index(self) -> u32` |
| `AdmissionReceipt::occurrence` | `L:2867` | `pub fn occurrence(&self) -> &ConstraintOccurrenceId` |
| `AdmissionReceipt::cause` | `L:2870` | `pub fn cause(&self) -> &CauseId` |
| `AdmissionReceipt::fact` | `L:2873` | `pub const fn fact(&self) -> FactId` |
| `AdmissionReceipt::delta` | `L:2876` | `pub const fn delta(&self) -> AdmissionDelta` |
| `ProvenanceEdge::cause` | `L:2886` | `pub fn cause(&self) -> &CauseId` |
| `ProvenanceEdge::fact` | `L:2889` | `pub const fn fact(&self) -> FactId` |
| `SemanticFact::id` | `L:2900` | `pub const fn id(&self) -> FactId` |
| `SemanticFact::lower` | `L:2903` | `pub const fn lower(&self) -> Term` |
| `SemanticFact::upper` | `L:2906` | `pub const fn upper(&self) -> Term` |
| `ConstraintStore::from_batch` | `L:2971` | `pub fn from_batch(batch: ConstraintBatch) -> Self` |
| `ConstraintStore::transaction` | `L:3015` | `pub fn transaction(&mut self) -> ConstraintTransaction<'_>` |
| `ConstraintStore::term_view` | `L:3244` | `pub fn term_view(&self, term: Term) -> Result<TermView<'_>, TermLookupError>` |
| `ConstraintStore::term_kind` | `L:3247` | `pub fn term_kind(&self, term: Term) -> Result<ComponentKind, TermLookupError>` |
| `ConstraintStore::record_provenance` | `L:3273` | `pub fn record_provenance(&mut self, receipt: AdmissionReceipt) -> Result<(), ConstraintError>` |
| `ConstraintStore::facts` | `L:3393` | `pub fn facts(&self) -> &[SemanticFact]` |
| `ConstraintStore::provenance` | `L:3396` | `pub fn provenance(&self) -> &[ProvenanceEdge]` |
| `ConstraintStore::counters` | `L:3399` | `pub fn counters(&self) -> &ProductionCounters` |
| `ConstraintTransaction::admit` | `L:3468` | `pub fn admit( &mut self, occurrence: &ConstraintOccurrence, ) -> Result<AdmissionReceipt, ConstraintError>` |
| `SolvedProjection::value` | `L:3637` | `pub const fn value(self) -> SolvedValue` |
| `SolvedProjection::effect` | `L:3640` | `pub const fn effect(self) -> SolvedEffect` |
| `SolverError::occurrence` | `L:3669` | `pub fn occurrence(&self) -> &ConstraintOccurrenceId` |
| `SolverError::cause` | `L:3672` | `pub fn cause(&self) -> &CauseId` |
| `SolverError::kind` | `L:3675` | `pub const fn kind(&self) -> SolverErrorKind` |
| `SolvedModule::solve` | `L:15665` | `pub fn solve(batch: ConstraintBatch) -> Result<Self, SolveAvailabilityError>` |
| `SolvedModule::hir` | `L:15668` | `pub fn hir(&self) -> &Arc<HirModule>` |
| `SolvedModule::occurrences` | `L:15671` | `pub fn occurrences(&self) -> &[HirOccurrenceId]` |
| `SolvedModule::errors` | `L:15674` | `pub fn errors(&self) -> &[SolverError]` |
| `SolvedModule::store` | `L:15677` | `pub fn store(&self) -> &ConstraintStore` |
| `SolvedModule::counters` | `L:15680` | `pub fn counters(&self) -> ProductionCounters` |
| `SolvedModule::projection_for` | `L:15693` | `pub fn projection_for( &self, occurrence: &HirOccurrenceId, ) -> Result<SolvedProjection, ArtifactMismatch>` |
| `SolvedModule::root_value_for` | `L:15708` | `pub fn root_value_for(&self, root: &DefinitionRootId) -> Result<SolvedValue, ArtifactMismatch>` |
| `LiveVariableView::kind` | `T:138` | `pub const fn kind(self) -> ComponentKind` |
| `LiveVariableView::polarity` | `T:141` | `pub const fn polarity(self) -> Polarity` |
| `LiveVariableView::ordinal` | `T:144` | `pub const fn ordinal(self) -> u32` |

### Every ProductionCounters macro accessor and call/reference dependency

All rows A; each is `pub const fn name(&self) -> usize`. Declaration locator identifies its macro argument. `none` means no lexical public call/reference found, not no private-field test observation or external use.

| Accessor | Declaration | Call/reference locators |
|---|---|---|
| `hir_traversals` | `L:2280` | L:18903,19889,20051,20903,20982 |
| `body_pass_visits` | `L:2281` | L:18904,19890,20983 |
| `definition_registration_visits` | `L:2282` | L:18905,19891,20984 |
| `collected_complete_bodies` | `L:2283` | L:18907,18966,19893,20986 |
| `collected_error_bodies` | `L:2284` | L:18908,18967,19894,20987 |
| `collected_ambiguous_name_bodies` | `L:2285` | L:18909,18968,19895 |
| `collected_unresolved_name_bodies` | `L:2286` | L:18910,18969,19896 |
| `collected_definitions` | `L:2287` | L:18906,19892,20052,20985 |
| `definition_use_endpoint_pass_visits` | `L:2288` | L:18911,19898,20988 |
| `definition_use_endpoint_workspace_peak_capacity` | `L:2289` | L:18912,19918,19997,19998,20989 |
| `definition_use_endpoint_workspace_capacity_growths` | `L:2290` | L:20005,20006 |
| `definition_use_endpoint_workspace_peak_bytes` | `L:2291` | L:19917,19925,20013,20014 |
| `definition_endpoint_index_inserts` | `L:2292` | L:18913,19897 |
| `definition_endpoint_index_probes` | `L:2293` | L:18914,19899 |
| `definition_endpoint_identity_hash_byte_incidences` | `L:2294` | L:19901,19973,19976,20017,20018 |
| `definition_endpoint_logical_successful_equality_byte_incidences` | `L:2295` | L:19905,19981,19984,20021,20022 |
| `definition_endpoint_index_peak_capacity` | `L:2296` | L:19913,19993,19994,21133,21134 |
| `definition_endpoint_index_capacity_growths` | `L:2297` | L:20001,20002 |
| `definition_endpoint_index_peak_bytes` | `L:2298` | L:19912,19924,20009,20010 |
| `definition_record_index_inserts` | `L:2299` | L:18915,19909 |
| `definition_use_index_inserts` | `L:2300` | L:18916,19910 |
| `f0_collection_retained_bytes` | `L:2301` | L:19504,19513,19923,20033,20034,20064,20070 |
| `f0_collection_peak_bytes` | `L:2302` | L:19510,19922,20037,20038,20069 |
| `f2_batch_retained_bytes` | `L:2303` | L:19503,20063,20090,20091,21052 |
| `f2_batch_plan_peak_bytes` | `L:2304` | L:19509,20068,20094,20095,21053 |
| `retained_definition_uses` | `L:2305` | L:18917,19908,20053,20990 |
| `definition_record_index_capacity` | `L:2306` | L:20025,20026,21137,21138 |
| `definition_record_index_retained_bytes` | `L:2307` | L:20086,20087 |
| `definition_record_retained_bytes` | `L:2308` | L:20082,20083 |
| `definition_use_retained_bytes` | `L:2309` | none |
| `definition_use_index_capacity` | `L:2310` | L:20029,20030 |
| `definition_use_index_retained_bytes` | `L:2311` | none |
| `definition_query_probes` | `L:2312` | L:16729,18918,21017 |
| `definition_use_query_probes` | `L:2313` | L:16401,16735,17011,17012,18919,19442,21018 |
| `scc_component_for_definition_query_probes` | `L:2314` | L:16740,19438,19544,21019 |
| `scc_component_members_query_probes` | `L:2315` | L:16402,16742,17016,17017,19439,19548,21020,21141,21142 |
| `scc_component_internal_uses_query_probes` | `L:2316` | L:16403,16748,17021,17022,19440,21021,21145,21146 |
| `scc_component_incoming_uses_query_probes` | `L:2317` | L:16404,16754,17026,17027,19441,21022,21149,21150 |
| `scc_distinct_arcs` | `L:2318` | L:19631 |
| `scc_retained_occurrence_payloads` | `L:2319` | L:19633,19634 |
| `scc_forward_adjacency_entries` | `L:2320` | L:19637,19638 |
| `scc_forward_payload_lengths` | `L:2321` | L:19641,19642 |
| `scc_forward_adjacency_capacity` | `L:2322` | L:19645,19646 |
| `scc_forward_payload_capacity` | `L:2323` | L:19649,19650 |
| `scc_reverse_adjacency_entries` | `L:2324` | L:19653,19654 |
| `scc_reverse_adjacency_capacity` | `L:2325` | L:19657,19658 |
| `scc_definition_index_probes` | `L:2326` | L:19661,19662 |
| `scc_definition_index_capacity` | `L:2327` | L:19665,19666 |
| `scc_seen_use_set_probes` | `L:2328` | L:19669,19670 |
| `scc_seen_use_set_capacity` | `L:2329` | L:19673,19674 |
| `scc_condensation_set_probes` | `L:2330` | L:19677,19678 |
| `scc_condensation_set_capacity` | `L:2331` | L:19681,19682 |
| `scc_plan_component_index_probes` | `L:2332` | L:16405,16760,17031,17032,19685,19686,21023,21153,21154 |
| `scc_plan_component_index_capacity` | `L:2333` | L:19689,19690 |
| `scc_plan_definition_index_probes` | `L:2334` | L:16406,16766,17036,17037,19693,19694,21024,21157,21158 |
| `scc_plan_definition_index_capacity` | `L:2335` | L:19697,19698 |
| `scc_map_set_rebuilds` | `L:2336` | L:19700 |
| `scc_stable_id_clone_count` | `L:2337` | L:19523,19532,19702,19703,19841 |
| `scc_stable_id_clone_payload_bytes` | `L:2338` | L:19706,19707,19843 |
| `scc_node_visits` | `L:2339` | L:19626 |
| `scc_edge_visits` | `L:2340` | L:19627 |
| `scc_stack_pushes` | `L:2341` | L:19628 |
| `scc_lowlink_writes` | `L:2342` | L:19629 |
| `scc_component_writes` | `L:2343` | L:19630 |
| `scc_peak_stack_bytes` | `L:2344` | L:19709 |
| `scc_peak_temporary_set_bytes` | `L:2345` | L:19711,19712 |
| `scc_kosaraju_workspace_peak_bytes` | `L:2346` | L:19715,19716,19810,19818 |
| `scc_partition_workspace_peak_bytes` | `L:2347` | L:19719,19720,19815,19820 |
| `scc_scheduler_workspace_peak_bytes` | `L:2348` | L:19723,19724,19828,19834 |
| `scc_freeze_transition_peak_bytes` | `L:2349` | L:19727,19728,19822 |
| `scc_maximum_component_size` | `L:2350` | L:19739,19740 |
| `scc_internal_use_count` | `L:2351` | L:19477,19731,19732 |
| `scc_incoming_use_count` | `L:2352` | L:19500,19735,19736 |
| `scc_condensation_node_visits` | `L:2353` | L:19744,19745 |
| `scc_condensation_edge_visits` | `L:2354` | L:19748,19749 |
| `scc_ready_queue_operations` | `L:2355` | L:19752,19753 |
| `scc_ready_queue_comparisons` | `L:2356` | L:19616 |
| `scc_ready_queue_maximum_size` | `L:2357` | L:19756,19757,19826 |
| `scc_sort_count` | `L:2358` | L:19759 |
| `scc_sort_comparisons` | `L:2359` | L:19616 |
| `scc_sort_elements` | `L:2360` | L:19760 |
| `scc_plan_component_capacity` | `L:2361` | L:19762,19763 |
| `scc_plan_member_capacity` | `L:2362` | L:19766,19767 |
| `scc_plan_internal_use_capacity` | `L:2363` | L:19770,19771 |
| `scc_plan_incoming_use_capacity` | `L:2364` | L:19501,19774,19775 |
| `scc_plan_retained_payload_bytes` | `L:2365` | L:19504,19778,19779,20065,20098,20099,21055,21056 |
| `scc_graph_workspace_peak_known_bytes` | `L:2366` | L:19782,19783,19811,19829 |
| `scc_f1_graph_input_plan_peak_known_bytes` | `L:2367` | L:19515,19786,19787,19817,19819,19821,19833,20072,20102,20103,21059,21060 |
| `cst_traversals` | `L:2368` | L:20918,21009 |
| `cst_rescans` | `L:2369` | L:20919,21010 |
| `hir_clone_count` | `L:2370` | L:20920,21011 |
| `typed_tree_copies` | `L:2371` | L:20921,21012 |
| `copied_spelling_bytes` | `L:2372` | L:20922,21013 |
| `emitted_facts` | `L:2373` | L:20905,20935,20991 |
| `admitted_facts` | `L:2374` | L:20786,20906,20992 |
| `duplicate_facts` | `L:2375` | L:20917,21008 |
| `canonical_map_probes` | `L:2376` | L:19929,20958,21190 |
| `canonical_map_rebuilds` | `L:2377` | L:16945,16992,17384,17385,19930,20953,21130 |
| `canonical_map_capacity` | `L:2378` | L:20951,21112 |
| `canonical_map_retained_bytes` | `L:2379` | L:21064,21065 |
| `occurrence_component_index_probes` | `L:2380` | L:21192,21193 |
| `occurrence_component_index_capacity` | `L:2381` | L:21114,21115 |
| `occurrence_component_index_retained_bytes` | `L:2382` | L:21068,21069 |
| `occurrence_component_query_probes` | `L:2383` | L:18840 |
| `root_component_index_probes` | `L:2384` | L:21196,21197 |
| `root_component_index_capacity` | `L:2385` | L:21118,21119 |
| `root_component_index_retained_bytes` | `L:2386` | L:21072,21073 |
| `root_component_query_probes` | `L:2387` | L:18841 |
| `consumed_receipt_index_probes` | `L:2388` | L:21200,21201 |
| `consumed_receipt_index_capacity` | `L:2389` | L:21122,21123 |
| `consumed_receipt_index_retained_bytes` | `L:2390` | L:21076,21077 |
| `solved_root_query_probes` | `L:2391` | L:18842,21038,21203 |
| `generated_work_items` | `L:2392` | L:20910,20929,21002,21044 |
| `accepted_work_items` | `L:2393` | L:20787,20911,20930,21003,21045 |
| `duplicate_work_items` | `L:2394` | L:20912,21004 |
| `component_allocations` | `L:2395` | L:20904,20932,20999,21047 |
| `component_retained_bytes` | `L:2396` | L:20940,21051 |
| `fact_allocations` | `L:2397` | L:20908,20933,21000,21048 |
| `fact_retained_bytes` | `L:2398` | L:20941,21062 |
| `occurrence_allocations` | `L:2399` | L:20907,20993 |
| `occurrence_retained_bytes` | `L:2400` | L:20934,21049 |
| `occurrence_record_retained_bytes` | `L:2401` | L:20937,20938,21084,21085 |
| `root_allocations` | `L:2402` | L:20916,20994 |
| `root_retained_bytes` | `L:2403` | S4:4427,4638; L:21050,23203,23301,23303 |
| `hir_definition_root_allocation_bytes` | `L:2404` | L:20996 |
| `definition_root_def_id_clone_bytes` | `L:2405` | L:817,21014 |
| `index_rebuilds` | `L:2406` | L:20040,20954,21131 |
| `index_capacity` | `L:2407` | S4:4511; L:20952,21129 |
| `provenance_edges` | `L:2408` | L:20909,21001 |
| `provenance_retained_bytes` | `L:2409` | L:20942,21087 |
| `solved_projection_retained_bytes` | `L:2410` | L:16850,17187,17188,20944,20945,21089,21090 |
| `solver_error_workspace_capacity` | `L:2411` | L:17324,17325,17822,17961,17965 |
| `solver_error_workspace_retained_bytes` | `L:2412` | L:17329,17330,17963,21109,21110 |
| `eager_explanation_builds` | `L:2413` | L:20923,21015 |
| `scc_execution_component_visits` | `L:2414` | L:16407,16907,17041,17042,18014,21025,21161,21162 |
| `scc_execution_internal_use_connections` | `L:2415` | L:16408,16920,17046,17047,17579,18015,21026 |
| `scc_execution_draft_members` | `L:2416` | L:16409,16910,17051,17052,21027,21165,21166 |
| `scc_execution_drafts_visible_barriers` | `L:2417` | L:16410,17056,17057,21028,21169,21170 |
| `scc_execution_finalized_members` | `L:2418` | L:16411,16912,17061,17062,21029,21173,21174 |
| `scc_execution_installed_members` | `L:2419` | L:16412,16916,17066,17067,21030,21177,21178 |
| `scc_execution_incoming_instantiations` | `L:2420` | L:16413,16924,17071,17072,17580,18016,21031 |
| `scc_execution_int_instantiation_facts` | `L:2421` | L:16414,16928,17198,17199,17635,17658,17731,21032 |
| `scc_execution_bottom_trivial_instantiations` | `L:2422` | L:16415,16929,17203,17204,17655,17737,21033 |
| `scc_execution_draft_lookups` | `L:2423` | L:16416,17208,17209,21034,21181,21182 |
| `scc_execution_cross_draft_visits` | `L:2424` | L:16417,17213,17214,21035 |
| `generalization_quantifier_writes` | `L:2425` | none |
| `generalization_recursive_binder_writes` | `L:2426` | none |
| `generalization_shared_summary_admissions` | `L:2427` | none |
| `generalization_uncacheable_states` | `L:2428` | none |
| `generalization_shared_summary_hits` | `L:2429` | none |
| `closed_normalized_key_writes` | `L:2430` | L:26587 |
| `closed_normalization_child_comparisons` | `L:2431` | none |
| `closed_normalization_hash_probes` | `L:2432` | L:26592 |
| `closed_normalization_hash_admissions` | `L:2433` | L:26593 |
| `closed_normalization_hash_duplicates` | `L:2434` | L:26594 |
| `closed_normalization_descriptor_words` | `L:2435` | L:26588 |
| `closed_normalization_word_comparisons` | `L:2436` | none |
| `closed_normalization_index_requested_slots` | `L:2437` | L:26589 |
| `closed_normalization_index_actual_capacity` | `L:2438` | L:26595 |
| `closed_normalization_index_retained_bytes` | `L:2439` | L:26596 |
| `closed_normalization_index_peak_bytes` | `L:2440` | L:26591 |
| `closed_normalization_index_capacity_growths` | `L:2441` | L:26590 |
| `component_expansion_memo_requested_slots` | `L:2442` | none |
| `component_expansion_memo_actual_capacity` | `L:2443` | none |
| `component_expansion_memo_retained_bytes` | `L:2444` | none |
| `component_expansion_memo_peak_bytes` | `L:2445` | none |
| `component_expansion_memo_capacity_growths` | `L:2446` | none |
| `instantiation_fresh_value_variables` | `L:2447` | L:28491; S26:1640 |
| `instantiation_fresh_effect_variables` | `L:2448` | L:28497 |
| `instantiation_node_visits` | `L:2449` | L:28512 |
| `instantiation_lower_bound_restorations` | `L:2450` | L:28503 |
| `instantiation_upper_bound_restorations` | `L:2451` | L:28509 |
| `instantiation_substitution_requested_slots` | `L:2452` | L:28346 |
| `instantiation_substitution_actual_capacity` | `L:2453` | L:28350,28451 |
| `instantiation_substitution_retained_bytes` | `L:2454` | L:28354,28450 |
| `instantiation_substitution_peak_bytes` | `L:2455` | L:28358,28452 |
| `instantiation_substitution_capacity_growths` | `L:2456` | L:28362 |
| `constraint_pair_admissions` | `L:2457` | L:16418,16866,16878,16900,17432,17433,17437,17439,18017,18643 |
| `constraint_pair_duplicates` | `L:2458` | L:16419,16872,16878,16900,17218,17219,17438,17440,18018,18644 |
| `lower_bound_insertions` | `L:2459` | L:16420,17223,17224,18019 |
| `upper_bound_insertions` | `L:2460` | L:16421,17228,17229,18020 |
| `lower_bound_replays` | `L:2461` | L:16422,16772,16901,17233,17234,17244,18021,18682,18714 |
| `upper_bound_replays` | `L:2462` | L:16423,16773,16901,17238,17239,17245,18022,18683,18715 |
| `scheme_table_len` | `L:2463` | L:16424,17076,17077,21036,21184 |
| `scheme_table_capacity` | `L:2464` | L:17081,17082 |
| `scheme_table_retained_bytes` | `L:2465` | L:17086,17087 |
| `scheme_table_rebuilds` | `L:2466` | L:17249,17250 |
| `scheme_root_query_probes` | `L:2467` | L:16425,17146,17147,18028,18029,21039,21204 |
| `scheme_root_index_capacity` | `L:2468` | L:17091,17092 |
| `scheme_root_index_retained_bytes` | `L:2469` | L:17096,17097 |
| `scheme_root_index_growths` | `L:2470` | L:17254,17255 |
| `scheme_root_index_rebuilds` | `L:2471` | L:17259,17260 |
| `scheme_root_query_identity_hash_byte_incidences` | `L:2472` | L:17151,17152,18032,18035 |
| `scheme_root_query_logical_successful_equality_byte_incidences` | `L:2473` | L:17156,17158,18040,18043 |
| `draft_scratch_max_len` | `L:2474` | L:16426,17264,17265 |
| `draft_scratch_capacity` | `L:2475` | L:17101,17102 |
| `draft_scratch_retained_bytes` | `L:2476` | L:17106,17107 |
| `draft_scratch_growths` | `L:2477` | L:17269,17270 |
| `bound_table_retained_bytes` | `L:2478` | L:17274,17275,22544 |
| `bound_table_capacity` | `L:2479` | L:17111,17112,22543 |
| `bound_table_growths` | `L:2480` | L:17279,17280 |
| `bound_table_rebuilds` | `L:2481` | L:17284,17285 |
| `bound_table_peak_bytes` | `L:2482` | L:17289,17290 |
| `constraint_pair_cache_retained_bytes` | `L:2483` | L:17449,17450 |
| `constraint_pair_cache_capacity` | `L:2484` | L:17444,17445 |
| `constraint_pair_cache_growths` | `L:2485` | L:17294,17295 |
| `constraint_pair_cache_rebuilds` | `L:2486` | L:17299,17300 |
| `constraint_pair_cache_peak_bytes` | `L:2487` | L:17304,17305 |
| `semantic_arena_retained_bytes` | `L:2488` | L:16832,17454,17455,22547,27143,27338,27403,27407,28108,28366,28613,29760,29844,29885; S23:523,772 |
| `semantic_arena_peak_bytes` | `L:2489` | L:16838,16902,17459,17460,28370,29861,29879,29907,29908 |
| `routed_use_provenance_len` | `L:2490` | L:16427,16935,17116,17117,17581 |
| `routed_use_provenance_capacity` | `L:2491` | L:17121,17122 |
| `routed_use_provenance_retained_bytes` | `L:2492` | L:17126,17127 |
| `routed_use_provenance_growths` | `L:2493` | L:16950,17309,17310; S23:456,461 |
| `occurrence_bound_state_retained_bytes` | `L:2494` | L:17314,17315 |
| `occurrence_bound_state_len` | `L:2495` | L:16429,17131,17132 |
| `occurrence_bound_state_capacity` | `L:2496` | L:17136,17137 |
| `occurrence_bound_state_growths` | `L:2497` | L:17319,17320 |
| `finish_projection_visits` | `L:2498` | L:16433,17141,17142,21037,21185 |
| `inference_session_retained_bytes` | `L:2499` | L:16844,17464,17465,22553,27149,27344,28114,28374,29766,29850; S23:530,779 |
| `inference_session_peak_bytes` | `L:2500` | L:16856,16903,17469,17470,28378 |
| `constraint_store_requested_capacity` | `L:2501` | L:16958,17334,17335 |
| `constraint_store_actual_capacity` | `L:2502` | L:16969,17339,17340 |
| `constraint_store_growths` | `L:2503` | L:16940,16980,17344,17345,17582 |
| `constraint_store_rebuilds` | `L:2504` | L:16941,16989,17349,17350,17583 |
| `fact_store_requested_capacity` | `L:2505` | L:16960,17354,17355 |
| `fact_store_actual_capacity` | `L:2506` | L:16971,17359,17360 |
| `fact_store_growths` | `L:2507` | L:16942,16982,17364,17365 |
| `canonical_map_requested_capacity` | `L:2508` | L:16961,17369,17370 |
| `canonical_map_actual_capacity` | `L:2509` | L:16972,17374,17375 |
| `canonical_map_growths` | `L:2510` | L:16944,16983,17379,17380 |
| `provenance_requested_capacity` | `L:2511` | L:16962,17389,17390 |
| `provenance_actual_capacity` | `L:2512` | L:16973,17394,17395 |
| `provenance_growths` | `L:2513` | L:16946,16984,17399,17400 |
| `provenance_rebuilds` | `L:2514` | L:16947,16993,17404,17405 |
| `consumed_receipt_requested_capacity` | `L:2515` | L:16963,17409,17410 |
| `consumed_receipt_actual_capacity` | `L:2516` | L:16974,17414,17415 |
| `consumed_receipt_growths` | `L:2517` | L:16948,16985,17419,17420 |
| `consumed_receipt_rebuilds` | `L:2518` | L:16949,16994,17424,17425 |
| `scc_count` | `L:2519` | L:19572,19742,19799,20054,20924,21016 |
| `adjacency_appends` (deprecated, returns 0) | `L:2524` | L:17948,20913,21005 |
| `adjacency_visits` (deprecated, returns 0) | `L:2530` | L:17949,20914,20931,21006,21046 |
| `maximum_fan_out` (deprecated, returns 0) | `L:2534` | L:17950,20915,21007 |
| `solved_root_index_probes` (deprecated, returns 0) | `L:2538` | L:17951 |
| `solved_root_index_capacity` (deprecated, returns 0) | `L:2542` | L:17952,21126,21127 |
| `solved_root_index_retained_bytes` (deprecated, returns 0) | `L:2546` | L:17953,21080,21081 |
| `bounds_workspace_capacity` (deprecated, returns 0) | `L:2550` | L:17954 |
| `bounds_workspace_retained_bytes` (deprecated, returns 0) | `L:2554` | L:17955,21097,21098 |
| `fanout_index_capacity` (deprecated, returns 0) | `L:2558` | L:17956 |
| `fanout_index_retained_bytes` (deprecated, returns 0) | `L:2562` | L:17957,21101,21102 |
| `solver_workspace_retained_bytes` (deprecated, returns 0) | `L:2566` | L:17958,20948,20949,21093,21094 |
| `failed_component_workspace_capacity` (deprecated, returns 0) | `L:2572` | L:17959 |
| `failed_component_workspace_retained_bytes` (deprecated, returns 0) | `L:2578` | L:17960,21105,21106 |

### Non-counter public call/reference selector map

Shared-name rows are lexical supersets as defined above; they preserve every candidate locator without claiming a typed receiver.

| Selector (public owners) | Call/reference locators |
|---|---|
| `occurrence` (AdmissionReceipt, CauseId, ComponentId, ConstraintOccurrenceId, SolverError) | L:1003,1006,1061,3277,3474,16320,16529,17627,18073,18078,18097,18742,18783,18786,18799,18829,18888,18889,19040,19041,19082,19087,19109,19115,19388,19471,19495,20122,20158,20170,20179,20190,20202,20236,20242,20312,20315,20317,20319,20367,20702,20883,20890; S26:384,410,437,523,619,1536,1634 |
| `definition_root` (ComponentId) | L:886,974,981,997,16318,16528,16722,17574,17606,17610,17614,17663,17984,18007,18060,18803,18808,18836,20226,20230,20269,20363,20406,20429,20433,20471,20542,20698,20721,20976; S26:594 |
| `kind` (ComponentId, LiveVariableView, SolverError) | S4:6396; L:9182,9188,9481,10608,10612,10640,10644,21217,21389,21547,21714,21840; T:78,220,759,1367; S26:458,481,1555 |
| `source_ordinal` (ConstraintOccurrenceId) | L:18727,18761 |
| `local_slot` (ConstraintOccurrenceId) | L:18079,18728,18762,18814,20313 |
| `id` (ConstraintOccurrence, SemanticFact) | S2:36,74; S3:2418,2864,2908,2943,2944,2976,3019; S4:11924,11925,11975,11976,12027,12028,12091,12092,12128,12129,12161,12162; S6:557,600,653; L:887,889,992,3282,15139,18078,18079,18088,18727,18728,18761,18762,18814,18888,18896,18897,18928,19368,19378,19380,19381,19433,19882,20825; S17:624,625; S20:1435,1790,1882,1951; S23:173,176,181,538,787,1256,1266,1271,2635,2639,3276,3279,3284,3519,3522,3527; S26:437,523,619,1234,1355,1473,1494,1503,1512,1568,1667,1716,1724,1749 |
| `lower` (ConstraintOccurrence, SemanticFact) | L:16299,18825,20330,20657,20729,20743,20756,27121,28298; S23:173,540,789,1250,1260,1727,1976,2630,3276,3519; S26:439,449,474,511,515,612,626,1554,1575 |
| `upper` (ConstraintOccurrence, SemanticFact) | L:16299,17748,18826,20710,20711,20871; S23:173,541,790,1251,3276,3519; S26:513,517,610 |
| `cause` (AdmissionReceipt, ConstraintOccurrence, ProvenanceEdge, SolverError) | L:17633,18092,18896,20312,20827,20828,20854; S26:437,523,619 |
| `value` (Components, SolvedProjection) | L:913,996,16320,16529,18097,18102,18799,18806,18825,18829,19040,19874,20122,20153,20170,20181,20236,20242,20287,20308,20319,20367,20421,20702,20885,20892; S26:384,391,586,590,1344,1484,1499,1663,1673,1684,1687,1692 |
| `effect` (Components, SolvedProjection) | L:18102; S26:535 |
| `collect` (ConstraintBatch) | S2:30,64,95,96,97; S3:2437,2439,2890,2891,2930,2931,2964,2965,2998,3000,3034,3036; S4:11956,11957,11965,11966,12002,12008,12014,12073,12079,12110,12154,12190,12191; S6:580,585,629,630,632,635,640,688,689; S7:1337,1366,1639,1669,1704,1711,1879,1914,2130,2632,2664; S8:3572,3591,4863,4873,4917,4962,4999,5149,5215,5223,5226,5249,5256,5291,5295,5356,5377,5378; L:7949,7961,8039,12977,14052,14100,15253,15304,15328,15333,16275,16455,16476,17604,18080,18129,18167,18168,18198,18199,18225,18281,18371,18379,18383,18392,18394,18401,18403,18463,18464,18467,18468,18481,18485,18525,18541,18553,18563,18659,18689,18731,18766,18777,18815,18859,18872,18892,18957,18982,19031,19044,19049,19066,19078,19083,19088,19091,19104,19110,19116,19119,19473,19474,19496,19497,19578,19591,19594,19598,19600,19605,19611,19806,19807,19939,20223,20263,20270,20752,20762,20898,20965,21212,21229,21235,21236,21237,21256,21314,21399,21484,21548,21583,21644,21746,21853,21998,22045,22076,22142,22212,22221,22246,22303,22330,22348,22366,22409,22422,22560,22765,23416,24179,27868,27947; S13:244,268,271,294,410,517; S16:45,130,455,2978,3005,3145,3149,4871; S17:639,641; S18:758; S19:260,292; S20:148,243,444,450,491,1068,1298,1319,1341,1459,1543,1581,1582,1854,1857,1904,1907,2068,2072,2074,2451,2467,2469; S23:69,375,395,611,631,875,1141,1328,1617,1866,2476,2774,2783,2957,2969,3120,3358,3597,3606,3938,4139; S25:110,113,119,123,124,172,216,217,258,263,311,320; S26:423,777,843,848,853,854,859,1104,1111,1464,1476,1517,1527,1537,1635,1759,1763 |
| `hir` (ConstraintBatch, SolvedModule) | L:16717,17569,18002,18740,19388,19867,20971 |
| `occurrences` (ConstraintBatch, SolvedModule) | L:10449,10460,10463,17649,17748,18076,18083,18724,18757,18774,18805,18812,18824,20118,20225,20298,20425,20696,20705,20710,20729,20743,20756,20777,20825,20827,20828,20833,20836,20837,27899,27939,27982,28015; S26:491,492 |
| `term_view` (ConstraintBatch, ConstraintStore) | S4:6392,7554; S10:180; L:3245,10527,10602,10634,10737,10764,12309,12330,16295,20330,20335,20338,20345,20349,20663,20730,20733,20737,20743,20756,20811,20815,22850,22854,22858,27121,27127,28298,28304,28307,28322,28324,28329; T:92,1414,1418,1425,1561,1565,1587,1591,1621,1623; S23:1260,1727,1976,2630; S26:439,449,457,474,478,511,517,612,626,630,634,640,644,1554,1555,1575,1580,1584,1587,1595,1599,1606,1610 |
| `term_kind` (ConstraintBatch, ConstraintStore) | L:3248,3569,10475 |
| `counters` (ConstraintBatch, ConstraintStore, SolvedModule) | L:15578,15579,16728,17578,17635,17654,17658,17822,17947,18025,18028,18029,18031,18034,18039,18042,18839,18902,18965,19437,19477,19499,19523,19532,19544,19547,19548,19572,19865,19972,19975,19980,19983,19989,19990,20050,20058,20078,20079,20786,20787,20902,20926,20927,20981,21041,21042,26585,28449; S26:1640 |
| `components_for` (ConstraintBatch) | L:18799,20121,20236,20242,20702 |
| `root_value_component` (ConstraintBatch) | L:16318,18803,20230,20698; S26:594 |
| `index` (FactId) | L:3281,18088 |
| `fact` (AdmissionReceipt, ProvenanceEdge) | L:3373,20849; S23:176,550,799,1266,2635,3279,3522; S26:437,523,619 |
| `delta` (AdmissionReceipt) | L:3374,20850,20851 |
| `from_batch` (ConstraintStore) | L:20714,20731,20772,20776,20792,20793,20831,20846,20856 |
| `transaction` (ConstraintStore) | L:3353,10465,20715,20781,20832,20847,20848,20855 |
| `record_provenance` (ConstraintStore) | L:3376,10471,20852,20853,20858,20861,20863 |
| `facts` (ConstraintStore) | L:17651,17685,17722,17765,17789,17821,18086,18088,20306,20330,20361,20427,20635,20657,20784,27117,27121,27247,27346,27409,27463,27718,27855,28298,28312,28643,28717,28808,28864,29037,29152,29326,29331,29427,29506,29541,29588,29715,29910,30034,30076,30082,30121,30157; S20:2152,2494; S21:77; S23:170,171,219,992,995,1240,1246,1248,1710,1725,1727,1959,1974,1976,2619,2625,2627,2871,2877,3057,3063,3266,3273,3274,3509,3516,3517,3707,3713,3843,4015,4300; S26:430,470,508,607,1553,1566 |
| `provenance` (ConstraintStore) | L:17631,17686,17723,17766,17790,18092,20307,20312,20785,20854,27248,27719,29038,29153,29327,29507,29911,30077,30083,30122; S23:175,176,220,549,550,798,799,993,1241,1247,1266,1711,1730,1960,1979,2620,2626,2634,2872,2878,3058,3064,3267,3278,3279,3510,3521,3522,3708,3714,3844,4016,4302; S26:435,522,618 |
| `admit` (ConstraintTransaction) | S4:7490; L:3354,10466,20716,20781,20833,20847,20848,20855,22954,22955,22981,23014,23051,23085,23187,23281,23592,23737,23792,24540; S17:85,291,305,345,364,410 |
| `solve` (SolvedModule) | L:17596,17772,17819,17945,17978,17999,18000,18054,18084,18739,18770,18771,18827,20150,20188,20200,20264,20384,20426,20444,20466,20536,20719,20873,20899,20900,20968,20969,22408,26580 |
| `errors` (SolvedModule) | L:17535,17820,17822,20288,20382,20875; S26:578,603,1468,1623,1654 |
| `store` (SolvedModule) | L:3075,17630,17651,17821,18086,18088,18092,20361,20427,20635; T:373,374,1472; S26:429,434,439,449,457,469,474,478,508,511,517,522,606,612,618,626,630,634,640,644,1553,1554,1555,1565,1575,1580,1584,1587,1595,1599,1606,1610 |
| `projection_for` (SolvedModule) | L:18096,18742,18783,18786,18829,20158,20170,20179,20190,20202,20367,20883,20890; S26:533 |
| `root_value_for` (SolvedModule) | L:16722,17574,17606,17610,17614,17663,17984,18007,18060,18836,20269,20363,20406,20429,20433,20471,20542,20721,20976 |
| `polarity` (LiveVariableView) | S4:6396,7573; L:10613,10645,20342,20343,22861,22862; S26:458,637,638,1555,1614,1615 |
| `ordinal` (LiveVariableView) | S4:6402,7578; S10:185; L:406,1021,1059,1080,1117,10614,10646,13939,14022,14023,14070,14071,14122,14258,14267,14385,14394,14562,14595,14882,15396,18776,18858,18886,18887,18888,18889,18981,19073,19077,19082,19087,19098,19103,19109,19115,19472,19495,20341,20463,20491,20528,20626,22804,22863,22864,22865,22866,27112,27192,27305,27358,27658,27850,27891,28045,28128,28174,28212,28310,28325,28426,28484,28554,29028,29098,29261,29365,29462,29988,30050,30097; S13:59,360,361,817,818,819,824,1049,1086; S20:143,161,166,198,203; S23:844,1055,1416,1531,1786,2270,2719,2902,3308,3551,3727,3878,4117; S26:458,482,483,484,648,650,678,1302,1523,1524,1616,1618 |

### Exact exported enum variants

All variants A; exhaustive, with payload shape as declared.

`ComponentId` at `L:360`:

```rust
pub enum ComponentId {
    Occurrence {
        occurrence: HirOccurrenceId,
        kind: ComponentKind,
    },
    /// Definition roots are value-only: an effect variant cannot be formed.
    DefinitionValue { root: DefinitionRootId },
}
```

`CollectionAvailabilityError` at `L:653`:

```rust
pub enum CollectionAvailabilityError {
    DefinitionIdentityExhausted,
    DefinitionUseIdentityExhausted,
    DuplicateDefinitionId,
    DuplicateDefinitionOrderId,
    DuplicateDefinitionUseId,
    MissingDefinitionEndpoint,
    NonTotalDefinitionMap,
    NonTotalDefinitionUseMap,
    GraphIdentityExhausted,
    ComponentIdentityExhausted,
    NonTotalSccMembershipMap,
    NonTotalSccComponentMap,
}
```

`AdmissionDelta` at `L:2849`:

```rust
pub enum AdmissionDelta {
    Accepted,
    Duplicate,
}
```

`ConstraintError` at `L:3579`:

```rust
pub enum ConstraintError {
    CrossKind {
        lower: ComponentKind,
        upper: ComponentKind,
    },
    ArtifactMismatch,
    CauseMismatch,
    ReceiptMismatch,
    AlienReceipt,
    ReceiptConsumed,
    IdentityExhausted,
}
```

`SolvedValue` at `L:3621`:

```rust
pub enum SolvedValue {
    Int,
    Unknown,
    Never,
}
```

`SolvedEffect` at `L:3627`:

```rust
pub enum SolvedEffect {
    Empty,
    Unknown,
}
```

`SolverErrorKind` at `L:3645`:

```rust
pub enum SolverErrorKind {
    CrossKind {
        lower: ComponentKind,
        upper: ComponentKind,
    },
    IncompatibleValue {
        lower: ValueShape,
        upper: ValueShape,
    },
}
```

`ValueShape` at `L:3657`:

```rust
pub enum ValueShape {
    Bottom,
    Int,
    Function,
}
```

`SolveAvailabilityError` at `L:3680`:

```rust
pub enum SolveAvailabilityError {
    ArtifactMismatch,
    CauseMismatch,
    ReceiptMismatch,
    IdentityExhausted,
}
```

`TermLookupError` at `T:126`:

```rust
pub enum TermLookupError {
    ArenaMismatch,
    InvalidHandle,
}
```

`Polarity` at `T:150`:

```rust
pub enum Polarity {
    Positive,
    Negative,
}
```

`TermView` at `T:170`:

```rust
pub enum TermView<'a> {
    Leaf(Leaf),
    Component(&'a ComponentId),
    LiveVariable(LiveVariableView),
    PositiveBottom,
    NegativeTop,
    NegativeBottom,
    PositiveFunction {
        argument: Term,
        argument_effect: Term,
        result_effect: Term,
        result: Term,
    },
    NegativeFunction {
        argument: Term,
        argument_effect: Term,
        result_effect: Term,
        result: Term,
    },
}
```

## Result and unresolved questions

The exported boundary comprises 30 types, all explicit public methods above,
240 macro counter accessors, 13 deprecated zero accessors and public trait/enum/
borrow shapes. F5 representation observations exposed by these APIs are A;
only their hidden backing state is B. No API disposition is selected here.

External consumer discovery, typed attribution of shared-name call candidates,
approved preservation/versioning of changed public surfaces, and the complete
canonical generalized-interface/invalidation proof remain open. Absence of
local production consumers narrows migration work without deciding authority.
Private F5 test assertions are C dependencies, not automatic language contracts.

No code, test, fixture, expectation, test name, design status, task record, Git
index or ref was changed. No runtime/performance evidence was collected. The
primary owns any accepted task/progress/design linking and integration; this
lease permits only this artifact.
