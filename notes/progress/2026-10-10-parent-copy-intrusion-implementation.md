# Parent-copy SCC intrusion implementation

Status: reviewed implementation checkpoint; not a public/F5 cutover certificate
Branch: `research/simple-sub-intrusion`
Baseline: `394c3bfc54aeea3532ecb2e07ec9fa355c8aa81d`
Authority: [current user decision](../design/2026-10-10-parent-copy-scc-intrusion.md)
Mode: M2; semantic and resource review, at most two reviewers per round
Verification budget: owning candidate/default Cargo checks; zero runtime tests,
probes, benchmark processes or samples

## Operation and integration

Actual extrusion-copy allocation retains kind-qualified parent provenance,
polarity and target level. Parent metadata itself contributes no dependency
edge. Dependency SCC processing equates qualifying copy/parent representatives.
Value/effect forests remain separate; physical immutable term and source rows
retain provenance. Solving, capture, freshening and fresh-row identity observation
resolve canonical representatives.

Union retains both bound sides, minimum level and combined non-generic state.
Generation-aware pair completion and subsequent propagation revisit comparisons
affected by equality. Incoming transactions journal representative forests,
parents, bounds, metadata, pair completions and diagnostic state.

Recursive definition components register all live roots before processing
member schedules. Internal occurrences route to those open roots with their
actual use row, occurrence and cause. All schedules run before any member graph
is captured for publication. This supplies ordinary monomorphic internal uses;
it does not claim polymorphic recursion. Live local schemes retain root and
boundary, without imposing initializer finalization before continuation.

## Initial review and accepted repairs

The frozen initial six-file artifact passed candidate/default owning builds
without warnings. Initial independent semantic/resource review accepted three
major repairs:

1. Later incoming freshening must recapture from the current live root, so
   bounds added by postcapture union survive in later fresh copies. The static
   counterexample is a private-kernel trace, not an established public-source
   failure. Stored graphs retain historical observation identity.
2. Dependency/SCC/merge scratch must remain charged while merging and related
   resource sampling still retain those allocations, including error cleanup.
3. Diagnostic edge membership must avoid repeated linear scans, and memo and
   completion undo must preserve transaction-entry state once per key. New
   transaction pairs use the existing admission rollback rather than duplicate
   memo snapshots. Auxiliary indexes and insertion journals require rollback
   and capacity accounting.

The first batched repair passed both owning builds without warnings. Fresh
semantic/resource delta review closed all three initial findings, then exposed
two direct repair dependencies: fresh-use observations paired a new row map
with the old definition snapshot, and the additional resource samples repeatedly
scanned saved memo child capacities. A second fresh producer now repairs these
as one bundle by retaining the exact per-use graph and caching the checked
nested memo-capacity subtotal. Second semantic/resource delta closed graph/map correspondence and cached
accounting. Semantic review additionally found that graph-pointer row identity
breaks existing source-row correspondence assertions across export/use snapshots.
The third bounded repair threads borrowed solver-state context through observers
and compares canonical kind-qualified source keys within one session. Structural
node identity and snapshot contents remain historical. No expected output or
test assertion is altered. Final fresh semantic delta closed the source-identity finding without further
findings. The clean resource review carries forward because this repair adds
only borrowed context. All accepted majors are closed within their inspected
implementation scope.
No runtime tests or measurements have run.

## Final deterministic evidence and integration

The frozen final artifact passed:

- `RUSTC_WRAPPER= cargo check -p yu-solver --features shadow-apply-candidate -j 2 --offline`
- `RUSTC_WRAPPER= cargo check -p yu-solver -j 2 --offline`
- `git diff --check`

Both owning configurations completed without warnings. The default check covers
the unchanged default dependency subset; the final observer-only change is
feature gated. Initial M2 semantic/resource reviews and fresh repair delta
reviews closed all accepted majors. The last borrowed observer repair required
one fresh semantic reviewer; its clean resource result carried forward. No
runtime tests, failure-injection probes, broader workspace checks or performance
measurements were added or run. Their absence is a verification limit, not
runtime or public-source certification. Measurement budget consumed: zero
samples and zero benchmark processes.

Primary-owned task, design index and decision implementation-status records are
synchronized in this checkpoint. Pending questions are excluded from staging.
The working branch remains `research/simple-sub-intrusion`; no target-branch
cutover is claimed.

## Costs and retained boundaries

Expected work per SCC pass is proportional to interned rows, structural Function
nodes, dependencies and parent records after forest compression. Dirty passes,
representative-chain walks, lower/upper bound cross-products, generation
invalidation, per-use graph recapture/reconstruction and diagnostic propagation
add work. Each incoming use retains its actual capture graph alongside the
fresh row map; retained storage includes the sum of those graphs and maps.
Exact diagnostic-edge hash membership avoids repeated linear duplicate scans;
first-write memo undo copies each touched old memo once. Undo capacity reporting
reads a checked cached nested subtotal rather than scanning those copies. There is no overall linearity or timing claim. Historical physical
bounds and pair keys remain retained. Resource evidence follows the repository
logical-capacity convention, not RSS or exhaustive allocator-failure peaks.

Source-row identity compares canonical kind-qualified keys in the same solver
state across export/use snapshots. Fresh-row identity compares instantiated
representatives. Structural node identity remains graph/index identity; observed
snapshot content and locality remain historical. Complete Call construction,
structured effects/protection, source/public correspondence, soundness,
principality and replacement of F5 on `yulang3` remain open. Default F5 selection
is unchanged. Pending question bundles remain outside this checkpoint.
