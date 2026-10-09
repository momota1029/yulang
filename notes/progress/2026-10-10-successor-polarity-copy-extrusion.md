# Successor polarity-copy extrusion

Date: 2026-10-10
Branch: `research/simple-sub-intrusion`
Code baseline: `280d399e4e7e1ddcaacf2c1c6d8cf882ec88dc57`
Integrated record-only upstream: `8d67b2f5a`
Scope: private mixed-graph bound ownership, extrusion and fresh-use replay
Authority: current Simple-sub correction and existing four-port variance;
no new language/Call interpretation or production cutover
Mode: M2; independent compiler-referee and performance-auditor
Status: reviewed implementation checkpoint; runtime behavior unverified

## Owning implementation

The new `candidate_extrusion.rs` implements the pinned Simple-sub operation
with kind-qualified, polarity/target-level memo keys. Rows already at or below
the boundary retain their identity. Younger rows receive fresh representatives
at the target level; originals retain their levels and metadata. Positive copies
receive selected lower bounds and an original upper link; negative copies receive
selected upper bounds and an original lower link. These are one-sided installed
memberships, not calls that install the opposite side through full comparison.

Both value and effect rows participate. Function argument and argument-effect
reverse polarity; result-effect and result preserve it. Structural reconstruction
and selected-bound initialization are iterative. Row identities are memoized
before following bounds. A separate pending-bound lane waits for the structural
stack to drain, preventing Function/row bound cycles from repeatedly rebuilding
an unfinished Function. Unchanged structural nodes are reused.

Graph-mode comparison selects its receiving bound owner using actual row levels
and replays direct plus structural opposite bounds. Structural comparisons use
the transformed endpoint on the owning worklist; their original diagnostic parent
remains pending until the existing completion mechanism resolves its child.
Ordinary F5 and legacy candidate solving retain paired edges and in-place aging.

Graph schemes now retain each bound's owner side. Fresh-use restoration installs
that side before processing its induced comparisons with the actual incoming
occurrence/cause. Idle-solver restoration and active-worklist replay are distinct
entrypoints, avoiding recursive worklist execution and mutation of completed
diagnostic parents. Existing journals own original-bound/flag restoration,
fresh-row/term truncation and typed-pair/diagnostic/route rollback.

## Review and costs

Both independent reviews found no BLOCKING, major or minor correctness finding
in the frozen solver delta. The semantic reviewer traced polarized identities,
four-port rebuilding, directional ownership, diagnostics, scheme restoration
and rollback against pinned `Typer.scala:88–181`. Moving HIR carrier semantics
and runtime inference were excluded.

The resource reviewer found expected local traversal/scratch proportional to
visited polarized endpoint keys and selected memberships per extrusion, excluding
solver propagation, journalling and allocation-event sampling. Aggregate costs
are not linear: interleaving P positive and N negative copies of one young source
can accumulate and visit Theta(P*N) copied memberships. A row with L lower and U
upper memberships incurs Theta(L*U) replay attempts before pair deduplication,
plus diagnostic/provenance settlement. No overall speed, bounded aggregate
resource or practical-cap claim is made.

Successful samples include both memo tables and work lanes using logical
capacity accounting. Failed-attempt high-water footprints, HashMap control/
allocator storage and RSS are not certified. No persistent cache or new limit
was added. Measurement consumption: zero processes and samples.

## Verification

Primary checks passed without warnings on the combined frozen dependency state:

```text
RUSTC_WRAPPER= cargo check -p yu-hir --features shadow -j 2 --offline
RUSTC_WRAPPER= cargo check -p yu-solver --features shadow-apply-candidate -j 2 --offline
RUSTC_WRAPPER= cargo check -p yu-solver -j 2 --offline
git diff --check
```

The separate generic local-source HIR carrier was frozen during these checks;
its static reviews/repairs remain separate and it is excluded from this solver
commit. Its existing enums and old entrypoint signatures are unchanged. No
test, execution probe, benchmark or workspace-wide suite ran; existing legacy/
model tests do not execute this new graph-copy path.

Reviewed solver SHA-256:

- `lib.rs`: `5397be9dafe90e7b2fc8f350f0ab3fa700c87b3c0a41631dad901936d822ac51`
- `candidate_extrusion.rs`: `04b7688ba2e5c4bf56536c207a8a16284d71f9f52cfe4688ebc344ba7bd7bde3`
- `candidate_scheme.rs`: `5e73d90bb962ea336718cb26b8e04b99d492c16694e45e9e3f966298c312c514`

## Remaining source integration

Current admitted source/formal/fresh-use rows are level one. This checkpoint
provides the cross-level kernel, not an executed ordinary-source cross-level
witness. General local initializer levels, sequential solve/freeze/install/use
scheduling, general anchor closure and local computation effects remain next
owning work. The new flat HIR source carrier is being independently reviewed;
its presence alone cannot establish local polymorphic inference.

Complete Call/protection/provider/world/image/admission/license/future behavior,
structured effects, ordinary public extraction and `yulang3` F5 replacement
remain open. No proof-DAG or full Call/production gate is closed. The full
inference/replacement goal remains active.
