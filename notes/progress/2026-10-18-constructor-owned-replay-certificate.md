# Constructor-owned Replay certificate implementation progress

Sprint `npair-constructor-owned-replay-certificate-20261018`, rev3, contract
SHA-256 `c3e21e367b90a3d13165139cade12c2730f5a38ad3beb2ec1ec5a923c4fe1047`.
Baseline `c881f5960`. Parent gate remains OPEN; no theorem, semantic approval,
or production authorization is claimed here.

## Source construction and verifier change

`candidate_insert_bound_with_evidence` reads back the exact item at the
addressed physical row/atom slot for each of the eight lanes after append. It
reconstructs the complete `BoundKey`, compares it with the expected owner,
polarity, and item, then stores `PhysicalBoundReadback { slot, bound, phase }`
inside the existing `BoundEmission`. This is fixed-size and included in the
existing `size_of::<BoundEmission>()` capacity accounting. No vector copy or
parallel slot registry was added. The candidate slot arrays are append-only;
the lifecycle proof owner audits that every truncation/reuse is paired with
evidence rollback. Post-solve verification relies on that constructor-time
readback and the retained emission record, not on discarded vectors.

The checker now obtains a unique source-to-p1 FreshUse `Transport` from the
retained dependency, checks its exact endpoint witness, admission, imported
snapshot, emission/readback record, and full target-fiber membership. Separately
it checks the exact `Replay { child:q, lower:l, upper:h }` dependency and recipe,
requires `h == p1` by `RelationId`, requires `H == B`, checks p1 in the full
upper fiber, and checks that the lower fiber is nonempty and contains l. q
remains a separate relation. Root or term equality and incoming-edge counts do
not establish these links. A successful `InferenceSession::execute` is the
precondition for final inference observation; retired Replay operation records
are not retained after completion.

For the fixture's direct consumer case, `C == q` is explicitly the zero-step
consumer identity. The verifier checks the four ordered and distinct
`FunctionPort` dependencies of q, their value/effect pair kinds, no child
demand, identity transforms for Argument and Result, exact
`stamp_input(demand.input)` for ArgumentEffect, and exact
`protect_body(demand.output_scope, demand.input)` for ResultEffect. The
observer reports p1, q, h, C, physical slot/readback, and port relation and
transformer IDs. This remains diagnostic source evidence and does not change
solver behavior.

## Positive and negative evidence authored

Positive controls require actual module and local route owners, two distinct
same-source uses, p1=h by relation identity, q different from h, C=q, exact
slot readback, scope/input mapping, and all four port equations. The public
candidate graph-call harness additionally checks the p1/h/q identities and
retains raw native-root mismatch as a separate observation.

Actual-record mutations are authored for: out-of-range index; wrong physical
owner and lane; wrong complete readback `BoundKey`; orphaned admission link and
replacement by another emission; wrong FreshUse endpoint; replacement of the
actual Replay dependency kind; changed actual effect-port transformer and
child-demand flow; and changed captured snapshot and retained scoped flow for
both route owners. Each mutation asserts rejection and restores the saved
record. Existing use/call/root/Replay tuple substitutions remain in place as
separate negative controls. The stale slot after reuse case is represented by
an actual emission address/readback mismatch; the lifecycle proof must confirm
that no post-constructor slot write or unpaired rollback can invalidate the
retained constructor observation.

## Evidence and limits

The rev1 owner map received an independent CLEAN review; rev3's Sol lifecycle
proof and fresh final proof/compiler review are separate and still required.
This implementation lane has not run Cargo, tests, runtime commands, formatter,
or Git. No executable result is claimed. Runtime remains forbidden until the
fresh frozen proof and compiler delta receive CLEAN reviews. A failed positive
control or a lifecycle counterexample blocks dependent use; expectations,
diagnostics, and solver semantics must not be changed to obtain green output.

Implementation stage interval: `[307400705040044, 308234430208193] ns`,
833.725s charged of 900s; unused 66.275s expired. Separate mutation stage start:
`308272117603925 ns`, stopped at `308671280849144 ns`, 399.163s charged of
480s; unused 80.837s expired. Requested model/effort Luna/high; observed
model/effort UNKNOWN. Independent review is not self-certified.

## Frozen implementation hashes and stop receipt

The author stopped code and authored mutation changes at
`308671280849144 ns`; mutation-stage interval was
`[308272117603925, 308671280849144] ns` (399.163s charged of 480s; 80.837s
expired). The prior implementation interval was
`[307400705040044, 308234430208193] ns` (833.725s of 900s; 66.275s expired).
The separate 240s freeze stage permits only these receipt documents to change.
No tests, Cargo, runtime, Git or formatter ran. Worker state STOPPED; no
descendants. The rev1 owner-map review was CLEAN; rev3 final independent proof
and compiler review remain pending. Parent theorem closure remains 0.

Frozen code/example hashes at the mutation-stage stop:

- `candidate_context.rs`: `3aa782c35ba049708c0268653c69f918553cecda287fbec97f1d61541fa1a02e`
- `candidate_scheme.rs`: `820ca039203dcbaae1b846e923133a185d4c397d264a6f8d7357f15c724e1bc0`
- `candidate_extrusion.rs`: `fc0d948d884a406746066f3df8db257d5c6686505166b330bef839a9b9e2f35d`
- `shadow_apply.rs`: `6214ec7160822f6e49553083fdbed6b9c5c9893c15ae23c26809252ee740d86c`
- `candidate_graph_call.rs`: `7ff60ecb30e3815ba703463c87f053d66bf2d0c1833784dc64f993203fcdf5ef`
- `research_scoped_formal_replay.rs` (unchanged): `e4c1bec2a41accfe09f664d5992b2575ce78b855c3ff622f08eeb6de8765e3d3`

The mutation-stage report hashes before the final receipt-only update were
progress note `96c12b5349851995ce945e6b1007c95e96e079cd06ad2a6edf393850402c46dc`
and inbox handoff `d07350f8918c6fa06696c4912a4e92b0be9445e6d6d06fce5fc31f4c9742941a`.
The receipt-only documentation stage started at `308717833238899 ns`; the
primary STOP receipt records its exact final boundary and elapsed charge.
Final hashes after this documentation-only stage are primary-captured. No
source/example changes were made during it. All eight leased paths and these
two receipt paths are STOPPED pending independent review and primary
integration.
