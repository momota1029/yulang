# R19: source ordering and the missing FieldBound FreshUse consumer

Status: FROZEN research artifact; independent review NOT_RUN. Method: read-only
constructor/consumer falsification, complementary to the separate prover lane.
Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, OPEN, closure 0.

## Baseline and authority

Semantic/source baseline: `d51baa6db0218fce6fc665d9da8cd0863fb23904`.
Observed integration HEAD at entry: `eeafa05c58a62f0a447a061520620368bdc59a9e`.
R19 contract SHA-256:
`75eba332166f8ffece47fe2ccbe6513058b151cc76fa74545ba56c3ca70977fd`.
All eight pinned solver/design dependencies checked below match the contract;
the R18 correspondence note and operation-catch fixture also match. The live
`current.json` is mutable primary-owned scheduling state; its acknowledged
launch-state drift supplies no proof premise.

Governing sections: R19 **Fixed outcome**, **Required source and native owners**,
**Independent falsification lane**, **Baseline pins**, and **Stop conditions and
parent application**; revision-6 design **Fixed source identity**, **New typed
source constructors**, **Native lower realizer and exact consumer**, and **Phase
boundary and present sprint outcome**. Apply the unchanged meanings of owner
request `c`, distinct callback realizer `c_outer`, and `AnnotationMember` versus
`Contribution`. Rules read: root operating map and pre-sprint map,
research-lab/current and pre-sprint rules, design-authority, git-concurrency,
goal-driven-sprints, top-level inference principles, and proof/sprint skills.
This packet selects no new language meaning.

## Result and exact premises

**Bounded source characterization:** Install does not freeze a Graph. Each
ordinary local use captures a Graph immediately before constructing its own
FreshUse. Source collection appends FieldBoundV1 actions after the ordinary
local-use actions. Consequently, in a successful execution that reaches such
uses in the same root schedule, those completed captures precede creation of
that root's typed `q`, `m0`, and `FieldBoundV1` record.

The execution premise matters: no parser, candidate solver, or runtime was run
for the proposed two-use source below. This is an obstruction to the claim that
the already captured Graph directly contains that later-created typed record;
it is not an accepted-program counterexample to the parent theorem. No genuine
sibling-receipt acceptance counterexample was established in this packet.

This result does **not** imply that all callback effects are absent before the
final action, or that late constraints cannot affect shared older anchors.
The catch constructor creates a q-owned allowance view, negative row, and
generic effect bound earlier. Generic flow through those coordinates must be
distinguished from transport of the typed source certificate.

## Actual constructor and action order

| Owner | Source fact |
| --- | --- |
| `candidate_source.rs:651–765` | `operation_v1_catch_source` follows exact catch/declaration/binder, `k response` callee/argument resolution, annotated local response initializer, and callback operation. Its scrutinee check here requires an immediate Apply/Operation. This collects `h_arg`, not a dynamic invocation. |
| `candidate_source.rs:1034–1040,1090–1125` | Block work visits each initializer before Install and visits the final expression after the bindings. Install follows initialization-effect facts; annotation uses LocalAnnotation instead. |
| `candidate_source.rs:1056–1082` | CatchArms records a deferred `(declaration,h_arg)` and emits CatchOperation before arm-body traversal. |
| `candidate_effect.rs:962–995` | CatchOperation creates `q_view`, the negative response row, its slot-249 bound to Allowance(q_view), and PreparedFieldV1. These precede the complete typed record. |
| `candidate_source.rs:1245–1252` | A nonrecursive Name resolved to a local binder emits Action::Local for that exact slot/occurrence. Active recursive initializers instead emit Link. |
| `candidate_source.rs:1448` | After the ordinary traversal finishes, deferred FieldBoundV1 actions are appended. |
| `candidate_source.rs:1621–1627,1642–1652,1688–1691` | Publication installs a local scheme and advances the schedule; ordinary local actions route synchronously; FieldBoundV1 calls its distinct producer. Suspension before publication does not execute a later action first. |
| `candidate_scheme.rs:1954–1974` | Install stores `LocalScheme { capture_region,id,root,boundary }`; no Graph is captured here. |
| `candidate_scheme.rs:1998–2028` | Each ordinary local route obtains the installed scheme, rejects duplicate occurrence routing, captures `Graph` at line 2023, then prepares its FreshUse at line 2024. |
| `candidate_scheme.rs:2151–2169` | Local routing restores the captured bounds before connecting that use's reconstructed root to its target component. |
| `candidate_effect.rs:1039–1096` | The final producer identifies the exact callback operation view and prepared handler argument, constructs typed q/m0 plus FieldBoundV1 at 1075–1089, constrains the original member/allowance pair, and marks consumed only after successful propagation. |

Thus for two successfully reached ordinary g Names `u1,u2` in this root:

```text
CatchOperation: prepared q_view/negative row/h_arg
  ... initializer and arm actions ...
Install(g): root/boundary/capture_region
Local(u1): Capture(G1) -> FreshUse(U1) -> restore G1 -> link use value
Local(u2): Capture(G2) -> FreshUse(U2) -> restore G2 -> link use value
FieldBoundV1: typed q,m0,record -> original native pair drain -> consumed
```

G2 need not equal G1: the second capture can observe constraints added by the
first route. Neither capture directly snapshots a record not yet constructed.

## Smallest timing witness and two-use candidate

One local use suffices to expose the timing premise. A second use is needed
to distinguish sibling authorization. The following is a **source candidate**
derived from the pinned operation-catch response fixture and R18 callback shape;
its parse, unchanged-solver acceptance, and runtime behavior are unverified:

```yu
act outer:
    our next: () -> int
act signal:
    our ping: () -> (int -> [outer] int)
my result = {
    my g = catch signal::ping() {
        signal::ping(), k -> {
            my response: int -> [outer] int = \x -> outer::next();
            k response
        }, v -> v
    };
    my first = g 0;
    g 0
}
```

The smallest exact falsified *candidate assumption*, conditional on reaching
the first route, is: “its captured Graph already contains this root's completed
FieldBoundV1 record.” The first source-owner boundary is deferred action
placement at `candidate_source.rs:1448`; the first capture boundary is
`candidate_scheme.rs:2023`. A stronger semantic or acceptance claim needs actual
source acceptance and an owner-level typed certificate/use consumer bridge.

This candidate contains two static g Name occurrences, not measured dynamic
cells/events. Their authenticity follows only conditionally through the real
Action::Local constructor, not from spelling or type equality. Distinct g
occurrences route separately and `context.begin_use` increments its checked
counter (`candidate_context.rs:2997–3000`), yielding distinct U1/U2 if both
constructions succeed. They can share nongeneric rows; disjoint endpoint sets
are not asserted. No synthetic FreshUse or receipt injection was performed.

## Endpoint, context, scope, snapshot, and physical consumer

The existing transport is substantive. `prepare_candidate_fresh_use`
(`candidate_scheme.rs:1542–1843`) allocates a context-use ID; remaps owned
scopes/inputs when scoped mode is enabled; canonicalizes and freshens eligible
rows while retaining older/nongeneric anchors; reconstructs terms; remaps
Support/Allowance/AnnotationMember views and tails; renames context weights and
contexts; maps scoped demands including root/input/output scope; and imports
the captured evidence snapshots. Member ordinals are preserved. Scope maps are
empty defaults outside scoped mode; this audit does not assume ordinary v1
execution enables scoped mode.

`begin_candidate_fresh_bound` (`1846–1892`) reconstructs lower/upper with their
polarities, preserves captured owner orientation, transports the captured
relation using this FreshUse's context-use/context/scope maps, and admits
`FreshUse { antecedent,use_origin,source_bound,mapped_relation }`.
`candidate_extrusion.rs:763–875` inserts a physical bound with that evidence,
retains a restoration, replays the saved opposite frontier through actual
typed children, and returns the emission only when restoration completes.
The additional direct dependency `candidate_extrusion.rs` was checked equal
to d51baa6db bytes; SHA-256
`fc0d948d884a406746066f3df8db257d5c6686505166b330bef839a9b9e2f35d`.

`candidate_context.rs:1772–1810` authenticates the immutable captured/imported
snapshot and the exact FreshUse admission, mapped relation, target BoundKey,
unique emission, physical slot/readback, and ConstructorAfterAppend phase.
`candidate_scheme.rs:393–475` also checks use-instance, captured negative root,
relation, imported snapshot, and scope/input maps before demand authentication.
These checks give no static reason to claim a sibling bypass. Existing mutation
tests at `candidate_scheme.rs:2480–2544` cover wrong use, root, sibling relation,
and scope-related inputs, but were **read only**, not executed here.

The missing typed bridge is visible at both ends. Graph (`candidate_scheme.rs:
40–56`) contains nodes/rows/bounds, generic snapshots, attachments, contexts and
regions; FreshUse (`233–244`) has the above remaps. Neither directly stores a
FieldBoundV1/q/m0 payload or its per-use transport map. EvidenceSnapshot
(`candidate_context.rs:520–524`) retains bound/relation/admission/emission heads
and coverage, not that typed record. Snapshot authentication explicitly avoids
sampling a later current evidence head. This does not preclude all future
reconstruction arguments; none is established by these generic fields alone.

The final FieldBound producer calls `constrain_live_effect(lower,upper)` using
the callback Apply slot 250 and records global `consumed`; it does not call
`begin_candidate_fresh_bound` for U1/U2. Public receipt projection
(`shadow_apply.rs:507–523`) exposes request/callback/response identities and
consumed after final inference success, without g binder, local route, context
use, mapped endpoints, scope, or FreshUse physical-emission identity. A Phase-S
receipt therefore cannot by itself certify either sibling's own consumer.
Accepting it as such would be an additional unsupported bridge, not an observed
compiler acceptance bug established here.

## Coverage, independence, resources, and next action

Commands: read-only `cat`, `sed`, `rg -n`, `sha256sum`, `git rev-parse`,
`git status --short`, and baseline `git show ... | sha256sum`; one clock read.
All returned successfully. Solver/design pins and supplemental extrusion pin
matched. No tests, builds, probes, mutations, Git changes, descendant agents,
or writes outside the two leased Markdown artifacts. No seeds/ranges apply:
one static constructor path and one proposed two-use source shape were traced.
No exhaustive source-domain search, dynamic identities, actual two-use receipt,
or successful local-g typing/run was measured. CPU/RSS were not measured;
shell reads/hashes were lightweight. Requested cap: 360 seconds, one lane.

Oracle independence: no executable oracle was used. This audit reads the same
pinned implementation that the prover may inspect; source-order facts are
independent of any assumed toy transition system, but they are not independent
validation of the language semantics or of the prover's theorem. The existing
R18 result is accepted as a dependency, not rerun or independently reviewed.
Failure conditions: pin drift, an earlier q/m0 producer or retroactive Graph
update not accounted for, different scheduling order, source rejection before
the routes, or generic shared-anchor behavior invalidating a stronger claim.

Recommended next action: primary should assign the first source/capture owner
premise exposed here—typed evidence availability and exact per-use retention/
consumer correspondence—after the separate prover result and fresh review.
Use the unchanged solver acceptance boundary from the runtime lane before
promoting the candidate witness. No parent condition closes from this note.

## Commit packet

- Exact leased paths: `notes/theory/2026-10-18-fieldbound-freshuse-source-falsifier.md`;
  `tasks/agent-loop/inbox/20261018-fieldbound-freshuse-source-falsifier.md`.
- Baseline: `d51baa6db0218fce6fc665d9da8cd0863fb23904`; contract hash above.
- Changed immutable dependency hashes: none; supplemental extrusion pin above.
- Review: NOT_RUN; research-only bounded characterization and conditional timing
  obstruction; no theorem/production/independent-review certification.
- Checks already run: source/consumer reads and dependency hashes only.
- Proposed message: `research: record R19 FieldBound capture timing obstruction`.
- Shared-record deltas left for primary/curator: correct Install-versus-capture
  terminology; retain parent OPEN/closure0; record exact missing typed use bridge,
  candidate acceptance UNKNOWN, supplemental dependency, and review disposition.
- Writer state: frozen; no further writes after submission without new handoff.
