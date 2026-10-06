# Frozen Oracle receiver-anchor registration: bounded historical trace

Date: 2026-10-08
Yulang3 baseline: `b7687afb33b1ae3367986c6f95145eb17820de74`
Frozen Oracle: `/tmp/yulang2-oracle-rebuild`, `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Status: frozen research-only bounded characterization; independent review pending
Exclusive lease: this note only
Semantic and implementation authority: none

## Objective, method and result

Seek a distinct historical constructor→identity→consumer mechanism for
source-owned receiver provenance or complete ordinary Call contribution,
beside the already characterized App/formal/frame, selection, SCC use,
Specializer2, Function path/projection, declaration slots, cast, synthetic App
and pattern-boundary routes. This is bounded static archaeology, with a
conditional data-dependency discriminator; no Oracle execution is evidence.

A separate mechanism retains **method receiver lowering anchors** and moves
them into a method-owned pending conformance record. Its consumer snapshots
the settled body value/effect and subsequently connects deferred requirement
edges. This is a historical declaration/body anchor analogue. It does not
provide the original ordinary Call primitive
`OriginalAssocType_X(beta,p0,j_call;s,c)` or its complete-family witness under
one original `xi=(nu,K,D)`.

The bounded novelty claim is exact: scoped searches in the October 6–8
Frozen Oracle note family found no mention of `ReceiverMethodLoweringAnchors`,
`receiver_anchors`, `capture_receiver_actual_view`, or
`pending_role_impl_conformance`. The declaration-slot and stored-signature
notes already cover declaration identity and binder bridges; this note's
additional seam is the body-anchor tuple and deferred snapshot consumer.
Absence of those symbol names does not establish that every prose-level
analogy is new. No repository-wide absence theorem is claimed.

## Authority, hypotheses and claim classes

The primary fixed the `ORIGINAL_ASSOC` target and the historical-only Oracle
boundary. Current authority is inferred-call-views §§1–5, especially §2's
source-owned static identities, typed paths and joint original assignment,
and §5's explicitly open construction rules. Source-contracts §§2.1–3 and
10 take independently typed primitive and owner/view kernels as inputs and
leave production adequacy and implementation unestablished. Approved Option
2 allows production observations without source executions; unannotated
formal refinement, annotation-scoped `io` permission, actual callable roles
and callback B remain the selected meanings.

The exact missing premise is an independently typed original introduction
owning the original slot and complete invocation contribution at `beta,p0`,
preserving every legitimate original witness, source arm, scope, providers and
shared `xi`, independently of pending comparison `Q`. No equation such as
`s=p0` or `c=j_call` is assumed.

- **H-bytes:** the source windows are the hashed files below at the assigned
  pins. Reading Git metadata with `sed` confirmed both assigned SHA values;
  committed-blob equality and full worktree cleanliness were not checked.
- **H-route:** a successfully resolved implementation method has a receiver,
  requirement and conformance shadow target, with the enabling shadow flag;
  annotation and body lowering succeed.
- **H-clean:** requirement preparation returns the Clean plain-parameter
  class; the completed descriptor passes the structural gate.
- **H-settle:** the component reaches the capture lifecycle with the same
  retained descriptor and bridge. No solver correctness or completeness is
  inferred from that control route.
- **H-pure-query:** for the local discriminator, use the same constraint
  machine state and bridge with deterministic compact/normalization routines.
  Their semantic validity is not a conclusion of this note.

Established observations here are inspected data fields, assignments,
branches and ordering. The trace under H-route/H-clean/H-settle is bounded
historical characterization. The discriminator under H-pure-query is a
conditional representation result. Equating these anchors or snapshot
outputs with current original slots/contributions would be an unsupported
candidate bridge assumption. No current-language theorem, source
counterexample, licensing inversion or gate closure is established.

## Constructor→identity→consumer

All code locators below are relative to the frozen Oracle checkout.

1. `crates/infer/src/lowering/body/impl_decl.rs:438–454` allocates the method
   root, joins it to `method.def` through `typing.set_def`, queues `RegisterDef`
   and registers implementation/requirement membership where applicable.
   `:471–479` selects receiver requirement preparation using receiver,
   requirement, shadow-target and enablement guards. These are declaration
   and analysis identities, not an ordinary source App identity.
2. `lowering/expr/method_body.rs:544–600` creates and annotates a receiver
   TypeVar, prepares contextual requirement endpoints, and binds the receiver
   as a local. `:616–640` lowers the tail/body and restores the local/frame
   state. `:642–662` builds a Function lower constraint. Only **after these
   operations**, `:663–669` constructs `ReceiverMethodLoweringAnchors` with
   receiver, tail-parameter vector, body value/effect and method value.
   The fields are explicitly defined at `:46–52`.
3. At `method_body.rs:670–679`, an inactive deferred requirement receives the
   anchor tuple; an out-of-class descriptor connects its requirement
   immediately. `:686–693` also returns the tuple in the lowering result.
   `lowering/mod.rs:168–205` retains the requirement, contextual parameter
   uppers, spine cursor, lowering continuation, parameter-context class,
   signature-variable map and inference level beside the optional anchors.
   This is same-session sharing, not a demonstrated original `xi` theorem.
4. `body/impl_decl.rs:549–605` consumes the inactive descriptor when a bridge
   is present and the clean-parameter/gate tests pass. It marks SCC
   conformance pending, provisionally finishes the binding and inserts
   `PendingRoleImplConformance` **keyed by method DefId**. The payload
   (`body/mod.rs:1261–1296`) retains impl/member, module/site/name, bridge,
   deferred descriptor, optional snapshot, phase and edge-application count.
   It contains no Call occurrence, argument receipt or original slot field.
5. `body/mod.rs:1917–1946` sorts pending members and captures all Captured
   records before applying that batch's deferred requirement edges.
   `:1368–1419` checks descriptor/kind agreement; the receiver branch passes
   only `anchors.body_value`, `anchors.body_effect` and the bridge to
   `capture_receiver_actual_view`. `:1422–1436` separately exports only the
   **length** of the tail-parameter vector.
6. `role_impl_conformance.rs:48–55` forwards that call.
   `role_impl_conformance/view.rs:926–984` rejects a missing bridge, compacts
   the machine's body value/effect, shares one binder-identity resolver over
   their recursive variables, and normalizes them into the actual method
   view. This is a settled-surface consumer, not an original receiver/Call
   producer. `:987–1019` documents the effect projection and rejects weighted
   or non-atomic unsupported surfaces on the displayed branches.
7. `body/mod.rs:1948–1994` subsequently consumes deferred requirement edges,
   commits a provisional receiver binding only on success, and records a
   success/failure phase. `:1485–1533` dispatches the receiver descriptor to
   `method_body.rs:1025–1108`: it checks cleanliness/anchors, reasserts saved
   parameter upper edges, resumes the body requirement and connects body and
   method endpoints using saved signature variables/level. Thus the captured
   view can precede this deferred requirement batch, while receiver annotation,
   contextual parameter input, body and Function constraints already exist.
   It is not established to precede all solver queries.

The precise retained chain is:

```text
resolved implementation method + receiver/body lowering
  -> receiver/tail/body/method TypeVar anchors
  -> method-DefId pending descriptor + binder bridge
  -> settled body value/effect snapshot + tail count
  -> deferred requirement edges + provisional publication outcome
```

## Smallest conditional discriminator

Fix one machine state `M`, bridge `B` and body endpoints `v,e`. Consider two
well-formed anchor representations

```text
A  = (receiver=r,  tail=[], body_value=v, body_effect=e, method_value=m)
A' = (receiver=r', tail=[], body_value=v, body_effect=e, method_value=m)
r != r'
```

Keep the same pending receiver kind and matching descriptor anchor sort. The
capture function receives exactly `(M,v,e,B)` for either record
(`body/mod.rs:1400–1412`); the attached tail count is zero for both. Under
H-pure-query their exported actual views therefore coincide. This is a
one-coordinate minimal representation discriminator: no tuple difference
would discriminate anything. With a nonempty tail, replacing one parameter
identity at fixed length likewise does not change the capture arguments or
count. No surface realization of either pair is asserted or executed.

Consequently the exported body snapshot/count alone cannot recover the
receiver identity or all tail parameter identities. The full pending
descriptor still retains them; this is no claim that the full historical
pipeline loses the tuple, or that the receiver cannot indirectly constrain
body endpoints in an actual source program. The discriminator addresses the
shortcut “the exported snapshot itself supplies original receiver ownership.”
It does not assume or refute a current source transition rule.

## Failure branches, independence and stop

No receiver takes the receiverless branch with `receiver_anchors=None`
(`method_body.rs:465–542`). Without requirement/shadow-target/enablement,
the pending route is unavailable. Clean preparation is distinct from
MutatedBridge and Unsupported: the latter use immediate fallback plans
(`:897–936`). The clean test requires equal vector lengths, every upper
present and anchors present (`:1924–1940`); the pending gate additionally
checks receiver sort, consumed Function-layer count and no whole-value upper
connection (`impl_decl.rs:641–664`). Failed gates connect requirements
directly (`:608–621`). Missing descriptor, anchors or matching kind makes
capture unavailable (`body/mod.rs:1372–1418`); missing bridge and unsupported
surfaces are also retained. An ordinary SCC blocker supplies
`OrdinarySccBlocker` rather than a sound snapshot (`:1828–1861`). Failed
requirement connection/publication produces FailedAndEdgesApplied
(`:1967–1993`). These checks do not prove exhaustive source coverage.

Oracle source independently grounds the historical storage/API chain; its
lowerer, solver, compact projection and normalizer share one implementation's
assumptions. Their agreement supplies no independent source semantics oracle.
No checker was written, no execution/output was used, and no transition-rule
assumption was promoted to proof. No seeds, enumeration ranges, samples or
applied mutations exist. The two representation substitutions above are
paper dependency discriminators, not tested source mutations.

Stop condition reached: the one uncovered anchor-registry candidate has a
concrete constructor and consumer, but both operate on declaration/body
inference endpoints. They introduce no ordinary Call identity, stable
`beta/Slots(beta)`, typed `p0`, receipt, complete invocation family,
original `(s,c)` interpretation or preserved original `xi`. Repeating endpoint
probes on this registry would leave the same missing original typed
owner/view introduction untouched.

Recommended next action: retain this as a bounded historical analogue, stop
receiver-registry archaeology, and construct the current original
slot/contribution introduction from its independently typed source premises.
`ORIGINAL_ASSOC`, complete Call typing and dependent licensing gates stay open.

## Checks, resources and unverified scope

Read the three assigned rules in full, task frontier/research seed/index,
governing design sections, and existing notes needed to exclude duplicate
mechanisms. Used serial lightweight `rg`, `sed`, `nl`, and `sha256sum` shell
reads. Initial broad receiver/owner search output truncated and included a
nonexistent `context` directory; narrowed file/symbol searches and exact
windows supplied every decisive citation. Later guessed body/view file paths
also failed; resolved actual paths are the citations above. No conclusion
depends on complete initial search output. Metadata reads confirmed the pins.

One serial lightweight shell command at a time; zero builds/tests/executions,
Git commands/mutations, formatting, child agents or scratch outputs. The
leased note is the entire write set. Work remained within the 15-minute
assignment; precise CPU time, peak RSS and wall time were not instrumented.
Full solver/normalizer correctness, source realizability of the discriminator,
generalization/serialization transport, all role/method branches, any other
Oracle registry, repository-wide absence and current production conformance
remain unverified. The artifact freezes on submission; its producer does not
claim independent review.

| Direct dependency | SHA-256 at freeze |
| --- | --- |
| Inferred-call-views design | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| Source-contracts design | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| Oracle `lowering/expr/method_body.rs` | `3319db30fd3d6771eea156a2b902372c59db75ce1e27f64fcb44d987c3e52b74` |
| Oracle `lowering/body/impl_decl.rs` | `7353af913f609b32502e8a0c18515aee95ef7419dc478432a9444b13e80d7b05` |
| Oracle `lowering/body/mod.rs` | `f5e82c2109a11938cab6a5b48d8a155f6ac3029c4d26cb7f4570790e8d5f9cb1` |
| Oracle `lowering/mod.rs` | `244e5f8ea339d2e24aa1f8456e99072e4a491b97da58348a4e79eed188ce61a1` |
| Oracle `role_impl_conformance.rs` | `92b328ad27289dcb10d2d228d6ee4aa53f8ebbdc8bb7a19243e6d47b59321041` |
| Oracle `role_impl_conformance/view.rs` | `94130ef703f4775f10a46d9706f165a9b588195bff280242d1da66ec49aec835` |

## Commit packet

- Exact leased path: `notes/progress/2026-10-08-frozen-oracle-receiver-registration-archaeology.md`.
- Baseline: Yulang3 `b7687afb33b1ae3367986c6f95145eb17820de74`; Oracle
  `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Dependency changes: none observed in the final hash recheck; pin-to-blob
  equality remains unverified. Hashes above identify the inspected bytes.
- Claim/review status: frozen bounded historical characterization and
  conditional representation discriminator; independent review pending.
- Checks run: scoped symbol/novelty searches, exact constructor/consumer and
  failure windows, metadata SHA reads, direct-dependency hash recheck, and
  leased-note reread. No test/build or semantic execution.
- Proposed commit message: `research: trace Frozen Oracle receiver anchor registration`.
- Shared-record deltas left for primary/curator: optionally add the
  declaration/body anchor→method pending record→settled snapshot analogue to
  the current frontier's dispatch-avoidance inventory; retain every open gate
  and existing authority boundary. No theory status promotion is proposed.
