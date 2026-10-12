# Nested Call: occurrence retention at the actual level crossing

Status: bounded source characterization; unreviewed research checkpoint; frozen
at handoff. Parent intrusion soundness/principality and production gates OPEN.
Baseline: `e5e7b5878ced01b8cc4682492b6187c3907fd014`, branch supplied by primary:
`research/simple-sub-intrusion`. Exclusive write lease: this note only.

## Objective, method and premises

Follow one inner `f y` demand from source identities to actual extrusion, and
test whether its origin `G`, receiver `F`, and generated polar pairs survive as
one retained event. This is a source audit complementary to the primary's
constructive prover lane. It is not independent certification of the existing
source audit, an executable run, or a new association rule.

Exact governing sections: top-level inference principles §§1–5;
`2026-10-10-parent-copy-scc-intrusion.md`, “Selected operation and compiler
responsibility”, “Value-reference SCC clarification”, and definition-root Value
ownership; `2026-10-12-intrusion-value-type-association.md`, “Approved
extrusion-event qualification”, “Qualification”, “Implementation and proof
boundary”, and “Earlier source-construction discriminator”. The selected
displayed event has origin G, receiver F, and pairs `(C,B,+,1)` and `(D,R,-,1)`.
Only an actual extrusion occurrence qualifies; freshening is not one. Value
identity is distinct from a solver Value row. No permanent type-variable owner,
copied Value incidence, encoding, or cache policy is selected here.

Operational and write limits follow `rules/research-lab.md` (different methods,
explicit dependencies, evidence quality), `rules/git-concurrency.md` (disjoint
lease and freeze), `rules/design-authority.md` (authority and proof boundary),
and `rules/compiler-engineering.md` (reconstruction debt). Artifact integration
is M0; theorem promotion would require the separate M3 gate and fresh review.
No reviewer was assigned by this producer. Runtime model/effort: unknown.

Hypotheses for the candidate prefix: an unannotated LocalSource is admitted with
the structure of `my f x = { my g y = f(y); g(x) }`; inner `f` resolves to the
module definition f, `y` to g's formal; the recursive internal-use route is
registered; outer type root o has level 1, inner formal b, callee Name row n,
result r and demand ports have level 2; allocation, bound admission and replay
succeed; no earlier equality changes these coordinates. This is hand evaluation
conditional on those concrete inputs, not evidence that the text was parsed or
executed. Only the first inner Call prefix is covered.

The native two-port reference is the original term:

```text
let rec f = lambda x.
  let rec g = lambda y. f y
  in g x
in f
```

At original Simple-sub pin `9bae772624c23b52a93c1b226157e16898b4d9db`,
`Typer.scala:48–55,62–72,115–123,143–156,205–207` directly produces
`o1 <: Function(B2,R2)`, then negative extrusion to 1 with the selected polar
pairs. The file was inspected; its hash is recorded below. It has no Yulang
Value graph or event extension and cannot prove that extension.

## Source-owned endpoint derivation, before any type-copy operation

G is the semantic value introduced by the nested binding g, identified here by
its retained `HirLocalId`; F is the semantic module-definition value identified
by resolved f and its registered definition root. These are binder identities,
not the b/r Function ports, the callee Name expression, or solver row n.

The origin can be obtained from this exact source, without guessing from levels:

1. `yu-hir/src/module/local_source.rs:163–171` retains g's identity, parameter y,
   and initializer index. Construction starts the initializer at
   `LocalInitializer(g)` (`329–364`). Its synthetic Lambda's body enters
   `Parameter(y)` (`359`), and Apply construction preserves that scope
   (`553–573`). Thus the inner Apply scope is **Parameter(y)**, not literally
   LocalInitializer(g).
2. The retained parameter entry for y has scope `LocalInitializer(g)`
   (`757–791`); for this one-parameter binding it leads directly to g.
   `candidate_source.rs:181–185` also explicitly constructs
   `parameter_scopes[y] = AnnotationScope::Local(g)` from the binding's
   parameter membership. That map currently serves annotations; using its
   observed membership here demonstrates source availability, not a newly
   approved global owner law.
3. While that initializer is traversed,
   `candidate_source.rs:300–305` retains `active_initializers[g] =
   endpoints[g.initializer]`; removal occurs only at Install (`307–309`). The
   inner Apply finishes before Install. The scoped binder g and its forming
   type endpoint are simultaneously available at source planning. The endpoint
   alone is not G; the retained binding identity supplies G under the already
   selected displayed-event rule. Selecting an arbitrary active HashMap entry
   would not generalize this derivation.

F comes from the callee's resolved binding, independently of target level:

1. The callee expression retains `LocalSourceResolution::ModuleDef(f)`
   (`local_source.rs:113–115,139–145`). In
   `candidate_source.rs:375–378`, that exact target and Name occurrence become
   a pending definition use and `Action::Module`.
2. The internal graph route activates actual definition roots and internal uses
   before source schedules (`candidate_scheme.rs:842–882`).
   `route_candidate_open_use:938–944` validates both registered ends;
   `lib.rs:15765–15782` obtains the resolved target-root coordinate o and the
   separate Name-use coordinate n and admits `o <: n`.
3. Therefore the resolved receiver is F even though the immediate Apply callee
   endpoint is n. Target level 1 describes the extrusion boundary; it does not
   identify F. A level is shared by many declarations and is no Value witness.

This finite reconstruction establishes that the **binding identities needed for
the accepted G/F association are available at the source owner**. It does not
establish a canonical semantic-Value registry, a rule for arbitrary scopes or
wrappers, or all-source association transport.

## Discriminating trace: two routine calls, one copying level crossing

Let d be the inner negative Function demand with ports
`(b2, argument_effect2, invocation_effect2, r2)`.

| Step | Concrete type work | Actual retained source information |
| --- | --- | --- |
| Module Name | `o1 <: n2` | Resolved target f and Name occurrence in the definition-use record. Row admission stores o as a lower bound of n (`candidate_extrusion.rs:816–831`). |
| Apply formation | `n2 <: d2` | `candidate_source.rs:394–410` retains expression index, callee/argument source indices, checking occurrence, cause and typed operands. `ApplySourceInput.owner` is `source.definition_root() = F` (`402`), not G. |
| First structural dispatch | `candidate_extrude(d, Negative, 2)` | `lib.rs:12428–12439` uses receiving **type row n**'s level. All four ports are already at level 2. `candidate_extrusion.rs:90–94,325–352` returns them and the Function unchanged, producing no parent pair. A call of this routine is insufficient evidence of the selected copying occurrence. |
| Bound replay | upper d on n meets lower o | `candidate_apply_value` stores d, then `candidate_replay_bound:763–803` requests `o1 <: d2`. The diagnostic parent records `(n,d) → (o,d)`; the executable replay joins the two retained bound relations. |
| Copying dispatch | `candidate_extrude(d, Negative, 1)` | Same demand d, now receiving older type root o (`lib.rs:12431–12435`). Function polarity reversal copies b positively and r negatively (`extrusion:224–253`); allocation installs `(c_b,b,+,1)` and `(c_r,r,-,1)` (`112–123`). Effect ports may also create pairs. |

The selected source event attaches the **nested definition Value G** to the
**resolved recursive definition Value F** at the last step. Its association is
not `(Y,F)` or `(inner Apply result,F)`, and is not supplied by the earlier
no-copy dispatch to n. G/F follows the accepted displayed-event decision plus
the actual source binding derivation above. The Value SCC comparison remains a
different operation from either type demand or replay relation.

### Replay retains lineage, but not the selected event certificate

Apply demand creation retains `NativeInterface` and its actual terms
(`shadow_apply.rs:1335–1387`), then admits a constraint carrying the inner Apply
checking occurrence/cause (`1390–1404`). `lib.rs:12138–12149` keeps that
occurrence/cause in the typed-drain frame and seeds a relation origin;
`candidate_context.rs:2496–2531` records `(relation, occurrence, inferred_entry)`.

Bound insertion obtains the currently processing pair/relation through
`candidate_extrusion.rs:389–397,453` → `candidate_effect.rs:420–429` →
`candidate_context.rs:2814–2854`; each attached bound relation preserves its
derivation parent. Replay uses the lower o-on-n and upper d-on-n relations,
creates a relation for `(o,d)` with their ordered Replay context, and retains
`Dependency::Replay {child,lower,upper,lower_input,upper_input}`
(`candidate_context.rs:2911–2982`). Queueing retains that child RelationId and a
ReplayOperationId acknowledgment (`1837–1841,3060–3104`). The original Apply
typed-drain cause continues to own diagnostic replay; the child's two-parent
derivation also includes the callee Name admission. It is not a new uniquely
selected G/F event cause.

Consequently, the current worklist can distinguish `(n,d)` from `(o,d)` and
their contextual derivations. Dispatch even has `item.relation` and the current
processing relation (`lib.rs:12259–12277`). **The direct extrusion call still
passes only `(d, polarity, target_level)`**, not that RelationId, a selected
source binding pair, or an actual extrusion-occurrence identity. The same d and
polarity with target 2 versus 1 distinguish these two routine invocations;
they do not identify G/F or group the produced pairs into the approved event.
This is absence of the explicit handoff, not proof that every source fact is
globally irrecoverable: relation origins and source indices remain elsewhere.

The first missing explicit source field is the selected **origin binding G** at
`candidate_source.rs:401–408`: the existing `owner` stores F. No event record
couples G with the resolved receiver F. The decisive later missing handoff is
an occurrence/certificate handle from dispatch into `candidate_extrude` and
`retain_extrusion_parent`; `Parent` retains only copy, parent, polarity, target
(`candidate_intrusion.rs:23–28,171–219`). Neither relation lineage nor an
Apply checking ID is already that handle.

## Memoization obstruction and consumer boundary

Within one copying call, `(endpoint,polarity,target)` memoization precedes bound
traversal (`extrusion:4–5,73–79,121–123`). A second visit to the same polar row
reuses its actual pair. Both signs remain different keys. Those facts support
retaining the produced pair set once per actual event, but supply no Value
association.

Across task replay, `lib.rs:12350–12374` can return for an already current
relation or reuse an already transformed diagnostic child. Currency is
**relation and generation sensitive** (`11463–11473`), not a bare endpoint-pair
cache. The ambiguous case is attribution when this displayed demand is revisited
and existing copying work is reused: neither Parent nor the transformed child
identifies which actual G/F extrusion produced its pair set. Conversely, a
different source origin reaching equivalent type/context work cannot be
classified as the same event merely from the cached pair. This latter case is
a missing invariant to investigate, not a second source-qualified witness:
no such distinct-origin execution was constructed in this packet. Cache misses,
hits, replay-operation IDs and source checking IDs must not silently choose an
event policy that Authority deliberately leaves open.

`TransportReason::Extrusion` likewise retains only operation endpoint, polarity
and target (`candidate_context.rs:220–230`; emitted at extrusion `304–322`).
Immediate consumers needing the selected record are: parent retention and pair
grouping; transformed-bound/replay transport; and intrusion settlement. The
inspected settlement compares canonical **type parent/copy** component IDs
(`candidate_intrusion.rs:375–404,474–486`), so it cannot consume G/F qualification.
Later generalization/fresh use would need to preserve the certificate, but its
complete lifecycle was not audited here and remains a separate source gate.

## Falsifier, independence, coverage and next action

The bounded absence claim would be refuted by a pinned constructor on this
route retaining an actual occurrence handle with G/F and the emitted pair set,
and a transport/consumer path reading those Value endpoints. An origin scope
field alone, a numeric level, type-row SCC equality, relation ancestry alone,
or another finite checker assuming the missing event does not refute it.

The source-availability derivation would fail if admitted HIR gives the inner
Apply a different scope, y belongs to another binding, f resolves elsewhere,
the use is not internal/open, levels differ, or canonicalization changes the
prefix. A native execution of the exact admitted route recording these fields
could discriminate those premises; none ran here. The Scala source independently
grounds ordinary two-port generation and polar copying only. Candidate hand
evaluation shares the inspected candidate transitions and cannot prove them
sound. G/F and Value qualification come from accepted Authority, not an oracle.

Checks: bounded `cat`, `rg`, `nl`/`sed`, `wc -l`, `sha256sum` source reads;
read-only `git rev-parse HEAD` and `git status --short` at startup confirmed the
full supplied baseline and a clean startup tree. One mistyped HIR path failed
and was corrected; some aggregated output truncated, with decisive windows
reread. No builds/tests, parser run, checker, mutation, seed/range enumeration,
performance measurement, compiler edit, Git mutation, or delegation occurred.
One leased-note write. Exact CPU/RSS and total wall use were not measured; no
heavy process ran and no explicit numerical wall/CPU/RAM allocation was given.

Recommended next action: primary assigns the smallest explicitly provisional
source/replay certificate construction for **this admitted prefix**, carrying
the proven-available g/f binding identities to the actual level-1 copying call
and retaining its complete produced polar-pair set through transformed-child
reuse. Prove the occurrence/reuse invariant before broader implementation.
This recommends no particular representation or permission expansion.

All-source Value identity, scope/wrapper ownership, full replay/cache-event
classification, generalization, abnormal paths, effect equality, equality
preservation, soundness, required principality, normal progress, termination,
complete Call and F5 cutover remain OPEN. This note reduces the missing
construction premise; it does not close the parent theorem or prove semantic
impossibility.

## Dependency snapshot and commit packet

SHA-256 of inspected direct dependencies (no producer changes):

```text
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49  crates/yu-solver/src/candidate_source.rs
fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0  crates/yu-solver/src/candidate_extrusion.rs
79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35  crates/yu-solver/src/candidate_call.rs
cbd2e0c49a3f1fbe3c5fc78a06d469faedf4aa261525b24a0c9584e9956c2411  crates/yu-solver/src/shadow_apply.rs
aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0  crates/yu-solver/src/candidate_intrusion.rs
4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987  crates/yu-solver/src/candidate_context.rs
9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1  crates/yu-solver/src/candidate_scheme.rs
ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df  crates/yu-solver/src/candidate_effect.rs
c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94  crates/yu-solver/src/lib.rs
906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed  crates/yu-hir/src/module/local_source.rs
0063b88d17104f85182439d80360e42f8f99a5af4793eab70640a66f955ede25  notes/design/2026-10-12-intrusion-value-type-association.md
6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b  notes/design/2026-10-10-parent-copy-scc-intrusion.md
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389  notes/design/2026-10-11-yulang-inference-top-level-principles.md
f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9  /home/momota1029/rust/simple-sub-reference/shared/src/main/scala/simplesub/Typer.scala
```

- Exact leased path: `notes/progress/2026-10-12-intrusion-occurrence-retention-audit.md`.
- Baseline SHA: `e5e7b5878ced01b8cc4682492b6187c3907fd014`.
- Changed dependency hashes: none by this producer; primary revalidation required
  if concurrent work changes a listed input before integration.
- Review status: unreviewed, research-only, frozen; no self-certification.
- Checks already run: bounded source/authority reads and direct dependency hashes;
  no executable verification.
- Proposed checkpoint message: `research: trace nested Call occurrence endpoints through replay`.
- Shared-record deltas left for primary/curator: cite the scope-to-g and resolved-f
  derivation, the no-copy level-2 / copying level-1 distinction, and the missing
  certificate handoff in `tasks/current.md` and the existing theory gate; retain
  OPEN statuses. No task/index/authority/question-board file was changed.
