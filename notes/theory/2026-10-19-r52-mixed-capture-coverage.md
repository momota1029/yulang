# R52 mixed capture: physical owner invariant and first source obstruction

Status: CANDIDATE source/native owner analysis; NO_SOURCE_WITNESS for a bad cut.
Author: `/root/r52_mixed_capture_proof`, sole author; no descendants.
Sprint: `computation-mixed-capture-20261019-r52`, revision 4, SHA-256
`feb92f2ff3f2dc65059e07723adc5bef8ebf2ca9f83c979120ac484214c8e69d`.
Baseline: `42b5dccaa4ec1768b474848acb4c7f53e3d77e7b`.
Exact outputs: this file and `tasks/agent-loop/inbox/20261019-r52-proof.md`.

## Parent application and result

The original forwarding-preservation §§6–7 mapped-admission obligation remains
universal over its original authentic captures, uses and compared providers.
The full inference/evaluator theorem and Simple-sub A/B parents remain OPEN
0→0. The original source theorem keeps one joint satisfying assignment,
arbitrary finite prefixes, repeated calls, independently live receivers and
raw/foreign continuations. None is discharged by one static frame or SCC.

This pass supplies a narrower physical-owner fact that rules out a purported
bad cut *at ordinary row-row admission*, and a source-qualified recursive
construction showing why qualified intrusion is not itself a bad-cut witness.
It does not establish the general post-merge invariant or a counterexample.
The first unproved step is preservation of owner coverage when a prior
Function-bound traversal reaches a tracked effect row with a different sign
or through a different occurrence from the original provider's structural
port traversal. The entry into that traversal must be supplied by actual
source/native construction, not by a manually selected effect-row root.

Applied to the parent: the initial ordinary owner choice cannot justify the
abstract older-owner/newer-item fixture. A qualifying recursive application
also cannot be cited without its complete signed closure. The general
mapped-admission proof must next handle the first source-generated traversal
that changes only part of an inherited AE→Name→RE route, or prove that no such
entry is generated. This remains an exact source-construction obligation,
not a new conditional parent theorem.

## 1. Ordinary admission has a useful level-indexed owner fact

Write a physical scalar bound as `B(owner,side,item)`, with Positive meaning
`item<=owner` and Negative meaning `owner<=item`. For a nonreflexive ordinary
effect-row task `a<=b`, `candidate_apply_effect`
(`candidate_extrusion.rs:944–969`) selects

```text
level(b)<=level(a): B(a,Negative,b)
level(a)< level(b): B(b,Positive,a).
```

The corresponding value-row rule is at `:912–935`. Thus the selected owner
has the maximum endpoint level at THIS admission. In particular, if exactly
one endpoint is above capture boundary L, that local endpoint owns the bound.
Capture from a Function containing both endpoints interns both ports, and
expansion of the local endpoint can capture the edge despite the other port
being an older anchor. This single-edge statement needs that the local owner
is actually reached; it is not a global reachability theorem for arbitrary
intermediate rows. Nongeneric metadata can also stop expansion and is not
decided by this level comparison.

The emission is physical: `candidate_insert_bound_with_evidence`
(`:499–670`) appends ONLY the selected side and reads back that physical slot.
It does not silently add a reverse-side slot. Capture incidence at that owner
is specifically effect-allowance incidence (`candidate_effect.rs:663–675`),
not a second generic row-row adjacency. Hence `h<=z` stored solely as an
upper on h with `level(h)<=L<level(z)` cannot be supplied by this ordinary
admission rule in that state. It needs an earlier history changing the owner
or levels. This rules out an unsupported fixture assumption; it does not
prove that later histories exclude the configuration.

For a fresh direct-Name Computation formal, original registration t, body
Name n and Lambda RE r start at the same initializer level. Source registration
and Name actions are `candidate_source.rs:869–879,1220–1229,1663–1666`;
`candidate_formal_effect_equal` at `candidate_effect.rs:1437–1445` emits both
directions. Slot 4 supplies n<=r; Computation omits slot 3. Initially the
effect route has physical uppers t→n, n→t and n→r. Concrete S gives no cap
on t, and the Function argument is Int−, not a negative copy of result row v.
These are the reviewed R51/signed-copy premises, checked at current owners.

## 2. Why the induction over later history stops

An extrusion row visit creates a parent/copy record and its opposite-side
source link, then copies only the selected bound side
(`candidate_extrusion.rs:78–167,330–340`). A successful merge appends both
stored sides, takes minimum level and OR of nongeneric bits, redirects the
copy representative and canonicalizes evidence
(`candidate_intrusion.rs:599–703`). This preserves the quotient inequality;
it does not reapply the ordinary maximum-level owner selection to every
preexisting third-owner slot.

The sign matters. A negative visit of h copies its upper closure, whereas
a positive visit copies its lower closure. For a simple h<=z route already
selected during a negative visit, with both rows above target T, the operation
can create h−<=z− together with z−<=z (the latter on z's lower side).
If h− later merges into h, while z remains generic, capture can have an
alternative route h<=z−<=fresh(z), provided the actual root reaches z and
those physical owners. This uses selected, occurrence-indexed copies and
their actual source links; it is not a total unsigned substitution.

A positive-only lowering of h has no such upper-closure conclusion from the
row visitor itself. Conversely a positive-only lowering at another position
can be safe if an actual alternate route is present. Therefore the induction
cannot use either “merge keeps inequalities” or “a row has an extrusion
parent” as its preservation step. It needs the source-generated entry sign,
the full operation's Function children and selected closures, surviving
source links and subsequent merge groups for the SAME provider lineage.

`retain_extrusion_parent` records actual source sets and occurrence; only
qualifying source events enqueue equality (`candidate_intrusion.rs:308–365`).
The SCC criterion does not assert that every bound reachable from a parent
is another parent of that operation, nor that an independently reached
provider's ports were all visited structurally. That missing structural
incidence is the first unavailable owner judgment in this attempted induction.
It is not established by the abstract positive-only pressure configuration.

## 3. An approved recursive source construction, and its actual limits

The following is a static resolved-source construction candidate, not a parser,
solver or runtime execution. S is a resolved concrete finite set, shown as io.

```text
my outer q = {
  my loop x = {
    my forward (t:[io] int) = t;
    my used = loop forward;
    used
  };
  loop
}
```

This uses the approved single local self-recursive parameterized binding.
There is no mutual-local recursion. The recursive Name inside used links
the active loop initializer's open monomorphic root; it is not a LocalScheme
FreshUse (`candidate_source.rs:1245–1251,1669–1673`). Later installed uses
retain their normal live capture; no freeze or early publication is assumed.

Exact original source-reference edges are:

```text
Local(loop) -> Local(used)       final Name in loop body
Local(used) -> Local(loop)       recursive callee Name
Local(used) -> Local(forward)    argument Name
Local(forward) -> Parameter(t)  direct body Name
Module(outer) -> Local(loop)     final Name in outer body.
```

Nested initializers switch owners to their own Local Values
(`candidate_value_graph.rs:89–143`); Lambda bodies retain their current owner.
Thus the actual `loop forward` event is `(Local(used),Local(loop))`, and both
are in the same SCC by the first two edges (`:181–196,245–247`). Neither t
nor a type-row SCC is the qualification witness. Helper fragment edges retain
these Name incidences; they do not fabricate a receiver.

Levels follow `candidate_source.rs:956–1040`: outer/q start at 1; loop/x and
its body are at 2; forward/t and used's Apply/argument Name are at 3. Forward
is installed at boundary 2; loop at boundary 1. The actual local argument
Name freshly reconstructs forward at use level 3. Let its map be mu, and
write t,n,r,v for mu's rows of the original registration/Name/RE/result.
This first local use is within the isolated first-use supplier's premises;
it does not identify mu with the original graph or with a later use.

At the source Apply, its negative demand D is constrained against the
level-2 open loop value root. Conditional on that actual task reaching the
ordinary scalar dispatch and successful completion, the owner calls negative
Function extrusion to target 2 (`lib.rs:12582–12593`). This is a native
dispatch implication, not a claim that all subsequent recursive solving
terminates or that scoped checks reach this dispatch.

The SAME operation visits the positive provider through its positive argument
row. The structural ports are `(Int−,t−,r+,v+)`, and selected closure supplies

```text
t−<=n−<=r−<=r+,
t−<=t, n−<=n, r−<=r, r<=r+.
```

All copies shown have target level 2. The structural-before-pending schedule
is exactly the repaired signed-copy supplier: r<=r+ exists before the
negative r snapshot. Parent records include t−, n−, r− and r+, with their
separate signs, and v+; Int− supplies no parent. The qualification above
applies to records actually carrying that checking source. When those
records are settled successfully, it does not merge r+ alone: t/n/r and the
selected polar copies all acquire level at most 2 through their own parents.
It is invalid to omit those other parents to obtain an artificial mixed cut.

This construction therefore establishes lexical/source qualification and the
conditional native signed-group analysis, not a bad-cut source witness.
There is a concrete earlier obstruction on the current scoped consumer path.
Apply records this recursive Local Name as `local_callee`
(`candidate_source.rs:1292–1317`), although its active-initializer Name was
emitted as `Action::Link`. `candidate_call::authenticate_scoped_apply`
(`candidate_call.rs:689–738`) requires that SAME Name occurrence to have a
retained `LocalFreshRoute` and an installed LocalScheme. Neither is produced
by the recursive Link, and installation follows initializer actions. In
`shadow_apply::admit_candidate_fact` (`shadow_apply.rs:1762–1776`) this
authentication precedes demand lowering when scoped_experiment is enabled.
Consequently the recursive candidate is NOT an admitted scoped mixed-cut
history. Source Value-SCC qualification does not bypass this owner. This is
the first exact native consumer obstruction for this construction. The
unadopted R50 route supplies no authority to repair or bypass it.

Completion of the entire recursive native route, every contextual disposition
and actual later reconstructed-port comparison are not established. In
particular it is not a theorem that this candidate executes or supplies a
new dynamic receiving entry. No parent conclusion relies on assuming that it
does. R51's independently reviewed nonrecursive two-use theorem remains
reusable only in its own fixed history.

## 4. Exact obstruction and next discriminating evidence

NO_SOURCE_WITNESS: this pass has no approved-source history producing a bad
mixed cut. It also has no induction excluding all such histories. The exact
missing case is an actual structurally generated extrusion whose selected
closure first reaches one representative of an inherited same-provider
AE→Name→RE route, with sign/target causing partial owner lowering, without
already possessing enough actual alternate route edges to the other port.
The unknown is source reachability of that entrance and its complete group,
not correctness of a manually invoked `candidate_extrude(Effect(h),+,T)`.

Owners, in dependency order:

1. `candidate_source::Action::{Link,Local}` and Apply lowering retain the
   original recursive/local occurrence and receiver. `lib.rs` typed Function
   comparison/rewrite dispatch chooses actual structural extrusion roots.
2. `candidate_extrude::Work::{Visit,Function,Bound}` determines the first
   selected entry sign and actual co-visited ports/closure.
3. `retain_extrusion_parent`, `finish_candidate_extrusion` and
   `settle_candidate_intrusion` determine actual source-qualified parent
   groups, merge order and representative levels.
4. `Capture::{row,expand_row}` at `candidate_scheme.rs:755–790,1054–1132`
   stops at nonlocal/nongeneric anchors; `prepare_candidate_fresh_use`
   (`:1594–1608`) independently chooses actual row images. Function children
   and captured bounds use the same reconstruction table (`:1715–1755,
   1860–1906`), but cannot restore an uncaptured edge by table consistency.

TODO R52-FIRST-PARTIAL-OWNER-1, for Luna's next bounded source-construction
assignment: supply one original source history and the first such entry,
including original registration/body/argument occurrence, actual Function
root, sign/target, Parent indices/source event, physical BoundKeys/owner levels,
capture boundary and both actual reconstructed Function ports. Alternatively
prove a source-directed exclusion at these entry owners. Falsifier of the
candidate exclusion: an authentic first partial-lowering entry outside the
co-visited route closure. Falsifier of mapped admission: the same actual
ports lack their admitted route after capture/restoration; an unrelated
provider, occurrence or executable fiber cannot repair it.

Mutual TODO R52-RECURSIVE-AUTH-1: Luna owns disposition of the earlier scoped
authentication seam. Preserve the approved monomorphic recursive Link; obtain
the governing consumer contract and an authorized source/native route for
that SAME original callee occurrence before using this example as native
evidence. Exact falsifier of the current obstruction: an existing pre-demand
producer of a genuine retained route and installed scheme for that recursive
Link occurrence, without freshening the monomorphic recursive root. A policy
decision to adopt R50 or a new authentication mechanism is outside R52.

If static construction cannot settle that entry, the smallest proposed
provisional implementation TODO is an observation of those operands at
extrusion entry/parent retention and recapture, exercised from original
source. No production repair, speculative edge or capture-rule change is
justified. Code, tests, execution, new inputs and leases need Luna's revised
authorization; none is authorized or performed by this TODO.

Physical scalar coverage is also weaker than executable evidence.
`candidate_transfer_bound_origins` (`candidate_effect.rs:677–715`) transports
existing fibers separately and preserves MissingOriginAssociation on metadata
without a fiber. Equality canonicalization of third-owner fibers
(`candidate_context.rs:4005–4021`) is not fresh-port admission. A future scalar
Function comparison supplies demandAE<=actual provider AE and actual provider
RE<=demandRE (`lib.rs:12655–12683`); Apply connects invocation effect to output.
The original implication can be used only after the SAME instance's route is
actually admitted. Dynamic receipt/Force, complete Call, general hygiene,
soundness, principality, replay and foreign-continuation coverage remain OPEN.

## 5. Reuse, checks and stop receipt

Reused: R51 initial template/first-use provenance and repaired signed-copy
schedule within their actual premises; scalar quotient survival only as a
quotient fact. Rejected: arbitrary older-owner fixture as source witness;
selected-side copying as unsigned graph substitution; SCC equality as a
whole-interface theorem; recursion qualification with omitted co-parents;
origin metadata as executable fiber. The adjacent first-Call generalization
note concerns a complete typed challenge/projection obstruction, not this
native capture constructor; its theorem does not transfer to this cut.

All 24 current.json dependency file hashes and revision-4 contract were
revalidated before writes and at freeze. Revision 2's historical current-state
pin was not re-readable without forbidden Git; Luna corrected the contract
before writing. Revision 3 was superseded by revision 4's explicit local
self-recursion authority. No output bytes were written under the superseded
revisions. One hash-script command used unavailable `python`; `python3`
performed read-only hashing. No compiler tests, builds, probes, executions,
runtime measurements, scratch files, Git operations or descendants.

Requested model/effort: Sol/high; observed model/effort UNKNOWN/UNKNOWN.
900 seconds charged at launch, no expansion; independently measured active
duration and CPU/RSS UNKNOWN. Stop condition reached: exact first source/native
entry obstruction after ordinary-owner and recursive-source methods. Fresh
independent review and all promotion belong to Luna. No further producer
stage is claimed while waiting. WRITES_STOPPED / NO_DESCENDANTS upon frozen
hash submission. All new paths are exactly the two exclusive outputs above.

Direct frozen dependency manifest follows (SHA-256 of consumed file bytes).

```text
09511a51539ca2a14cd7a40d2b9a5da00f72417d1ec5f97a4ba6bfd6ec20c2e1  notes/theory/2026-10-15-computation-freshuse-admission-bridge.md
477ada20e61ce5355601af138b37016ba1a8036e65f4f39627beda2abe062adf  notes/theory/2026-10-15-computation-signed-copy-source-bridge.md
d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79  notes/theory/2026-10-15-computation-forwarding-preservation.md
7766aff08cedde1ebc796b8927cd1d44f459df72a632e0c0d35d4bfcd28d335e  notes/theory/2026-10-15-computation-formal-permission-construction.md
baeebe5872dcf313cffa402667494a9ea9d5395bbe18025e1c14f0c1d7526397  notes/progress/2026-10-15-computation-source-plans.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
c544ed3c7b83686a740aa43b1db92d901de31a3b197f81f90a4c9dbdae561134  notes/design/2026-10-15-callback-identity-forwarding.md
a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18  notes/design/2026-10-10-annotation-effect-hygiene-integration.md
66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c  crates/yu-solver/src/candidate_source.rs
8738c1b1699228b1a4dfd30af7e03d0afb100ca6124d23037c645246d888dc50  crates/yu-solver/src/candidate_value_graph.rs
ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5  crates/yu-hir/src/module/local_source.rs
fc0d948d884a406746066f3df8db257d5c6686505166b330bef839a9b9e2f35d  crates/yu-solver/src/candidate_extrusion.rs
8a1f531be9fb5e5f160bf4f75c6eb98bbc35ce0a30acaf06424c531840504ba4  crates/yu-solver/src/candidate_intrusion.rs
d4ff8a9e98eb667a5eb85aff9c0feec1f0227e86257bb56892493ac1d04a9278  crates/yu-solver/src/candidate_scheme.rs
42f89dcf5fa6d7095db1e220c89308a2a35f4e74b05c3e8821d4fb2e3e32b0ca  crates/yu-solver/src/candidate_context.rs
6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0  crates/yu-solver/src/candidate_effect.rs
5bbcf27d51906814ba38b2cca2066807d285d0b1817f0ea6e04d70c4a5c8a5cb  crates/yu-solver/src/shadow_apply.rs
2300400e87d0a487225f207d414ac71fa4f21c6f80279fea4f793e43c7809aee  crates/yu-solver/src/lib.rs
e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479  crates/yu-solver/src/candidate_call.rs
f133c402f47b90f37bca92d2470cd7007fd320c580efba9ae0919a7f38a027b8  notes/theory/2026-10-19-computation-formal-copy-bridge.md
8180aa417995c6d069a5a1b24a0ab405ad0b10bb056ac42c74d402a0ca0874ce  tasks/agent-loop/inbox/20261019-computation-formal-copy-proof.md
b58e19d3a921dcf9ba99627c8584f24f8d7ab779a336f21e21f0dcd63d7a0807  tasks/agent-loop/sprints/computation-formal-copy-bridge-20261019-r51.md
a37cd471c26c9936118282afe2eec295380a02b5197159d787f7d3ef75a50b47  notes/theory/2026-10-16-first-call-local-result-view-generalization.md
38d42183fdc4f2c0136112d8b305816241d8f449367b473e4de3a5135dc49895  notes/design/2026-10-10-local-self-recursive-binding.md
```
