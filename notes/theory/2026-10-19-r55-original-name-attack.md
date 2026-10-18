# R55 original direct-Name domain and induction attack

Status: CANDIDATE adversarial source/native evidence; NO_SOURCE_FALSIFIER.
Handoff ID `R55-ORIGINAL-NAME-ATTACK`, revision 1. Sole author
`/root/r55_original_name_attack`, session `current-conversation-2026-10-19-r55`.
Requested Sol/high; observed model and effort UNKNOWN. No descendants.
Baseline `a703e158c`. Contract `original-name-core-20261019-r55`, revision 1,
SHA-256 `4c292a24c7fba19c40587fcc2cb9374fdbff3dd7059533548e4e1be1420546d1`.

## Result and application to the parent

The original forwarding-preservation §6 direct-Name mapped-admission premise
remains OPEN. This independent attack finds no original-domain history with
an exact absent mapped physical BoundKey. It identifies two necessary proof
repairs: source-instance applicability must be checked separately from a
provider's body shape, and an authentic FreshUse row table is a partial map,
not automatically a total substitution on the original registration graph.
It also supplies an authentic direct-Name callee-use source shape and an
original-domain recursive input for the remaining source-owner case. These
are static resolved-source constructions, not compiler executions or assertions
of successful complete solving, parsing, publication or runtime behavior.

Apply these findings to the unchanged parent by rejecting automatic application
of auxiliary higher-order source witnesses and requiring the exact coverage
judgment below before substituting mapped endpoints in §6. The original
shared satisfying assignment, arbitrary finite prefixes and forwarding-chain
length, repeated calls, simultaneously live receiving entries, raw resumptions
and independent foreign-continuation obligations remain unchanged. A static
use identity is not a dynamic receiving entry. Parent and Simple-sub A/B gates
remain OPEN 0→0; R50 is NOT ADOPTED. No semantic or production decision follows.

## 1. The source instance must match the original quantifiers

Forwarding-preservation §1 fixes explicitly annotated single-parameter
Computation functions with finite concrete resolved permission sets. At each
forwarding edge the whole actual argument is the resolved computation Name of
the current formal. Ordinary ground return, operation, designated consumption,
Bind, call and shallow handlers/raw continuation invocation remain in scope.
The fragment constructs no new general higher-order function/field interface.
§6's selected provider additionally has direct resolved formal-Name body.

A provider having body `t` does not make every surrounding source history an
instance. In R51, `k forward` passes a callable as the whole argument to an
unannotated outer formal k. R52/R53 use `loop forward`, again passing a callable
to the loop formal. Those displayed argument edges are not the current
computation-formal Name edges required by §1. R54 explicitly records its
annotated higher-order q discriminator as NON_APPLICABLE. Thus none of those
whole displayed source shapes is established as an original §1 instance by
the pinned artifacts. Their reviewed physical-owner, signed scheduling,
source-set, restoration and scalar facts remain reusable at independently
established matching operational premises. This finding neither withdraws
those facts nor narrows the supported language.

Conversely §1 does not imply that every source history is one isolated,
nonrecursive first use. It permits ordinary source constructors and arbitrary
finite interactions. An exclusion of later captures, nested declarations,
qualified replay or raw continuations needs its own actual source argument;
the non-applicability of the previous examples proves no such exclusion.

## 2. Authentic source entrance at an ordinary forwarding edge

An original-domain resolved source shape is:

```text
my outer (q:[io] int) = {
  my forward (t:[io] int) = t;
  forward q
}
```

Both formals are explicitly Computation with finite concrete io. The actual
argument is the whole current formal Name q, and forward's body is exactly
its own resolved formal Name t. No higher-order formal or function-valued
argument is introduced. This is an input to existing ordinary HIR/LocalSource
constructors, with resolved family/binder identities fixed.

`candidate_source.rs:869–879` registers t; `:1220–1229,1663–1666` connects
its exact Name effect to that registration. `candidate_formal_effect_equal`
(`candidate_effect.rs:1437–1445`) emits both effect directions; Lambda slot 4
(`lib.rs:11357–11444`) emits Name<=RE and Computation omits slot 3. The
original physical route is upper(t,n), upper(n,t), upper(n,r) at equal levels;
R52's admission-time owner analysis supplies the physical orientation.

The outer/q Lambda has level 1. The local forward initializer, t, n and r
have level 2; Install stores boundary 1. The final Apply and its callee Name
have level 1 (`candidate_source.rs:956–1040`). Since forward's initializer
has completed, its callee Name emits `Action::Local`, not active-initializer
`Action::Link` (`:1245–1251`). `route_candidate_local_run`
(`candidate_scheme.rs:2011–2038`) reads the real scheme root/boundary, captures
that live graph and prepares ONE FreshUse at level 1. The isolated first-use
supplier's source/history premises apply to this first local occurrence.
Its capture/restoration argument derives the three mapped physical bounds.
The Local consumer restores all captured bounds before linking its root
(`:2153–2183`). The Apply uses q's exact Name effect as demand AE
(`shadow_apply.rs:1795–1817`); actual Function dispatch supplies the ordinary
contravariant AE/covariant RE tasks (`lib.rs:12655–12683`).

This supplies an authentic original-domain use of the existing bounded
first-use result. It does not establish a new general recapture theorem.
The repeated-use variant `my a = forward q; forward q` remains in the source
fragment and puts the first Apply at level 2 and the second at level 1. Any
induction invoking first-use twice must first audit the first call's write
endpoints and prove that its fresh rows/argument effects have not aliased the
original scheme closure. The body shape and equal family spelling cannot
supply that noninterference premise.

## 3. Partial FreshUse maps require a coverage statement

`Capture::row` (`candidate_scheme.rs:755–790`) resolves each requested row to
its current representative and marks it local only above the boundary and
when generic. `Capture::expand_row` (`:1054–1059`) stops at a shared anchor.
`prepare_candidate_fresh_use` (`:1555–1615`) iterates graph.rows; its
canonical_rows memo constructs images ONLY for those captured representatives.
It does not iterate all original rows or define an image of an unvisited Name
row merely because that row once belonged to the provider's original body.

Therefore the proof cannot introduce `mu(e_n)` solely by citing the memo.
For a wholly shared middle, a legitimate original-to-use correspondence can
use the actual retained shared identity, with the actual canonical quotient
for aliases; captured fresh rows use their actual FreshUse images. The proof
must establish that these choices are consistent with the reconstructed
Function ports and the physically admitted path for the same lineage. In a
mixed cut, writing identity for an uncaptured local row does not repair an
absent bound to a newly reconstructed port. For signed extrusion, the
occurrence/sign-specific port correspondence also cannot become a global
unsigned substitution.

This is a proof-definition attack, not a source counterexample. It matters at
the precise point §6 composes argument<=mu(t)<=mu(n)<=mu(r)<=demandRE. A valid
proof may instead provide an explicit same-lineage physical route between the
actual ports and its honest intermediate identities, then state exactly how
it supplies the original mapped-bound premise. The route must include the
reverse Name<=AE direction when claiming the full R55 fixed outcome.

## 4. A recursive original-domain case and first unsupported owner judgment

Use the following distinct source input instead of the callable-argument
R53 discriminator:

```text
my outer (q:[io] int) = {
  my forward (t:[io] int) = t;
  my loop (x:[io] int) = {
    my a = forward x;
    my z = loop x;
    z
  };
  loop q
}
```

All three forwarding arguments are current computation-formal Names, and
forward remains a direct-Name provider. The approved single local self-recursion
construction is sufficient; no mutual-local recursion is used. No complete
successful solver execution is asserted. Conditional successful-prefix claims
must explicitly identify their completed drainage/restoration boundary.

The actual source-reference owners (`candidate_value_graph.rs:89–143`) give
forward->Parameter(t), a->forward, a->Parameter(x), z->loop,
z->Parameter(x), loop->z, outer->loop and outer->Parameter(q). Parameter
vertices have no source outgoing edges in this construction. Therefore the
actual recursive event `(Local(z),Local(loop))` qualifies, while an Apply
whose receiver is forward does not qualify merely by that receiver's SCC.
The recursive callee Name uses the open initializer Link. Ordinary candidate
solving can be considered at its actual scalar dispatch as in R53; scoped
authentication and R50 remain separate and unmodified.

The typed recursive demand now has an Int-valued argument Name. It has NO
positive Function provider argument port corresponding to R53's `forward`
argument. Thus R53's co-visited Function-port calculation cannot supply this
case's actual signed group. Conversely, the sink edge forward->t alone does
not prove that no qualified ancestor event can ever enter the retained effect
closure of one of forward's fresh uses. `retain_extrusion_parent`
(`candidate_intrusion.rs:308–365`) qualifies the actual retained source SET,
not an assertion that its endpoints' provider name is recursive.

The first unsupported source-owner judgment for the proposed universal
induction is consequently:

> For every parent-permitted successful owner history preceding an authentic
> direct-Name scheme capture, establish which original and previously fresh
> provider rows may be reached by the ACTUAL current structural/pending bound
> traversal and retained source set; derive their physical signed owner/path
> coverage after complete successful group settlement and replay.

At `Capture::expand_row` this judgment is consumed to conclude that stopping
at a shared owner cannot remove the route needed by the independently
reconstructed actual ports. Ordinary maximum-level owner selection proves it
at initial admission only; merge appends stored sides and takes minimum levels
(`candidate_intrusion.rs:599–703`) without relocating every historical bound.
Scalar quotient survival is insufficient. Assuming uniform port levels,
whole-provider co-visitation, replay of an uncaptured bound, source purity of
every future event set, or injectivity of representatives is circular here.

No physical missing BoundKey has been derived for this recursive input. In
particular a symbolic owner(h,Negative,z) with h shared and z freshable is only
a pressure configuration until this input's actual constructors emit it;
ordinary admission alone cannot do so in that final state (R52). Successful
replay may also install an alternate lower on the local RE (R54's lesson).
This packet stops at the exact owner judgment, rather than claiming refutation
or the exclusion of all original-domain partial histories.

## 5. Evidence request, checks and stop receipt

Mutual TODO `R55-ORIGINAL-INT-RECURSION-1`, owner Luna for assignment to the
source/extrusion lane: trace the above original-domain recursive input from
its actual `loop x` negative demand through structural versus pending visits,
actual source sets/parent indices, group settlement, canonical representatives,
first later capture boundary and ONE reconstructed provider lineage. Required
falsifier of a claimed exclusion is an actual entry into only a partial
same-provider route. Required falsifier of mapped admission is an exact absent
physical bound/alternative route AFTER successful actual restoration, between
that same instance's ports. The input may instead establish an exclusion for
this source case; that would still need application to the original universal
constructor induction. Do not substitute R53's Function argument or R54's q.

If static source construction cannot settle this, the minimal provisional
implementation TODO is an observation at actual signed Visit/Bound,
retain_extrusion_parent, settlement and Local reconstruction for this source,
with the source and physical row/BoundKey lineage frozen. Such instrumentation
needs a new primary-authorized exact code lease and falsifier. No code repair,
production change or execution is authorized by this request.

Prior work reused: original template/conditional implication; isolated first-use
supplier at its matching source; R52 physical admission owner fact; R53 ordinary
versus scoped distinction; R54 replay countercheck and explicit domain warning.
Rejected: promoting R51–R54 whole source histories into §1 instances, total
unsigned map substitution, source-event SCC from a provider's name alone,
retained/queued evidence as physical admission, and one frame action as a
foreign-continuation proof.

Checks: static source reads/searches and exact SHA-256 validation only; all
39 dependency hashes matched before work and again before these writes.
No tests, builds, runtime, probes, measurements, scratch paths, Git operations,
external/user contact or descendants. Exact two output leases only. Assigned
600-second cap; no budget expansion or carryover and no measured CPU/RSS claim.
WRITES_STOPPED after the frozen handoff; no descendant leases exist. This
producer/coauthor is ineligible to independently certify the combined R55
packet. Fresh review and integration belong to Luna.

Frozen dependency manifest (39/39 matched):

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
feb92f2ff3f2dc65059e07723adc5bef8ebf2ca9f83c979120ac484214c8e69d  tasks/agent-loop/sprints/computation-mixed-capture-20261019-r52.md
16850d4f83a65d1c4a124c520da0b1546a97c62869b0a23a3722f3f93afe6220  notes/theory/2026-10-19-r52-mixed-capture-coverage.md
3ad115cf65969c1b39b074fcc2e22631c0ab04f91eb810a4d666087a78cce2c1  tasks/agent-loop/inbox/20261019-r52-proof.md
276b692d820aa6cec3e29a2428b4e75ff34e20e546b76fc07209eed8e1ab6299  notes/progress/2026-10-19-r52-mixed-capture-source.md
f667508891d9990036c5bd33150d96f428bae0030af007cd174d28915e00773a  tasks/agent-loop/inbox/20261019-r52-implementation.md
a4bec1ffe6e5e29120e5adc726b93eac32c8c81ec6445180a2436dd6f71cc4eb  tasks/agent-loop/sprints/ordinary-mixed-capture-20261019-r53.md
527b7ac19e446f964c234cf832db8daa0046d893d73d8078c007d7277d4c20d2  notes/theory/2026-10-19-r53-ordinary-mixed-capture.md
1db746f2e54309b366635b9085e6c2f28009c252460f844fd220b3e978973847  tasks/agent-loop/inbox/20261019-r53-proof.md
6d67452a83020f8377e7a874169a7ac4e1613ffad2894206377d726b1bc630c5  notes/progress/2026-10-19-r53-ordinary-source-native.md
deb4886decbc907188101ebe1b18c58e15ae5336177c5676e7909711a4910201  tasks/agent-loop/inbox/20261019-r53-implementation.md
b39fbe7287e420c6ff902ea0fa082923f5a820a066f78f547fa49a24b9fd59bd  tasks/agent-loop/sprints/first-partial-capture-20261019-r54.md
98210c2e83ca04c195d5476bf8abc127d058c77f30549a0bd79d1e55c8a27469  notes/theory/2026-10-19-r54-first-partial-capture.md
4cf53e5a1fc4ebd30cec664176978e4a6e5dfad3242eadba1d33f181a8fd4bda  tasks/agent-loop/inbox/20261019-r54-proof.md
9d188aae4c1908f8158063e4ddb69537ada2bb785f586ce2d51ed973444abc49  notes/progress/2026-10-19-r54-first-partial-source.md
048dc4e47efb81b908e104fe264e39e4b02a08bd295a2ace8b4d968534cfa4da  tasks/agent-loop/inbox/20261019-r54-implementation.md
```
