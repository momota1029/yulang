# R54: a source-generated shared-anchor cut survives replay and FreshUse

Status: CANDIDATE bounded source/native derivation; fresh independent review
pending. Parent OPEN 0→0. No parent counterexample or exclusion theorem.
Author `/root/r54_first_partial_proof`; primary `/root` contributed the
annotated-q discriminator and adjudicated its scope. No descendants.
Baseline `96b24b22bd63650964692ef44845c0bc27c376a0`.
Contract `tasks/agent-loop/sprints/first-partial-capture-20261019-r54.md`,
revision 1, SHA-256
`b39fbe7287e420c6ff902ea0fa082923f5a820a066f78f547fa49a24b9fd59bd`.
Exclusive outputs: this note and `tasks/agent-loop/inbox/20261019-r54-proof.md`.

## 1. Result and application to the unchanged parent

The actual constructor trace below reaches a first use whose same-provider
AE-to-RE route crosses several older shared anchors. R51–R53's private
all-local route arguments do not justify this capture. Its path nevertheless
survives: normal Apply and Lambda replay creates a positive lower on the
actual provider RE, and ONE authentic FreshUse restores that edge. Stopping
capture at an older row does not erase the live shared middle of this path.
The initial suspected missing edge is rejected after inspecting that replay.

This is a compiler/source discriminator under existing formal-annotation,
ordinary Apply, live local capture and freshening constructors. It is outside
the original forwarding-preservation §1 positive source fragment: it adds an
annotated higher-order formal q and forwards q rather than the current
computation formal. Its forward body is Apply, not the direct-Name body used
by the native template lemma and the R51–R53 suppliers. Accordingly its
parent-instance application is NON_APPLICABLE. It neither refutes nor closes
that original native theorem. No new source-domain or semantic authority is
inferred from the investigation.

The useful parent-facing result is methodological and source-specific: the
proposed shared-anchor failure mechanism must account for successful native
replay before claiming that a required RE edge is absent. This removes this
concrete purported witness. The parent still needs the first actual entrance
for one of ITS original provider lineages, or an exhaustive source-generation
argument excluding that entrance. Neither a successful discriminator outside
that fragment nor its scope caveat supplies such exclusion. Original shared
satisfying assignment, finite-prefix, repeated-call, independent receiving
entry and F1/FK1/foreign-continuation quantifiers remain intact. R50 stays
NOT ADOPTED; soundness, principality, full contextual/dynamic correspondence,
complete Call and production authority remain OPEN.

## 2. Concrete source constructors and successful-prefix boundary

Fix a resolved concrete finite S, shown as io, and one original symbolic
effect-variable spelling e in q's annotation scope. Consider this ordinary
named-header source shape:

```text
my outer (q: ['e] int -> ['e] int) = {
  my forward (t:[io] int) = q t;
  forward
}
```

The mathematical input is the corresponding resolved source carrier, with
q/t/forward retaining distinct original binders and source occurrences. This
is a static source-to-constructor derivation, not an executed parse, fabricated
test graph, observation of successful solve, or assertion of runtime behavior.
Textual parser execution, complete-session success and all diagnostic paths
remain unobserved. The result quantifies over finite successful ordinary
constructor prefixes through the displayed final Local route; successful
fallible construction/drainage/restoration is explicit, not smuggled in as
full solver completion.

The production HIR path is `local_source.rs:595–627` for the outer named
parameter, `:1267–1337,1351–1357` for the local named header/block schedule,
`:651–703` for t's lexical binding/publication, and `:876–937` for ordinary
Apply. The original q Name resolves to Parameter(q); the argument Name to
Parameter(t); the final Name to the installed Local(forward). No unresolved
Name, sibling forward reference, zero-header lambda, mutual group or recursive
Link is needed. Annotation parsing is delegated by this carrier to its existing
source-annotation owner (`:604–608,1313–1321`); this pass does not prove a new
parser theorem or inspect an unpinned dependency to extend its grammar.

Candidate preflight's actual rules accept the resolved formal shape:
`candidate_source.rs:473–477,509–521` permits a singleton symbolic row at both
Function children and concrete finite S at t's outer effect row. Existing
formal construction uses the two q positions in ONE AnnotationScope:
`candidate_effect.rs:1272–1289,1355–1382,1387–1434` allocates the same row
z for repeated (scope,e), so q has actual positive Function
`Q=(Int−,z−,z+,Int+)`. This is a constructor judgment, not equal spelling
used to identify unrelated providers. q is a Value formal; t is Computation.
Concrete io grants permission and does not add io inflow or cap t.

`candidate_source.rs:956–1040,1090–1125,1512–1545` places q and z at 1;
forward's original t, body Names, Apply and Lambda at 2; local boundary at 1;
final Local use at 1. All relevant nongeneric bits start false and no inspected
constructor changes them. Ordinary `solve` selects false,false
(`shadow_apply.rs:270–281`). Scoped authentication is guarded by
scoped_experiment (`:1763–1776`), so no R50 route is involved.

## 3. Actual signed entrance and complete parent group

Use allocation-qualified names, not observed numeric ordinals. Let t be
forward's original registration AE, n its actual argument-Name effect, C its
fresh q-call invocation RE, O its Apply output effect, and r its later Lambda
RE. They start at 2. Let v be t's Int value row, U the Apply result row,
f the pure q-Name evaluation effect. All original source identities stay fixed.

FormalNameEffect admits/constrains t<=n and n<=t before Apply
(`candidate_source.rs:1220–1229,1663–1666`;
`candidate_effect.rs:1437–1445`). Both physical slots are negative uppers.
Apply retains its real native demand and checks source endpoints before typed
admission (`shadow_apply.rs:1780–1887`):

```text
D = Function−(v+, n+, C−, U−), constrained q<=D.
```

Here superscripts on the ORIGINAL D children indicate polarized endpoints;
the operation-local copies below are named a, b, c, d to avoid confusing those
endpoints with their new rows. q's row is at 1. Actual scalar dispatch therefore
calls `candidate_extrude(D,Negative,1)` (`lib.rs:12558–12598`). It does not
visit a hypothetical standalone Effect root.

The operation's structural row parents, with distinct signed keys, are:

| Parent row | Sign | Copy | Actual source link / BoundKey |
| --- | --- | --- | --- |
| v | + | a at 1 | v<=a / (v,−,a) |
| n | + | b at 1 | n<=b / (n,−,b) |
| C | − | c at 1 | c<=C / (C,+,c) |
| U | − | d at 1 | d<=U / (U,+,d) |

`candidate_extrusion.rs:78,93–167,229–258` memoizes these four operation-local
keys, snapshots selected bounds BEFORE source-link insertion, inserts the source
links, completes structural work, and only then runs pending selected bounds.
v's positive closure contains Int+; n's positive closure has no row lower;
C/U's negative closures are empty at their snapshots. Thus there is no omitted
t/r/n-negative parent hiding in this operation. r does not exist yet. Positive
Int and the atomic q interface add no further row parents. The rewritten
negative demand is `D'=(a+,b+,c−,d−)`.

The authentic checking event is h=(Local(forward),Parameter(q)). The Value
graph contains forward→q and forward→t, and outer→forward from the final
Name, but no outgoing q incidence. Hence h does NOT qualify
(`candidate_value_graph.rs:89–143,181–196,245–247`). Every actual retained
parent has this operation/source set; none is queued as a qualified equality
(`candidate_intrusion.rs:308–386`). Settlement changes no representative or
level here. No co-parent or merge is omitted to manufacture a mixed cut.

Comparing Q with D' admits b<=z and z<=c through the actual AE/RE port tasks
(`lib.rs:12655–12683`). These rows are at 1, so physical BoundKeys are
(b,−,z) and (z,−,c). Native evidence/context is ordinary identity; no scoped
deferred demand or fabricated executable fiber is required.

## 4. The replay that defeats the false missing-edge argument

Apply next admits its real invocation-to-output edge C<=O at slot 2
(`shadow_apply.rs:1906–1923`); Lambda later admits O<=r at slot 4
(`lib.rs:11357–11444`). Computation omits slot 3. At equal level 2,
C<=O is stored as (C,−,O), and O<=r as (O,−,r).

The structural source link (C,+,c) was already installed while forming D'.
`candidate_apply_effect` inserts each new edge then calls
`candidate_replay_bound` (`candidate_extrusion.rs:944–967`). Its actual
opposite-side meet at C creates c<=O; because c is at 1 and O at 2 this is
stored as (O,+,c). Later the O upper meets that lower and creates c<=r,
stored as (r,+,c). The pending replay owner is
`candidate_extrusion.rs:867–908`, not selected bound copying inside extrusion.
Successful owned drainage completes these work items before its action
returns; the driver continues through settlement and all queued work
(`lib.rs:12369–12398`). A queued item alone would not justify this conclusion.
No general transitive closure of arbitrary constraints is assumed: these are
two specific physical lower/upper meets at their actual owners.

The generated same-provider route is now

```text
t2 <= n2 <= b1 <= z1 <= c1 <= r2.
```

The middle b→z→c remains physically live at level 1. The original longer
c<=C<=O<=r route also remains, but replay has supplied the shorter actual
BoundKey (r,+,c) needed for capture. This is why inspecting r before the
successful Lambda drain, or looking only for the original O<=r slot on r,
gives a false missing-edge claim. That earlier suspicion is explicitly
retracted. Mixed generic/shared eligibility was never a counterexample.

## 5. One actual capture and FreshUse reconstruct both ends

Forward's Lambda Function is `P=(Int−,t−,r+,U+)`. Its local initializer root
and all actions finish before Install publishes that live root with boundary1
(`candidate_source.rs:1097–1125`; `candidate_scheme.rs:1965–1985`). No first
use occurs earlier. Linking P to its own level-2 root creates no nontrivial
additional copy. The final Local action reads this installed scheme and runs
`capture_candidate_graph_owned` followed by ONE
`prepare_candidate_fresh_use` (`candidate_scheme.rs:2011–2038`).

The actual provider fields independently intern t and r. Capture marks t/n/r
local since 2>1 and nongeneric=false; b/c/z are shared at 1. From t's negative
upper it captures t<=n; from n it captures n<=t and n<=b. From r's POSITIVE
lower it captures c<=r. Capture stops expansion at b/c, preserving their live
session identities (`:755–790,945–1000,1054–1132`). It need not visit the
intermediate z, C or O. Pure q-Name effect f is not a route alternative.
The original result U's Int/value bounds are not an invented effect adjacency.

Let mu be this actual Local FreshUse. Its one canonical_rows table maps the
captured local source rows to fresh use-level-1 rows t',n',r',U', while
mu(b)=b and mu(c)=c (`:1555–1608`). The Function fields and captured bounds
use the same table (`:1715–1755,1860–1906`). Physical restoration inserts

```text
t'<=n', n'<=t', n'<=b, c<=r'.
```

before completing the Local route (`candidate_extrusion.rs:763–789`;
`candidate_scheme.rs:2153–2183`). The unchanged LIVE shared slots b<=z and
z<=c supply the middle, so actual reconstructed provider ports satisfy

```text
AE(Pmu)=t' <= n' <= b <= z <= c <= r'=RE(Pmu).
```

This is a piecewise live/captured route for ONE original formal/provider/use.
mu is defined on the captured table; it is not falsely extended into a global
unsigned substitution on omitted C/O/z. No other provider's RE, independent
witness or shared-variable spelling is substituted for this provider's port.
Evidence import retains snapshots; ordinary scoped flow is default
(`candidate_context.rs:3246–3310,4051–4068`), so the latent-demand expansion
in capture (`candidate_scheme.rs:1259–1292`) supplies no assumed extra route.

## 6. Constructor-history induction boundary and exact remaining judgment

For THIS prefix, original formal generation gives t↔n; the actual annotated
callee gives z; native structural extrusion creates all four signed parents;
nonqualification preserves their separate representatives; ordinary port tasks
give b→z→c; Apply/Lambda replay gives c→r; capture/FreshUse then gives the
shown route. Each induction stage uses the previous constructed physical slots,
not an assumed mapped route. No failed transaction or same-session retry is
inserted into this successful history. Existing source-session discard and
route rollback barriers remain requirements, not newly proved global cases.

The all-parent-domain induction is still incomplete. Its first unsupported
owner judgment is: at an authentic structural Function entrance for a parent
DIRECT-NAME provider, can an inherited internal row be first reached with a
sign/target that lowers or shares its physical owner while neither its
same-provider port closure nor ordinary replay supplies an anchor-to-actual-RE
slot before the next real capture? Required evidence is the generating
`candidate_source::Action::{Link,Local,Candidate}`, actual Function task in
`lib::dispatch_live_item`, full `candidate_extrude::Work::{Visit,Function,Bound}`
closure, qualified group/source sets, successful quotient or rollback,
`Capture::{row,expand_row}` boundary, and ONE real FreshUse. The specific missing
consumer judgment would be absence of every actual stored/replayed crossing
slot into the captured RE; this discriminator shows why that absence cannot
be inferred merely from selected-side copying or a stopped shared anchor.

R51 applies to its two isolated local uses; R52's admission-time maximum-level
owner fact applies to our scalar insertions, not as a post-merge invariant;
R53 applies only to its actual qualified whole group. None supplies general
constructor-case completeness here. The earlier `forward=loop t` candidate
uses an approved nested-helper active-root seam, but its changed body/returned
callable likewise does not establish a parent direct-Name instance and is not
used as a counterexample. The original q annotation with omitted AE and only
RE=e also fails to supply a same-provider AE→RE route: omitted AE is a separate
fresh row. Repeated e at both positions is essential to THIS discriminator.

Mutual TODO R54-PARENT-FIRST-ENTRANCE-1 (Luna disposition): keep the original
parent OPEN; assign a bounded original-domain constructor-completeness or
source-entrance obligation at the owners above, with all replay alternatives.
Inputs: parent §§1,6–7, frozen R51–R53, and this rejected bad-cut method.
Required output: actual original-domain source/native entrance plus full signed
history and first missing reconstructed BoundKey, or exhaustive generation-case
preservation. Falsifier: one actual same-provider captured AE/RE lacking every
admitted route after successful relevant drainage. Mixed levels, an arbitrary
effect-root call, a higher-order discriminator outside the fragment, or origin
metadata alone is insufficient. No code slice, semantics change, probe or
additional dependency is authorized by this TODO.

## 7. Checks, resources and frozen writer receipt

Contract revision 1 and all 34 manifest file hashes matched before writes and
again immediately before freeze. Direct dependencies are exactly the 34-entry
frozen manifest at the contract SHA above; no source dependency was added.
Checks: static production source/rule/authority reads and SHA-256 comparisons.
No tests, builds, compiler/parser/runtime/probe executions, measurements,
Git, external/user contact, scratch paths, production edits or descendants.
Requested prover/Sol/high; observed effective model/effort UNKNOWN/UNKNOWN.
900 seconds charged at launch, no expansion; independently observed active
duration/CPU/RSS UNKNOWN. Stop condition: actual mixed shared-anchor prefix
with derived survival, explicit non-applicable parent instance and exact
remaining original-domain judgment. Fresh independent review and integration
belong to Luna. Only the two exclusive paths were written.
WRITES_STOPPED / NO_DESCENDANTS on frozen hash submission.
