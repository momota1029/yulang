# R56: original-domain Name source and its actual next captures

Status: candidate bounded source/native exclusion; independent review pending.
Author `/root/r53_ordinary_mixed_capture_proof`, session
`current-conversation-2026-10-19-r56`; no coauthors or descendants.
Contract `original-name-source-trace-20261019-r56`, revision 1, SHA-256
`052492309a379f3eef24078b9090f8e7081dceaf2e4c7af37ff90c75ffa013cd`.
Contract research baseline `90f40f4b1cdb2654536d1f78c32feea3980f2b2c`;
parent-reported launch checkpoint `4ce857353`, not independently Git-verified.
Exclusive outputs: this artifact and `tasks/agent-loop/inbox/20261019-r56-proof.md`.

## 1. Actual result and its application to R55

For this exact source, under successful ordinary constructor prefixes through
the specified captures, the qualified recursive extrusion does not enter or
alias the ORIGINAL forward template, or carry a forward Function through its
argument. There is one static forward Local/FreshUse before that event and
no later syntactic forward use. The first subsequent capture is of z; the
next is of loop. Neither is a recapture of forward. Thus this input does not
instantiate R55's required original-provider exposure between successive
captures of that SAME provider. This is a bounded exclusion of this candidate
entrance, not the universal noninterference invariant J.

“Successful prefix” conditions successful completion of the existing fallible
source actions, scalar drains and restorations. It is a constructor-derivation
condition, not an observed solve, successful typing of the whole session,
termination, parser/preflight run, invocation or runtime receipt. No source
counterexample or missing mapped BoundKey is claimed. The result does not
depend on a guessed numeric event/row/parent ID or on enumerating runtime state.

Applied to R55's OPEN premise: this proposed original-domain source cannot
supply the hoped-for alias/exposure witness; the selected qualified group and
next partial maps are now classified instead of left symbolic. R55's remaining
general source-exposure/recapture obligation stays OPEN 0→0. There is no
renewed universal induction, changed domain, R50 adoption or production gate.

## 2. Frozen source and membership

```text
act io:
    our tick: int -> int

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

There is one original source act identity io, with monomorphic ground
signature tick:Int→Int. The declaration is not an operation invocation.
Each of q,t,x has an explicit outer Computation annotation, with the same
finite concrete permission set {io} and no symbolic tail. Every Apply passes
the WHOLE Name of its CURRENT formal: x at forward x, x at loop x, and q at
loop q. Forward's body is exactly its original resolved formal Name t.
This is within forwarding-preservation §1's constructor fragment and its
§6 direct-Name-provider shape for forward. Loop's block body is not itself
that §6 direct-Name body. This establishes constructor-domain applicability,
not the parent's separate base typing or typed-interaction hypotheses.

The signature/declaration form appears in the pinned playground README
lines 125–136; no tool was invoked. The source annotation/parameter carriers
are formed by `yu-hir/src/module/local_source.rs:1260–1339`. The single local
self-recursion decision makes loop visible with one open monomorphic root;
it adds no mutual or polymorphic recursion. Concrete Computation permission
does not cap incoming E (`candidate_effect.rs:1449–1461`). No new higher-order
function argument is introduced, unlike the earlier callable-argument inputs.

## 3. Source identity, levels, events and schedule

Names below denote immutable allocation/source identities, not mutable forest
representatives. Distinguish forward's original rows F0,t0,n0,r0,v0 at level 2
from its first-use rows F1,t1,n1,r1,v1, freshly allocated at level 3. X is
loop's original parameter VALUE row at 2; ex is its registered EFFECT row at 2.
The original formal q/value/entry are at 1. Loop root L and body rows are at 2.
Names and Apply results in a/z initializers are at 3. Boundaries: forward and
loop 1; a and z 2 (`candidate_source.rs:956–1040,1090–1124,1512–1547`).

For each Name of x, its value endpoint is Parameter(X), not a fresh value
row, while its effect row is occurrence-specific
(`candidate_source.rs:889–897,1220–1229`). Let na and nz be the distinct
effect rows of the x Names at forward x and loop x; both start at 3.

The complete original semantic reference edges are:

```text
forward -> Parameter(t)       its direct body Name
a       -> forward, Parameter(x)
z       -> loop, Parameter(x)
loop    -> z                 its final Name
outer   -> loop, Parameter(q) its final Apply's Names.
```

Nested initializers have their own Local owners; Lambda preserves its owner.
The three Apply checking events (slot 0) are:

| Event | Origin | Receiver | SCC-qualified |
| --- | --- | --- | --- |
| ea | Local(a) | Local(forward) | no |
| ez | Local(z) | Local(loop) | yes: loop→z→loop |
| eo | Module(outer) | Local(loop) | no |

This follows from `candidate_value_graph.rs:89–143,181–196,245–247`.
Parameters have no outgoing source references in this input. Helper fragments
preserve these incidences. Names, declaration identity and type rows are not
additional checking events. In particular ea's nonqualification alone would
not prove later noninterference; the physical trace below is needed.

Ordinary `CandidateInference::solve` selects false,false
(`shadow_apply.rs:270–281,385–435`). Source order is: install forward; begin
loop; register x; infer a (Local forward then FormalName x, then Apply);
install a; infer z (active-Link loop then FormalName x, then Apply); install z;
Local z final Name; loop Block/Lambda; install loop; Local loop final callee;
FormalName q; final Apply; enclosing Block/Lambda.
Initializer slot 20 sends its evaluation effect to the block BEFORE Install
(`candidate_source.rs:1090–1124`); initializer effects are not generalized
into the installed value interface. No Name of a or second Name of forward
appears later. Dynamic recursion does not rerun this source schedule or create
new static FreshUse identities.

## 4. First forward use: honest map and physical effect path

FormalEntry, direct FormalNameEffect and Lambda slot 4 generate
t0<=n0, n0<=t0, n0<=r0. Their equal-level physical keys are
(t0,−,n0), (n0,−,t0), (n0,−,r0). The Function domain is Int−, its result v0
has Int+<=v0<=Int−, and Computation omits entry-force slot 3
(`candidate_effect.rs:1437–1461,1493–1522`; `lib.rs:11329–11444`).

F0 is installed live at boundary 1. At a's callee Name, Local capture reaches
the actual private generic level-2 closure and prepares mu1 at level 3
(`candidate_scheme.rs:2011–2038`). It includes the needed original t0,n0,r0
rows: mu1(t0)=t1, mu1(n0)=n1, mu1(r0)=r1. This is an actual partial map on
captured rows, not an arbitrary total substitution. It restores
(t1,−,n1), (n1,−,t1), (n1,−,r1) before root linkage
(`candidate_scheme.rs:755–790,1054–1132,1555–1608,1860–1906,2153–2183`).
FreshUse's source_bound/antecedent metadata names original evidence; it does
not insert scalar equalities between t0 and t1 or forest parents between them.

Let Ca,Ea,Ua be a's invocation effect, Apply output effect and value result,
all initially at 3; B is loop's body BLOCK effect at 2. The native demand is
Da=Function−(X+,na+,Ca−,Ua−). Its callee is the reconstructed level-3 forward
use, not F0. Any whole-demand extrusion into that callee at target 3 copies
no row: X is 2 and all other ports are 3. Function comparison supplies
X<=Int−, na<=t1, r1<=Ca, v1<=Ua
(`shadow_apply.rs:1788–1895`; `lib.rs:12558–12683`).

The following are direct physical keys, with + meaning a stored lower and −
a stored upper; all displayed rows here are effect rows:

| Admission or replay | Required stored key |
| --- | --- |
| ex<=na, na<=ex (actual x Name) | (na,+,ex), (na,−,ex) |
| na<=t1 (Function AE) | (na,−,t1) |
| replay at na | (t1,+,ex) |
| t1<=n1, n1<=r1 (restored provider) | (t1,−,n1), (n1,−,r1) |
| replay at t1 then n1 | (n1,+,ex), (r1,+,ex) |
| r1<=Ca (Function RE) | (r1,−,Ca) |
| replay at r1 | (Ca,+,ex) |
| Ca<=Ea (Apply slot 2) | (Ca,−,Ea) |
| replay at Ca | (Ea,+,ex) |
| Ea<=B (initializer slot 20) | (Ea,−,B) |
| replay at Ea | (ex,−,B) |

The owner rule always stores on the younger endpoint; at equal levels it
stores on the lower row (`candidate_extrusion.rs:912–969`). Each replay is
the actual lower/upper fiber product at that common owner
(`:856–910`; `candidate_context.rs:3763–3835`). The first Name equality has
sources None; native AE/RE port relations have {ea}; restoration and slots
2/20 supply no new checking event. Thus the displayed ex-propagation route
has {ea}, with no ez or eo yet. The original private constraints have no
Apply event. Other pure-effect fibers can coexist and are not collapsed.

This gives the scalar path ex<=t1<=n1<=r1<=Ca<=Ea<=B, and a replay-derived
direct ex<=B. It does NOT assert a materialized direct r1<=B or ex<=rLoop.
Crucially, ex's storage contains no reverse pointer to na/t1/n1/r1. Ea<=B
is stored on younger Ea; B's lower vector does not acquire Ea from that edge.
Row/row effect propagation creates no extrusion parents and performs no
original/fresh row union. The unused Ua value is not loop's block result.

## 5. Recursive demand: complete signed group and source set

Let N be the recursive callee Name value row at 3, Cz the new invocation
effect at 3 and Uz the Apply result at 3. Active `Action::Link` admits L2<=N3,
storing (N,+,L), sources None (slot 30 is not an Apply checking event).
The original recursive native demand is

```text
Dz = Function−(X+, nz+, Cz−, Uz−).
```

Apply stores (N,−,Dz) with sources {ez}. Replay of EXACTLY those physical
inputs produces L<=Dz. The relation source set is union(None,{ez})={ez};
both contexts are identity, and ordinary scoped payload is default
(`candidate_context.rs:2985–2996,3246–3310,3763–3835`). Hence identity context
does not consume the scalar task. Ordinary source collection does not create
local_callee and does not call authenticate_scoped_apply; this is no scoped
experiment or R50 bypass (`candidate_source.rs:1259–1317`;
`shadow_apply.rs:1756–1776`).

Typed row/Function dispatch selects extrude(Dz,−,2). Structural signs are
(X+,nz+,Cz−,Uz−). X is already at target 2: Visit memoizes it and STOPS before
reading its bounds. It is an Int parameter, not a Function containing forward.
nz's positive closure contains ex2 from (nz,+,ex); Visit likewise stops at ex2.
Cz and Uz are fresh and have no selected uppers at this point: Apply slot 2
and Install/final-result actions have not yet executed.

The complete row-parent group for this operation is therefore:

| Parent | Actual new copy | Sign | Target | Sources |
| --- | --- | --- | --- | --- |
| nz3 | nz+ at 2 | + | 2 | {ez} |
| Cz3 | Cz− at 2 | − | 2 | {ez} |
| Uz3 | Uz− at 2 | − | 2 | {ez} |

No X, ex, forward root, t0/n0/r0, or t1/n1/r1 parent is present. The physical
source links are (nz,−,nz+), (Cz,+,Cz−), (Uz,+,Uz−), and copied selected
lower (nz+,+,ex). This is a source-derived complete group for this exact
entrance, not an abstract chosen subset. Actual numeric parent indices are
UNKNOWN; each symbolic pair identifies its real retain call. Source fibers
on a copied bound can retain both the copying relation and transported original
evidence; parent source-set equality above refers to the processing relation,
not an unsupported assertion that every copied fiber has only {ez}
(`candidate_extrusion.rs:423–442`; `candidate_effect.rs:677–715`).

The Visit guard, signs and pending-bound traversal are
`candidate_extrusion.rs:78–167,229–258,330–340`. Each retain reads processing
sources {ez}, qualifies ez via loop↔z, and queues that actual pair
(`candidate_intrusion.rs:308–386`). At empty frontier settlement merges each
copy with its parent, appends both physical sides, takes min(level), ORs
nongeneric, redirects the forest and replays
(`lib.rs:12369–12398`; `candidate_intrusion.rs:568–713`). Write bars for those
three settled representatives: nzbar,Czbar,Uzbar have level 2 and remain
generic. ex and X remain their own rows; no equality to forward rows follows.

Later replay may combine ea and ez source sets; qualification is presence of
any qualifying event, not purity of the set. This does not create new row
aliases by itself. Until the next captures, native remaining Function ports
and body/Apply joins are Int or row/row tasks. Loop's newly formed Function
has domain Int−, AE ex2, RE rLoop2 and result bodyValue2. Its whole structural
admission into L2 visits only atoms or rows already at 2, without selected
bound traversal. Thus there is no subsequent structural entrance into either
forward closure before those captures. This endpoint argument, rather than
ea's nonqualification, establishes the bounded exclusion.

## 6. Next real captures and partial maps

First, z installs its live result Uzbar with boundary 2. Its final Name routes
through Local capture BEFORE the loop Lambda and before loop q. Capture sees
level(Uzbar)=2, hence nonlocal, and stops expansion. Its fresh table retains
that shared identity; it does not define images for forward's rows.
The final Name's pure effect and Block Group are separate from z's initializer
evaluation effect (`candidate_source.rs:1107–1124,1218–1253,1430–1441`;
`candidate_scheme.rs:755–790,1054–1059,2011–2038`).

Then loop's Lambda is constructed and loop installs live L at boundary 1.
Its final outer-body callee Name at level 1 starts the next Local capture.
That capture reaches the positive loop Function and retained negative Dz,
their Int/row ports, nzbar/ex, loop body/result rows and their physical bounds.
From loop's AE ex it can reach B through direct (ex,−,B), and B's Lambda
slot-4 upper rLoop. These rows are generic above boundary 1 and obtain one
actual row map nu at use level 1.

There is no physical reverse entrance from this loop-root closure to
forward's Function, its first-use t1/n1/r1, or the original t0/n0/r0:
the x Names' edges are owned on the younger Name rows; the forward effect
route's exit is owned on its younger rows; a's value is unused; and the
signed group did not union those rows. Capture follows stored endpoints, not
lexical sibling declarations or the whole locals table. Identity contexts
add no Allowance payload; ordinary mode adds no scoped latent demand that
would intern Da (`candidate_scheme.rs:945–1132,1259–1292`).

Consequently nu reconstructs LOOP's ports, including AE=nu(ex) and
RE=nu(rLoop), and restores their captured ex<=B<=rLoop route. It is NOT
mu1 followed by a forward recapture. nu(t1), nu(n1), nu(r1), or nu(t0/n0/r0)
cannot be invented as provider images: those endpoints are absent from this
loop capture's row table. Retained source_bound/transport metadata can still
mention their source identity without adding graph.rows or a physical alias
(`candidate_context.rs:4051–4070`). In contrast mu1's required forward
images were genuinely present at the earlier forward capture in §4.

Restoration uses the same nu table as Function reconstruction and inserts
captured bounds before the Local root is returned
(`candidate_scheme.rs:1555–1608,1715–1755,1860–1906,2153–2183`;
`candidate_extrusion.rs:763–789`). The later loop q Apply's actual argument
is q's Name; event eo is nonqualified. It is not a second forward use.
No claim about a further enclosing/module capture or complete final solve
is needed for this finite-input exclusion.

## 7. Remaining premise, falsifiers, reuse and stop

The original template remains separate and unchanged through these captures;
the one forward use's mu1 route was supplied before the recursive group.
No same-provider later forward comparison/capture exists here. This supplies
an exclusion for R55-ORIGINAL-INT-RECURSION-1's proposed entrance and reduces
its concrete input uncertainty. It does not establish R55-CORE-EXPOSURE-1
for other original-domain source histories or close mapped admission generally.
The parent's arbitrary finite prefixes, repetitions, independent live receivers,
shared assignment and foreign-continuation quantifiers remain unchanged.

Falsifiers: a real structural/selected-bound operand in this source reaches
F0/t0/n0/r0 or F1/t1/n1/r1 from the recursive extrusion; the L<=Dz relation
contains another source before that group; a listed row initially has a
different level or selected upper; a physically stored reverse edge crosses
the closure cut; a context payload actually interns Da into loop's graph;
or a later syntactic forward Name was omitted. Numeric identity spelling and
original-evidence metadata alone are not such falsifiers.

Mutual TODO R56-ORIGINAL-EXPOSURE-NEXT-1, owner Luna: choose a distinct approved
original-domain source-owner input that actually reaches an original forward
closure through structural/physical operands and has a later capture of that
SAME provider, or prove the corresponding source case excludes it. Required
evidence remains complete source sets, all signed parents, physical owner keys,
actual capture boundary and honest partial correspondence. An authentic first
partial alias falsifies a proposed J exclusion; parent refutation additionally
needs the missing same-provider mapped route after actual restoration. No new
source, dependency, code lease, execution or instrumentation is authorized here.

Reused: R55's exact original-domain source shape, original-template owners,
and partial-map warning. Re-established from the current pinned owners:
ordinary/scoped distinction, signed Visit guard, source-set union, physical
owner selection, settlement and capture. Rejected: earlier callable-argument
examples as parent instances; a sink SCC as global purity; metadata as scalar
alias; composed inequalities as materialized transitive keys; static identities
as dynamic entries; treating the loop map as a forward map. No producer review
or universal induction renewal was performed.

Three stages complete: exact source/domain freeze; owner/event/signed trace;
bounded application to R55. All 23 dependency pins and contract matched before
writing and at freeze. Static reads/searches and SHA-256 only; no parser,
preflight, solver, test, build, runtime, probe, instrumentation, measurements,
Git, code/semantic edit, external contact, scratch or descendants.
Requested Sol/high; observed model/effort UNKNOWN/UNKNOWN. Current-session
active-work receipt was sent to Luna after the R56 NEW_TASK. 900 seconds
charged for this assignment; no carryover/expansion; measured CPU/RSS/duration
UNKNOWN. Only the two exclusive new paths exist from this writer. STOPPED /
WRITES_STOPPED / NO_DESCENDANTS on frozen hash submission; fresh review and
all acceptance belong to Luna. Parent OPEN 0→0; R50 NOT ADOPTED.

Frozen direct dependency manifest follows.

```text
d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79  notes/theory/2026-10-15-computation-forwarding-preservation.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
38d42183fdc4f2c0136112d8b305816241d8f449367b473e4de3a5135dc49895  notes/design/2026-10-10-local-self-recursive-binding.md
59af7c1fd429f7c71d5a9c5bb3c6660519b18164329650cd32caaef784b6c1e6  tools/inference-playground/README.md
4c292a24c7fba19c40587fcc2cb9374fdbff3dd7059533548e4e1be1420546d1  tasks/agent-loop/sprints/original-name-core-20261019-r55.md
db5e8115e3f853e7831ffaf525e4c794bdca9892a18d7fb153f395451f94a40b  notes/theory/2026-10-19-r55-original-name-core.md
0e9f5274a4d5eb556ef7e37bd98444a8270213c1e8b7570726fa32c59c5acbdd  tasks/agent-loop/inbox/20261019-r55-core.md
0ebbc5e0e0b1c85b3f89e9017d9759fc3c8cfec80aced22457ed2fdc5867b258  notes/theory/2026-10-19-r55-original-name-attack.md
fcf17066b8a4a3198b4e5a7aabc492b6da5bf571a4bb042d5e40d5eb6f0602a2  tasks/agent-loop/inbox/20261019-r55-attack.md
d1aa7f1a1af5da50a78e012540e9c0f01878a3ec13bb43d2565f75ae279895a4  notes/progress/2026-10-19-r55-original-name-owners.md
2bd40ed7f8ea15fa9d06fae39c2064b06bade04887c007414dd0f0cdc43e3d65  tasks/agent-loop/inbox/20261019-r55-implementation.md
b688f6677a4f6572d7e947ccd5b26883620b951f63585706c7ba866aae6d80ad  notes/progress/2026-10-19-r55-closeout.md
66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c  crates/yu-solver/src/candidate_source.rs
8738c1b1699228b1a4dfd30af7e03d0afb100ca6124d23037c645246d888dc50  crates/yu-solver/src/candidate_value_graph.rs
e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479  crates/yu-solver/src/candidate_call.rs
6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0  crates/yu-solver/src/candidate_effect.rs
d4ff8a9e98eb667a5eb85aff9c0feec1f0227e86257bb56892493ac1d04a9278  crates/yu-solver/src/candidate_scheme.rs
fc0d948d884a406746066f3df8db257d5c6686505166b330bef839a9b9e2f35d  crates/yu-solver/src/candidate_extrusion.rs
8a1f531be9fb5e5f160bf4f75c6eb98bbc35ce0a30acaf06424c531840504ba4  crates/yu-solver/src/candidate_intrusion.rs
42f89dcf5fa6d7095db1e220c89308a2a35f4e74b05c3e8821d4fb2e3e32b0ca  crates/yu-solver/src/candidate_context.rs
5bbcf27d51906814ba38b2cca2066807d285d0b1817f0ea6e04d70c4a5c8a5cb  crates/yu-solver/src/shadow_apply.rs
2300400e87d0a487225f207d414ac71fa4f21c6f80279fea4f793e43c7809aee  crates/yu-solver/src/lib.rs
ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5  crates/yu-hir/src/module/local_source.rs
```
