# R57: second authentic forward capture after a qualified recursive group

Status: candidate bounded constructive source/native result; fresh independent
review pending. Sole author `/root/r53_ordinary_mixed_capture_proof`, session
`current-conversation-2026-10-19-r57`; no descendants.
Contract revision 1, SHA-256
`b8fb35aa130304ab459b1c8ead188c5ebd6c86bb177420842f279a1d17f4c5a9`.
Baseline `abef89fb8491c5709173ba55c76af7886897a5bd`; parent-reported activation
commit `b3530cd58`, no Git operation performed.
Exclusive outputs: this artifact and `tasks/agent-loop/inbox/20261019-r57-proof.md`.

## 1. Fixed claim and result

For the exact source below, under successful ordinary constructor prefixes,
the first forward use and the intervening qualified recursive construction
leave the original published forward value closure unchanged until the second
forward Local action. That second action captures the SAME original provider
and constructs a distinct authentic partial map mu_b. Its actual Function
ports and restored bounds satisfy

```text
mu_b(t0)<=mu_b(n0)<=mu_b(r0),  mu_b(n0)<=mu_b(t0).
```

The maps and admissions are conclusions of the owner trace, not assumptions.
“Successful prefix” conditions successful fallible source actions, drains,
capture, reconstruction and restoration. It is not an observed parser,
preflight or solver run, proof of whole-session typing/termination, invocation,
dynamic receipt or runtime behavior. No source-qualified counterexample is
claimed. The bounded proof stops after the second local use/admission; it does
not renew a universal induction or assert all later captures are covered.

Apply this to R55's OPEN owner judgment: this is a positive original-domain
two-use case with an intervening source-qualified group, and establishes the
second use's scalar mapped-admission premise. The original universal premise,
arbitrary finite histories, independent live receivers, shared satisfying
assignment and foreign-continuation quantifiers remain OPEN 0→0. There is no
complete-Call, hygiene, soundness/principality or production promotion.
R50 remains NOT ADOPTED.

## 2. Exact source and recomputed original-domain events

```text
act io:
    our tick: int -> int

my outer (q:[io] int) = {
  my forward (t:[io] int) = t;
  my loop (x:[io] int) = {
    my a = forward x;
    my z = loop x;
    my b = forward x;
    z
  };
  loop q
}
```

The in-source declaration supplies one concrete resolved io identity and a
monomorphic Int→Int operation signature; it invokes no operation. Each q,t,x
has an explicit outer Computation annotation with finite {io} and no tail.
All FOUR actual arguments are the whole current-formal Name (x,x,x,q), and
forward's body is its exact original formal Name t. This is constructor-level
membership in forwarding-preservation §1 and its §6 direct-Name-provider
shape for forward. The parent's base-typing/typed-interaction hypotheses are
separate. No callable argument, higher-order interface, mutual recursion or
source restriction is introduced. Source formation and the selected recursive
binder rule are the pinned LocalSource/authority owners; the pinned playground
README gives the same act declaration form at lines 125–136.

Recompute the entire original semantic reference graph for THIS changed input:

```text
forward -> Parameter(t)
a       -> forward, Parameter(x)
z       -> loop, Parameter(x)
b       -> forward, Parameter(x)
loop    -> z
outer   -> loop, Parameter(q).
```

Nested initializers switch to their own Local owners; Lambda bodies retain
the owner (`candidate_value_graph.rs:89–143`). The complete Apply events are:

| Event | Origin | Receiver | Qualification |
| --- | --- | --- | --- |
| epsilon_a | Local(a) | Local(forward) | no |
| epsilon_z | Local(z) | Local(loop) | yes, loop→z→loop |
| epsilon_b | Local(b) | Local(forward) | no |
| epsilon_o | Module(outer) | Local(loop) | no |

The construction/criterion are `candidate_value_graph.rs:181–196,245–247`.
Forward and parameters have no path back to a or b; loop does not reference
b because the final result remains z. Events are allocation-qualified source
identities, not numeric runtime IDs or type-row SCCs. The b event is newly
derived, not identified with a's event despite sharing the callee declaration.

## 3. Collection, actual action order and row identities

Collection retains all four source events and all action recipes. It does
not execute b early: source-mode `execute` skips `admit_all_collected_facts`
(`lib.rs:10424–10439`), and `append_source_facts` puts each fact in its
scheduled position (`candidate_source.rs:1482–1484`). The explicit work stack
visits initializers sequentially and each Apply's callee before argument
(`:970–1040`). Future b/outer events therefore affect the already sealed
source graph but cannot pre-seed an earlier processing relation.

Actual relevant order is forward template/Install; loop parameter setup;
a's Local forward, Name x, Apply, slot-20 initializer effect and Install;
z's active Link loop, Name x, Apply/settlement, slot-20 effect and Install;
b's Local forward, Name x, Apply, slot-20 effect and Install; final Local z;
loop Block/Lambda/Install; outer Local loop, Name q, Apply. The new b capture
occurs BEFORE the final z capture and BEFORE loop's Lambda construction.
Initializer effects flow once into their enclosing block before Install
(`candidate_source.rs:1090–1124`), not into the generalized value interface.

Use immutable allocation-qualified names, distinct from forest representatives:

| Rows | Initial levels / boundary |
| --- | --- |
| original forward root F0; entry t0; body-Name n0; Lambda RE r0; value v0 | 2; installed boundary 1 |
| loop root L, parameter VALUE X, registered EFFECT ex, body rows | 2 |
| first-use forward rows F_a,t_a,n_a,r_a,v_a | fresh at 3 |
| each initializer's callee Name/value result/output effect; argument x-Name effect h_a,h_z,h_b | 3 |
| second-use forward rows F_b,t_b,n_b,r_b,v_b | freshly constructed at 3 below |
| outer/q and final outer-body Apply | 1 |

The x Names' VALUE endpoint is the SAME Parameter X2, rather than a new
Name value row; their effect rows h_i are distinct
(`candidate_source.rs:889–897,1220–1229,1512–1547`). a,z,b install at boundary
2; forward and loop at 1. Metadata starts generic; fresh allocation is generic
(`lib.rs:10138–10184,10243–10298`).

Ordinary solve is `solve_mode(hir,false,false)`
(`shadow_apply.rs:270–281,385–435`). The scoped local-callee construction and
authentication gates do not execute; recipe/source identity checks still do
(`candidate_source.rs:1259–1317`; `shadow_apply.rs:1756–1776`).

## 4. First use and its complete relevant physical footprint

Original registration/Name/Lambda construct physical uppers
(t0,−,n0), (n0,−,t0), (n0,−,r0). The Function is
P0=(Int−,t0,r0,v0), where Int+<=v0<=Int−; v0 is not an Int leaf substitution.
Computation omits entry-force slot 3 and concrete permission does not cap t0
(`candidate_effect.rs:1437–1461,1493–1522`; `lib.rs:11329–11444`). F0 has
its actual positive Function lower. This entire private value closure is
generic2 above its installed boundary1.

The first Local action reads that live F0 and prepares actual mu_a at3. All
required rows are captured: mu_a(t0)=t_a, mu_a(n0)=n_a, mu_a(r0)=r_a. It restores
(t_a,−,n_a), (n_a,−,t_a), (n_a,−,r_a) before its fresh root is linked to the
callee Name K_a. Its writes are to these fresh rows and K_a, not F0 or the
original closure (`candidate_scheme.rs:2011–2076,2153–2214`).

Let C_i,E_i,U_i be invocation effect, Apply output effect and value result of
initializer i; B is loop's body effect2. Native demand
Da=Function−(X2+,h_a3+,C_a3−,U_a3−) compares against the fresh callee.
Whole-demand extrusion into a level-3 row copies nothing: all ports are
at/below3. The actual Function tasks are X<=Int−, h_a<=t_a, r_a<=C_a,
v_a<=U_a (`shadow_apply.rs:1788–1895`; `lib.rs:12558–12683`).

Relevant EFFECT storage/replay, writing + for lower-side and − for upper-side:

```text
(h_a,+,ex), (h_a,−,ex)                 actual x Name equality
(h_a,−,t_a)                          Function AE
(t_a,+,ex), (n_a,+,ex), (r_a,+,ex)    replay along provider uppers
(r_a,−,C_a), (C_a,+,ex)               Function RE and replay
(C_a,−,E_a), (E_a,+,ex)               Apply slot 2 and replay
(E_a,−,B), (ex,−,B)                  initializer slot 20 and replay.
```

The provider uppers used in the third line are exactly the restored
(t_a,−,n_a),(n_a,−,r_a); the reverse n_a<=t_a remains present. Each derived
ex lower is on the younger level-3 owner; the final ex<=B, at equal level2,
is stored on ex as an upper. These keys give a scalar path through r_a to B
and a replay-derived direct ex<=B, not a claimed directly stored r_a<=B.
Owner choice/replay are `candidate_extrusion.rs:856–969`.

The original template and Local root-link fibers have no Apply event.
Da's seed has {epsilon_a}; replay with the no-event provider lower retains
{epsilon_a}; each Function port inherits it. Thus the h_a/ex propagation
fibers above carry {epsilon_a} after union with original/slot-2/slot-20
no-event fibers. Pure atom fibers may coexist. Source sets belong to individual
relations, not globally to ex or a physical endpoint pair.

No row/row effect task retains an extrusion parent. VALUE writes use X,
fresh v_a/U_a and immutable Int atoms. a's unused value does not connect to
loop's result. No scalar link or parent alias reaches original F0/t0/n0/r0/v0.
Fresh evidence's original source_bound/antecedent records are provenance,
not an equality or permission to use original endpoints as write targets
(`candidate_scheme.rs:1860–1906`; `candidate_context.rs:4051–4070`).

## 5. Recursive signed group, sources and bounded noninterference

The recursive callee Name N3 uses active `Action::Link`, not a LocalScheme.
L2<=N3 stores (N,+,L), with no checking source at slot30. Its actual new demand
is Dz=Function−(X2+,h_z3+,C_z3−,U_z3−), retained in NativeInterface before
admission. N<=Dz stores (N,−,Dz) with source {epsilon_z}. Ordered replay of
these EXACT two inputs produces L<=Dz with

```text
sources = union(None,{epsilon_z}) = {epsilon_z}; context = identity.
```

The seed/union/product owners are `candidate_context.rs:2985–2996,3246–3310,
3763–3835`; identity context is not consumed at `:3575–3601`. epsilon_a's
outgoing effect bound ex<=B is not an input fiber of this VALUE replay, nor
does a future epsilon_b seed exist yet. Thus this source set is derived
afresh for R57 and is complete for the processing relation selecting the group.

Typed row/Function dispatch selects extrude(Dz,−,2). Its four signed ports
are (X+,h_z+,C_z−,U_z−). Visit stops at X2 without traversing its bounds.
Positive closure of h_z contains ex2 from (h_z,+,ex), then stops at ex2 too.
C_z and U_z are new rows with no selected uppers before this Apply's later
slot-2 or initializer/final-result actions. Complete retained row-parent group:

| Parent | New copy | Sign | Target | Parent processing sources |
| --- | --- | --- | --- | --- |
| h_z3 | h_z+ at2 | + | 2 | {epsilon_z} |
| C_z3 | C_z− at2 | − | 2 | {epsilon_z} |
| U_z3 | U_z− at2 | − | 2 | {epsilon_z} |

No X/ex or forward row is a co-parent. Physical links are
(h_z,−,h_z+), (C_z,+,C_z−), (U_z,+,U_z−), with copied lower (h_z+,+,ex).
Visit/sign/pending owners are `candidate_extrusion.rs:78–167,229–258,330–340`.
Each retain snapshots these processing sources, sees qualified epsilon_z and
queues that actual pair; finish records the whole group
(`candidate_intrusion.rs:308–386`). Copied-bound bootstrap and transported
original fibers may coexist with different source sets; that does not make
every fiber globally {epsilon_z} or change the listed Parent sources
(`candidate_extrusion.rs:423–442`; `candidate_effect.rs:677–715`).

The drain settles at empty frontier and resumes merge-generated work
(`lib.rs:12369–12398`). Merge appends BOTH sides to the parent representative,
takes min(level), ORs nongeneric, redirects copy→parent and replays lowers
(`candidate_intrusion.rs:568–713`). Quotient Q therefore joins just each
listed pair: h_zbar,C_zbar,U_zbar become generic2. Q does not join ex/X to
them or touch any original/first-use forward row. Physical stored vectors
can contain old/reflexive slots; their canonical interpretation and retained
relation lineage remain separate. Settlement replay can add further relations
on these rows, not fabricate a new source operand into F0.

Before b's Local action, subsequent source actions are z's effect joins and
Install. They use C_zbar,E_z,B,U_zbar; there is no loop Lambda yet. Their
row/row tasks cannot start structural traversal into a forward Function.
Source-set union may retain different fibers on equal keys; presence of a
qualified source is not by itself a write to another row. The finite footprint
is original loop/Name/body rows, the three actual copied rows, and a's fresh
closure; its structural visits never reach F0/t0/n0/r0/v0. Shared Int atoms,
ex/X, or original-source evidence create no mutable row alias. Hence ALL
original forward closure rows retain their physical bounds, generic2 metadata,
representatives and installed root/boundary through this prefix.

This is the necessary noninterference argument. It is not an inference from
forward's sink SCC, or from the first-use lemma being applicable once.

## 6. The actual second capture, map and restored bounds

b's callee Name is a different resolved occurrence of the SAME Local forward.
It emits `Action::Local` for the same slot; active loop recursion does not
make forward active again (`candidate_source.rs:1238–1253`). The successful
a route commits its completed frame into a retained LocalFreshRoute, removing
that frame (`candidate_scheme.rs:662–691`; `lib.rs:9302–9316`). b therefore
starts a new route, rather than resuming a's frame.

`route_candidate_local_run` reads the same stored (F0,boundary1) and captures
the NOW-live graph (`candidate_scheme.rs:2011–2038`). Section 5 derived that
this graph still contains its original generic2 t0/n0/r0 route. Capture from
F0 reaches P0 and its t0/r0 ports; t0's upper reaches n0, and n0's uppers reach
t0/r0 (`:755–790,945–1132,1259–1292`). Thus all required endpoints and their
physical bounds are actually captured; none is assigned an invented image.

`prepare_candidate_fresh_use` invokes begin_use again and allocates ONE image
per canonical local/generic row (`:1555–1608`; `candidate_context.rs:2997–3000`).
Write the actual partial correspondence mu_b. It supplies

```text
mu_b(F0)=F_b, mu_b(t0)=t_b, mu_b(n0)=n_b,
mu_b(r0)=r_b, mu_b(v0)=v_b.
```

These mutable rows are newly allocated at3, distinct from the corresponding
mu_a rows and the original rows. The two nonzero context_use identities are
distinct; their numeric values are UNKNOWN. Immutable Int and outer X/ex can
be shared by later constraints without identifying the two use maps.

Function reconstruction consumes that SAME mu_b table, producing
P_b=(Int−,t_b,r_b,v_b) (`candidate_scheme.rs:1715–1755`). Bound reconstruction
preserves captured physical side and uses the same table (`:1860–1906`). It
physically inserts, at minimum,

```text
(F_b,+,P_b),
(t_b,−,n_b), (n_b,−,t_b), (n_b,−,r_b),
(v_b,+,Int+), (v_b,−,Int−).
```

`candidate_begin_bound_restoration` inserts before retaining/driving the
restoration operation (`candidate_extrusion.rs:763–789`). The Local owner
finishes all captured bounds before linking F_b to b's callee occurrence and
committing its route (`candidate_scheme.rs:2165–2214,662–691`). These freshly
restored provider fibers transport the no-event original evidence, not
epsilon_a or epsilon_z merely because those events occurred earlier. The
root link itself is the callee Name's no-checking-event slot0, not the Apply's
checking occurrence. This establishes the displayed mapped-admission result.

If the same normal prefix continues through b's Apply, the actual x-Name
effect is h_b3, with (h_b,+,ex),(h_b,−,ex); native Db has ports
(X2+,h_b3+,C_b3−,U_b3−). Its seed is {epsilon_b}, and replay against P_b's
no-event lower keeps exactly {epsilon_b} for the Function comparison.
The tasks h_b<=t_b and r_b<=C_b use those actual ports. Replay through
(t_b,−,n_b),(n_b,−,r_b) restores the same ex propagation pattern with b-indexed
owners. For this compared provider in every satisfying interpretation:

```text
h_b <= t_b <= n_b <= r_b <= C_b <= E_b.
```

epsilon_b remains a separate nonqualified source; sharing ex does not union
epsilon_a into this Function comparison. After b's slot-20 effect the physical
key (ex,−,B) can have a- and b-derived alternative fibers. Their co-residence
does not identify their events/maps or select marginal witnesses across them.
No claim about all later replay source sets or the later loop/module captures
is needed; those owners would require their own trace.

## 7. Parent application, falsifiers and receipt

This derives a second actual scalar mapped-admission supplier for the SAME
published original direct-Name provider after an intervening qualified group.
Its application to forwarding-preservation §6 is indexed separately for a/b;
the second map is not a copy of the first map, and neither maps original rows
by semantic equality. The result supplies no runtime receiving instance,
permission/protection/receipt transport, Force, foreign continuation, complete
Call, general mixed-cut theorem or universal original-template preservation.

Falsify the bounded proof by an earlier physical write/alias into the original
closure; a source-set input carrying another event into L<=Dz; a selected
structural operand/parent omitted from the three-row group; a hidden earlier
b action admission; a stale Local frame reused for b; a second capture that
uses another root/boundary; absent original n0 or bounds in that capture; or
different tables for P_b ports and restored t_b/n_b/r_b. Original-evidence
metadata alone is not a physical alias, and a test of assumed transitions
would not establish this source trace.

Mutual TODO R57-GENERAL-EXPOSURE-1, owner Luna: apply this bounded case to the
remaining original-domain source-exposure classification. Any broader claim
must still derive the actual structural/physical entrance, complete sources
and signed group before a same-provider capture, including other qualifying
histories and nonlocal/nongeneric cuts. Falsifier of a proposed exclusion is
a reachable first partial alias; parent refutation additionally needs an exact
missing same-provider mapped route after restoration. This TODO grants no new
source, lease, semantics, dependency, execution or instrumentation authority.

Prior work reused only within premises: R55 original-domain/template/partial-map
requirements and reviewed R56 owner rules. Recomputed for R57: all four events,
qualification, action chronology, pre-b processing sources and signed group,
write footprint and second capture. R56 had no second forward occurrence;
that missing occurrence is not silently supplied by dynamic recursion. Rejected:
callable-argument examples as original-domain instances; source SCC as global
purity; original/fresh equality; a total mu for uncaptured rows; shared endpoint
as a source union; provenance as alias; green assumed transitions as source proof.

Three finite stages complete: source/dependency freeze; owner/source/write
derivation; second capture and parent application. All 28 exact pins and the
contract matched before work/writes and at freeze. Static reads/searches and
SHA-256 only. No parser/preflight/solver/test/build/runtime/probe/instrumentation,
code/semantic edits, measurements, Git, external contact, scratch or descendants.
Requested Sol/high; observed model/effort UNKNOWN/UNKNOWN. Current-session
active-work receipt sent after validation. 900 seconds charged, no carryover
or expansion; measured duration/CPU/RSS UNKNOWN. Stop at this bounded outcome;
fresh independent review and integration belong to Luna. STOPPED /
WRITES_STOPPED / NO_DESCENDANTS on hash submission. Only the two exact leased
new paths were written. Parent OPEN 0→0; R50 NOT ADOPTED.

Frozen direct dependency manifest follows.

```text
ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5  crates/yu-hir/src/module/local_source.rs
e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479  crates/yu-solver/src/candidate_call.rs
42f89dcf5fa6d7095db1e220c89308a2a35f4e74b05c3e8821d4fb2e3e32b0ca  crates/yu-solver/src/candidate_context.rs
6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0  crates/yu-solver/src/candidate_effect.rs
fc0d948d884a406746066f3df8db257d5c6686505166b330bef839a9b9e2f35d  crates/yu-solver/src/candidate_extrusion.rs
8a1f531be9fb5e5f160bf4f75c6eb98bbc35ce0a30acaf06424c531840504ba4  crates/yu-solver/src/candidate_intrusion.rs
d4ff8a9e98eb667a5eb85aff9c0feec1f0227e86257bb56892493ac1d04a9278  crates/yu-solver/src/candidate_scheme.rs
66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c  crates/yu-solver/src/candidate_source.rs
8738c1b1699228b1a4dfd30af7e03d0afb100ca6124d23037c645246d888dc50  crates/yu-solver/src/candidate_value_graph.rs
2300400e87d0a487225f207d414ac71fa4f21c6f80279fea4f793e43c7809aee  crates/yu-solver/src/lib.rs
5bbcf27d51906814ba38b2cca2066807d285d0b1817f0ea6e04d70c4a5c8a5cb  crates/yu-solver/src/shadow_apply.rs
38d42183fdc4f2c0136112d8b305816241d8f449367b473e4de3a5135dc49895  notes/design/2026-10-10-local-self-recursive-binding.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
b688f6677a4f6572d7e947ccd5b26883620b951f63585706c7ba866aae6d80ad  notes/progress/2026-10-19-r55-closeout.md
d1aa7f1a1af5da50a78e012540e9c0f01878a3ec13bb43d2565f75ae279895a4  notes/progress/2026-10-19-r55-original-name-owners.md
e9442fa05666018bb7bb2eefede2f6ef7867c6355a1e793bbb08ea825587a6d2  notes/progress/2026-10-19-r56-original-name-owner-trace.md
d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79  notes/theory/2026-10-15-computation-forwarding-preservation.md
0ebbc5e0e0b1c85b3f89e9017d9759fc3c8cfec80aced22457ed2fdc5867b258  notes/theory/2026-10-19-r55-original-name-attack.md
db5e8115e3f853e7831ffaf525e4c794bdca9892a18d7fb153f395451f94a40b  notes/theory/2026-10-19-r55-original-name-core.md
ee5edcaaa64b32323cd60b1a960aecd7f8cf239e17103a7f0e2bcc14cf8691fd  notes/theory/2026-10-19-r56-original-name-source-trace.md
fcf17066b8a4a3198b4e5a7aabc492b6da5bf571a4bb042d5e40d5eb6f0602a2  tasks/agent-loop/inbox/20261019-r55-attack.md
0e9f5274a4d5eb556ef7e37bd98444a8270213c1e8b7570726fa32c59c5acbdd  tasks/agent-loop/inbox/20261019-r55-core.md
2bd40ed7f8ea15fa9d06fae39c2064b06bade04887c007414dd0f0cdc43e3d65  tasks/agent-loop/inbox/20261019-r55-implementation.md
dac34a1377881f2519ff3486d1d3ce88114cac73d5477837da70ef77a4d747b1  tasks/agent-loop/inbox/20261019-r56-implementation.md
0fcdb5b9046e4beb9538bce4f423678170a02af56bf98d302f9d0708aead63f3  tasks/agent-loop/inbox/20261019-r56-proof.md
4c292a24c7fba19c40587fcc2cb9374fdbff3dd7059533548e4e1be1420546d1  tasks/agent-loop/sprints/original-name-core-20261019-r55.md
052492309a379f3eef24078b9090f8e7081dceaf2e4c7af37ff90c75ffa013cd  tasks/agent-loop/sprints/original-name-source-trace-20261019-r56.md
59af7c1fd429f7c71d5a9c5bb3c6660519b18164329650cd32caaef784b6c1e6  tools/inference-playground/README.md
```
