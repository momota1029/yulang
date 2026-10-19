# R138 ordered helper ledger: source actions and a bounded capture reduction

Status: **UNREVIEWED CANDIDATE SOURCE/NATIVE DERIVATION; UNFINISHED/OPEN.**
Fixed outcome A/B/C is not established. Author `/root/r138_proof`; no coauthors
or descendants. Requested `gpt-6-sol` / high; observed model/effort UNKNOWN.
Session `current-conversation-2026-10-20-r138`; launch receipt is Luna's actual
`spawn_agent` acknowledgement for this identity, followed by this worker's
active-work acknowledgement. No independent certification is supplied.

Contract revision 1:
`tasks/agent-loop/sprints/helper-cut-ledger-20261020-r138-rev1.md`, SHA-256
`8bfe31e038f1c7684ac2d9dba95164f13448e150ccb08a874bea22610fc6e04f`.
Baseline supplied by Luna: `66c7b52b197aa035d6feaf20ff4f84198a92f9cb`.
All 39 direct live-byte SHA-256 pins matched at entry; baseline-tree equality
is Luna's receipt, not a Git operation by this leaf.

## Parent application and scope

The parent is computation-forwarding preservation §§1, 6–7 at
`notes/theory/2026-10-15-computation-forwarding-preservation.md`: one shared
satisfying assignment, original current-formal identities and whole Name
arguments, every finite prefix, repeated calls, simultaneous receiving entries
and independent foreign-continuation obligations. Its native mapped-admission
and dynamic receiving/read/Force premises, full inference/evaluator
correspondence, Simple-sub A/B and production stay OPEN 0→0. R50 is NOT ADOPTED.
No local action below discharges a foreign-continuation quantifier.

The source is exactly the contract's ordinary-mode source:

```yu
act io:
    our tick: int -> int

my outer (q:[io] int) = {
    my loop (x:[io] int) = {
        my direct = loop x
        my helper (y:[io] int) = loop y
        helper x
    }
    loop q
}
```

The new contribution is an ordered source/action inventory and a constructor
noninterference argument for the helper's structural capture, followed by an
explicit restoration trace and suffix frontier. This removes the need to
*assume* R73's two-owner structural projection in this successful-prefix
analysis. It does not supply the complete global memo/fiber/completion ledger
required by the frozen contract. In particular the suffix section does not
assert that an unseen retained rewrite is absent. All fallible constructors
and drains discussed below are considered on their successful paths; this is
not a proof that a full solve succeeds or terminates.

## 1. Revalidation of all eight changed owners

| Current owner and SHA-256 | R138 rederived claim |
| --- | --- |
| `module.rs` `153a23ecaa68fd150d8bd0cc0316f3723e1cb5d98a6e3026aadef2bfd08fd907` | `lower_module_with_counters` retains the effect declaration namespace before lowering bindings; `lower_plan` passes original top-level parameters to `local_source::form` when the selected local-source route is enabled (§§1160–1210, 2030–2180). No source effect declaration is an invocation. |
| `module/local_source.rs` `d9f516993c579ae8f4dd905abb8400ffc0769072a904a4b4c8d4ffbefcde6442` | `Builder::slot`, `block`, `Work::Initializer` and `Publish` derive the table below. Initializers with parameters temporarily publish their original self identity; helper therefore resolves loop's still-active original identity. Publication restores lexical depth first (§§594–765, 837–850, 897–1027, 1378–1505). |
| `candidate_source.rs` `cbc39315f4243b0bae1db74976cf94282bc94cd28b9eb463699c085f421065f7` | `preflight`, `Work::Visit/Initializer/Install/Finish`, `initialize_candidate_source_levels`, and `execute_candidate_action` derive roles, levels and action order. Installation has a separate `Stage::PublishLocal`; Local completes before `next` advances (§§450–505, 850–1045, 1138–1163, 1294–1329, 1482–1543, 1590–1762). |
| `candidate_value_graph.rs` `19da9779e3e7866f5891e019e1cd343136ae0115bd1c47a02a7e7ee0cdfa80e0` | `retain_source` gives each initializer its original Local owner and enumerates checking events by expression-vector order. Fragment vertices preserve the same semantic Name reachability; `qualifies` uses original-Value SCCs (§§84–213, 216–247). |
| `candidate_scheme.rs` `2e64dc8781189b4da21c30f4d1b3208aaef48ca247cae55fb7e77e68b5857850` | `Capture::{intern,row,bound,expand_row}`, `capture_candidate_graph_inner`, `prepare_candidate_fresh_use`, `begin_candidate_fresh_bound` and `step_candidate_local_use` retain polarity, row order, exact fiber enumeration, immutable evidence snapshots and serial restorations. Shared rows are not adjacency-expanded (§§741–790, 1001–1156, 1217–1297, 1555–1632, 1855–1908, 2030–2076, 2170ff). |
| `candidate_context.rs` `002b9d86e26cfda6fdf094ea4d161501849a7127d55c2d147d408a781b9fd28d` | `RelationKey` includes pair/context/sources/scoped flow; `attach` prepends only a previously absent exact RelationId. Bound cursor order is newest attached first. Fresh transport and ordinary physical admission are distinct dependencies even when interning gives the same RelationId (§§2902–2983, 3130–3167, 3663–3714, 3767–3850, 4051–4066). |
| `lib.rs` `c75bf47b3d0d87e99d4365a587e6b90d5d05d05c335db16880cb2943b8b25985` | `occurrence_component` and `definition_value_component` register the immutable term→recipe-position table; `component_endpoint` now reads `component_term_positions`, then `live_components`. A collected ordinal is not a live row number (§§1938–1979, 10120–10184, 11499–11506). `admit_lambda_fact`, actual `run_candidate_typed_drain` and `candidate_step_function_dispatch` supply the provider, successful-drain boundary and child order (§§11327–11480, 12290–12440, 12807–12834). |
| `shadow_apply.rs` `838d862dd34fe2b2bd70c5d92c5ce9af0aa98f10f8b6a8eddf313ae798686543` | `solve` selects `solve_mode(false,false)`; scoped Local authentication is guarded and excluded. Ordinary source recipe/endpoint checks remain. `admit_candidate_fact` admits Apply slot 0 and drains it before slots 1 and 2; `candidate_local_lambda_effect` emits slots 0,1 (§§271–281, 385–435, 1436–1446, 1756–1924). |

The unchanged extrusion, effect and intrusion owners were also inspected at
their current pins. `candidate_formal_value_pair` selects Int+/Int−;
`candidate_formal_annotation` stores Int− as the domain; `admit_lambda_fact`
uses it. Thus the helper provider's Argument is **Int−**, never Y−. Its AE
is original `t_y`, and its RE is allocated at the *current* parameter level.

## 2. Source identity and action ledger

All indices in this section are constructor-derived vector/recipe indices,
not observed runtime IDs. `o[i]` is the actual occurrence retained at original
LocalSource expression index i. The new `component_term_positions` bridge
means `v[i]` / `e[i]` below denote the live endpoints obtained from that
occurrence's recipes, not i itself. Parameter values Q, X, Y are obtained via
`CandidateEndpoint::Parameter` at recipe positions 0,1,2.

`Builder::block` reserves its final expression before its initializers;
`Builder::expression(OperatorChain)` reserves callee then argument. Applying
those actual constructors, with no extra parenthesized expression in the body,
gives:

| Index | Form / children | Initial level |
| --- | --- | --- |
| 0 | outer Lambda(q), body 1 | 1 |
| 1 | outer Block, binding loop initializer 3, final 2 | 1 |
| 2 | final `loop q`, callee 15, argument 16 | 1 |
| 3 | loop Lambda(x), body 4 | 2 |
| 4 | loop Block, direct initializer 6, helper initializer 7, final 5 | 2 |
| 5 | final `helper x`, callee 13, argument 14 | 2 |
| 6 | direct `loop x`, callee 8, argument 9 | 3 |
| 7 | helper Lambda(y), body 10 | 3 |
| 8,9 | loop Name, x Name in direct | 3 |
| 10 | helper body `loop y`, callee 11, argument 12 | 3 |
| 11,12 | loop Name, y Name in helper | 3 |
| 13,14 | helper Name, x Name in final helper call | 2 |
| 15,16 | loop Name, q Name in outer final call | 1 |

Local slots are loop=0, direct=1, helper=2. Original-Value edges are
outer→loop,Q; loop→helper,X; direct→loop,X; helper→loop,Y. There is no
loop→direct Name edge. The checking events are constructed in expression
order 2,5,6,10, whereas source admission reaches Applies in order 6,10,5,2.
Thus event order is outer-loop, loop-helper, direct-loop, helper-loop;
qualification is false,true,false,true. These orders must not be conflated.

The following is the complete **source action vector**, not a claim that all
its typed subevents have been inventoried. Action numbers are zero based.
`Pure(i,a,b)` expands to two distinct Fact actions with slots a,b and effects
Bottom≤e[i] and e[i]≤Empty. Name purity uses slots 1,2; Lambda purity 0,1.
Each `FName` is one action containing two serial effect admissions, slots 1,2.
Each `Apply` contains slot 0, then 1, then 2 after slot 0's full drain.

| Actions | Constructor event in source order |
| --- | --- |
| 0,1 | FormalEntry(q), FormalAnnotation(q): Int+≤Q≤Int− |
| 2,3 | FormalEntry(x), FormalAnnotation(x): Int+≤X≤Int− |
| 4,5; 6 | Pure(8,1,2); Link slot30 L=v[3]≤v[8] |
| 7; 8 | FName(9): t_x↔e[9]; Apply(6) |
| 9; 10 | initializer slot20 e[6]≤e[4]; Install direct boundary2 |
| 11,12 | FormalEntry(y), FormalAnnotation(y): Int+≤Y≤Int− |
| 13,14; 15 | Pure(11,1,2); Link slot30 L≤v[11] |
| 16; 17 | FName(12): t_y↔e[12]; Apply(10) |
| 18,19; 20 | Pure(7,0,1); Lambda(helper), slot4 then slot2; slot3 omitted |
| 21; 22 | initializer slot20 e[7]≤e[4]; Install helper boundary2 |
| 23,24; 25 | Pure(13,1,2); Local(helper), caller level2 |
| 26; 27 | FName(14): t_x↔e[14]; Apply(5) |
| 28 | Group/Block(4): v[5]≤v[4], then e[5]≤e[4] |
| 29,30; 31 | Pure(3,0,1); Lambda(loop), slot4 then slot2; slot3 omitted |
| 32; 33 | initializer slot20 e[3]≤e[1]; Install loop boundary1 |
| 34,35; 36 | Pure(15,1,2); Local(loop), caller level1 |
| 37; 38 | FName(16): t_q↔e[16]; Apply(2) |
| 39 | Group/Block(1): v[2]≤v[1], then e[2]≤e[1] |
| 40,41; 42 | Pure(0,0,1); Lambda(outer), slot4 then slot2; slot3 omitted |
| 43 | final definition root Link slot30 v[0]≤definition root |

For each Install, the source frame first enters `PublishLocal` without
advancing `next`; the following owner step stores the live root and boundary,
returns to Execute, clears registration and increments `next`. It does not
capture a graph. At helper Local entry the source cursor is therefore 25,
not a guessed count of constraints or a Lambda-recipe number.

## 3. Event noninterference for the helper capture

Notation: H=v[7], N=v[11], Y=parameter y, t=t_y, n=e[12], U=v[10],
B=e[10], C=the invocation row allocated by Apply(10), R=helper Lambda RE.
An extrusion copy is named by operation, original row and sign; it is never
identified with its original before the actual merge.

1. Before action 11, neither original Y nor its original entry t has an
   admitted use. Source initialization allocates t at 3, but allocation emits
   no bound. H is only an active initializer root; the body references loop,
   not helper. No earlier source action can mention H, t or n as a live
   constraint endpoint. Original row identities are fresh and never identified
   by their common Int bound.
2. Action 12 adds Y lower Int+ then upper Int−, through two successful serial
   drains. Neither bound names H,t,n. Action 16 first admits t≤n, then n≤t.
   At equal level3, `candidate_apply_effect` selects the lower owner with
   Negative polarity. The physical additions are exactly
   `EffectUpperRow(t)[0]=n` and `EffectUpperRow(n)[0]=t`.
   Neither insertion has a positive opposite bound, so neither produces a
   replay product. Let r_t be the interned relation for (t≤n,IDENTITY,None,0)
   seeded by (o[12],slot1). Its bound relation is that same r_t: ordinary
   bound construction retains the processing parent and interns the same key.
   The self Derived dependency is still a constructor event.
3. Action 17 first links the helper demand through N. L at2 receives the
   negative Function(Y+,n+,C−,U−). Its production extrusion at target2 visits
   Y+,n+,C−,U− in that order. It snapshots selected sides before source links.
   Only Y+ selects a stored atom Int+; n+ has no positive bound; C− and U−
   have no selected upper bound yet. Apply effect slots1,2 have not happened.
   The copies and source links do not mention t as an item of a *selected*
   bound: the existing n→t is negative, whereas n is copied positively.
   `Work::Bound` for selected Y/Int is authentic, but its item is an atom.
4. Qualifying intrusion redirects these four copies to their ORIGINAL parents
   in pending-parent order, preserving physical copy storage. Y's merged lower
   Int can replay only against Y's old Int−/copy-Y upper slots. These are Value
   tasks; all of their structural leaves are Int or the same Y class. n's copy
   has no selected lower storage to append, and n has no positive side to
   replay. C/U copies have no selected upper storage to append. Equality
   canonicalization cannot change t→n: both its owner and raw item are still
   their own original representatives. It therefore does not attach an extra
   canonical child to that key. No t class is merged. t stays3; n,Y,C,U become2.
5. Remaining Apply slots add e[11]≤B and C≤B; helper Lambda purity concerns
   e[7]; helper Lambda slot4 adds B≤R. These effects contain no t or n port.
   The Lambda's fresh RE uses Y's current level2. Its positive provider is
   F=Function+(Int−,t−,R+,U+). Admission F≤H at target level3 freshens no row,
   because its sole level3 structural field is t at3. This is H's first bound:
   `ValueLowerAtom(H)[0]=F`. Let r_H be its source relation seeded by
   (o[7],slot2), with key (F≤H,IDENTITY,None,0). The ordinary bound interns the
   same r_H and retains its own admission/emission record.
6. Initializer slot20 and Install do not mention H's value interface. The two
   pure helper-Name facts preceding action25 concern e[13]. Consequently, at
   helper capture the physical H interface has exactly its one F lower atom;
   t has exactly its one n upper row. Their exact attached fiber lists each
   contain the one r_H/r_t respectively. There is no same-class alias of H or
   t. Copies of n canonically name n, but their physical storage is not visited
   by traversing a shared n endpoint at boundary2.

This is a dependency slice derived from the ordered actions, not the missing
global inventory. It does not assert that the other rows have one physical
slot, one relation, one source set or an empty memo. In particular Y may have
multiple physical Int+ slots and distinct source-tagged fibers after merging.

The same action slice derives the following restricted intrusion ledger before
action25. This still leaves per-relation completion/replay history unknown.
Let d be the direct checking event and h the helper-body checking event;
their source sets are the distinct interned singletons {d} and {h}, with only
{h} qualified. Use allocation-qualified operation names o_d and o_h: numerical
operation IDs are not inferred from source action counts, because even a
no-Parent structural extrusion consumes `next_occurrence`.

| Parent-vector indices | Operation / ordered parents | Disposition before action25 |
| --- | --- | --- |
| 0,1,2 | o_d: (n_d,+,2), (C_d,−,2), (U_d,−,2) | Unqualified; copies remain distinct; original X at2 is not copied. |
| 3,4,5,6 | o_h: (Y,+,2), (n,+,2), (C,−,2), (U,−,2) | Qualified; each copy is merged into its named original, in this order. |

For o_d the selected positive n_d bound is t_x: its original first Name
constraint t_x2≤n_d3 stores `(n_d,+,t_x)`, unlike the equal-level y case.
After Function reconstruction, one authentic `Work::Bound` copies that slot
to `(copy(n_d,+),+,t_x)`. C_d/U_d have no upper bounds yet. For o_h the only
selected Work::Bound is Y's Int+ atom. No other source action before25 builds
a structured bound with an above-target child; Y-settlement descendants have
only the Int/Y value endpoints. This yields exactly these two nonempty groups.

`by_output` consequently has the two entries
`[(Value(L≤D_d),Value(D_d*))→[g_d]]` and
`[(Value(L≤D_h),Value(D_h*))→[g_h]]`, where each starred demand is the actual
Function rebuilt from that operation's raw copies. `g_d` is inactive; `g_h`
is active. Before25 no comparison revisits the direct (L,D_d) key under a
different source set: helper's original demand term is different, and its
settlement produces only Int/Y comparisons. Revisit of helper's own group
with {h} is skipped by `original.sources == Some(sources)`.
Thus no recapture reuse/activation record has been derived or needed in this
prefix, and no recapture activates g_d there. This conclusion concerns the
listed original comparison keys, not all later renamed/copied keys.

The four successful copy→original merges advance intrusion generation from0
to4; no other merge occurs in this prefix. The qualified pending vector is
[3,4,5,6], with pending_cursor4 after successful drainage. The unqualified
parents0..2 remain in `parents`, even though they never entered `pending`.
This derivation does not specify `next_occurrence`, numerical RelationIds,
or the value of every `completed[r]`: a relation admitted before these merges
can retain a completion from an older generation. Those missing per-relation
entries are precisely why generation4 plus an idle queue is not a complete cut.

All contexts reached in this fixed ordinary source are IDENTITY, and all
ScopedFlow values are default. This rederives R73's characterization against
the current context owner: only a closed Allowance source can create the local
PrefixLeft wrapper; `[io] int` entry permissions emit no cap, and Int formal
value construction creates no nested effect Allowance. No handler, operation
use, ascription or external source graph is supplied. Seed/rewrite/bound/port
constructors preserve identity; replay's two-identity fast path preserves it;
FreshUse rename/transport and equality/extrusion/ParentCopy use post-check
identity. `candidate_context_execute_relation` returns before discharge or
residual writes at identity. `context_payloads(IDENTITY)` produces no weight,
and default ScopedFlow has no latent demand. Thus context traversal adds no
extra row to this capture. This does not identify sources, providers or witness
lineages with each other.

## 4. Ordered capture and separate restoration events

On the successful-prefix slice above, `Capture` starts with H+ and expands
discovered rows in increasing graph-row order, draining its pending endpoint
stack first. Its vectors are therefore derived as follows:

| Node index | Endpoint / node | Graph row index if applicable |
| --- | --- | --- |
| 0 | H+ | 0, local |
| 1 | F+, Function children [3,4,5,6] | — |
| 2 | H− | 0 |
| 3 | Int− | — |
| 4 | t− | 3, local |
| 5 | R+ | 2, shared |
| 6 | U+ | 1, shared |
| 7 | t+ | 3 |
| 8 | n− | 4, shared |

The row vector is [H,U,R,t,n], because Function children are interned in
Argument/AE/RE/Result order and popped in reverse order. The graph-bound vector
is exactly [b_H,b_t]:

* b_H: kind Value, side Positive, nodes lower1/upper2, source key
  K_H=(H,+,F), relation r_H, evidence index0 = snapshot(K_H,Some(r_H)).
* b_t: kind Effect, side Negative, nodes lower7/upper8, source key
  K_t=(t,−,n), relation r_t, evidence index1 = snapshot(K_t,Some(r_t)).

Distinct keys make these two snapshots distinct. Each bound cursor has one
entry, so no order is inferred from a HashSet. No context views, attachment
bundles or negative Function nodes are reached. Initial metadata is generic;
the inspected source/extrusion/merge owners do not set non_generic=true.
`prepare_candidate_fresh_use` visits this row vector and allocates H' then T
at caller level2, sharing U,R,n. Its row map is [H',U,R,T,n]. One context-use
origin u_H, one identity context map and both imported immutable snapshots are
retained. Rebuilt F'=Function+(Int−,T−,R+,U+).

For b_H then b_t, the actual ordered events are:

1. `begin_candidate_fresh_bound` maps the node pair and retains orientation.
2. `candidate_context_fresh_transport_scoped` interns r'_i for the mapped pair,
   identity/default flow and the original relation's sources None; attaches it
   to K'_i; records Transport(parent=r_i,child=r'_i,use=u_H,
   witness=(K_i,K'_i,FreshUse)). This is a logical transport, with no physical
   append yet.
3. `candidate_begin_bound_restoration` invokes physical insertion. In ordinary
   mode `candidate_bound_origin_with_evidence` calls ordinary
   `candidate_context_bound`, despite the FreshUse cause. No processing parent
   survives a top-level completed source drain here; fallback source context
   and sources are identity/None. Thus its interned relation is the SAME r'_i
   in this slice. Derived(r'_i,r'_i) and the FreshUse transport remain separate
   dependency records. Exact RelationId equality does not merge witnesses.
4. Admission a'_i retains cause FreshUse(snapshot_i,u_H,K_i,Some(r'_i)).
   Physical emission m'_i names that admission and its constructor readback:
   b_H appends `ValueLowerAtom(H')[0]=F'`; b_t appends
   `EffectUpperRow(T)[0]=n`. Physical keys equal their canonical keys here.
5. Saved opposite_count is zero for each newly allocated owner: H' has no
   negative slot; T has no positive slot. The following restoration owner step
   retires that handle, then `next_bound` advances. Neither restoration starts
   a replay child. Cursor sequence is (0,None,false), (0,rest_H,false),
   (1,None,false), (1,rest_t,false), (2,None,false).
6. Only after both retire does the root link H'≤M=v[13] execute. Equal level2
   places M in `ValueUpperRow(H')[0]`. H' lower F' and upper M produce the
   ordered replay inputs (H',+,F') / (H',−,M). Their sources union is None;
   its child compares F'≤M. Structural extrusion at target2 finds every field
   already at2 or an atom, so creates no Parent/selected Work::Bound. M gains
   F' as a positive atom. The Local returns only after that drain/acknowledgement
   boundary. `step_candidate_local_use` reserves publication storage and marks
   its frame complete. Only the successful transaction commit subsequently
   calls `GraphState::commit_local_use`: it pops the completed frame, publishes
   the occurrence→route index, and moves graph, row map and retained FreshUse
   maps to `LocalFreshRoute` (scheme §§656–691; lib §§9300–9310). The cursor
   itself is discarded with the frame. Production retains terms, context/evidence
   maps and use origin; test-only capture/row observations are not runtime proof
   evidence. No pre-commit route publication is assumed.

Evidence qualification is essential: ordinary OwnerEmission admissions carry
`ProcessingAntecedentsUnavailable`, `OrdinarySeedAuthenticationUnavailable`
and `MissingAntecedent` in `Evidence::admit` (context §§714–729). The snapshots
inherit these gaps; FreshUse additionally records
`ReplayUseAntecedentsNotRetained`. The source derivation above is not a claim
that the current evidence objects are complete source-authentication
certificates. These explicit gaps are neither earliest rejection B nor evidence
of an approved-behavior bug. They remain part of any later lineage obligation.

## 5. Suffix continuation and exact uncompleted seam

Action26 adds original x Name equalities t_x↔n_f=e[14] at2. Action27 builds
D_f=Function−(X+,n_f+,C_f−,U_f−) and compares M≤D_f. M's retained F' lower
induces the authentic Function comparison F'≤D_f with the qualifying
loop→helper source. The four child pairs are, in field order:

```text
X ≤ Int−;   n_f ≤ T;   R ≤ C_f;   U ≤ U_f.
```

These express a real constructor relation, not an independently licensed
foreign consumer. `candidate_step_function_dispatch` admits Result, RE, AE,
Argument in reverse array order, enqueuing each at the front only after its
separate admission stage. The pop order of those four queued children is
Argument, AE, RE, Result, interleaved with their own generated descendants.
The full descendant/fiber/memo event sequence has NOT been enumerated here.
No reverse n≤T is inferred from the original n≤t: n was shared during capture.

One decisive descendant can nevertheless be derived without treating those
four children as a single pair. Let f be action27's checking event and h the
earlier helper-body checking event. Before Result executes, original U still
physically owns its extrusion-link lower row `copy(U,−)`. That raw item now
canonically names U. Equality canonicalization attached the exact self-bound
fiber s_h on K_s=(U,+,U), with sources {h}; the raw physical slot was preserved.
No source action before action27 Result mentions the new U_f as a bound item.
Argument descendants mention only X/Int, and AE/RE descendants are Effect tasks.
Thus U≤U_f first enters with its Function-port relation r_f, sources {f}.

This gives the following actual constructor-derived local event fragment:

| Event | Physical / relation / replay delta |
| --- | --- |
| First U≤U_f dispatch | Marks completed[r_f]=generation4; appends `ValueUpperRow(U)[0]=U_f`; attaches r_f to K_u=(U,−,U_f). |
| First opposite replay | Reads the raw lower slot, canonicalizes its item to U, and uses ordered inputs K_s / K_u. Heads are (head(s_h),head(r_f)); old heads are absent. Union sources are {f,h}; child r_fh has pair U≤U_f and a DIFFERENT RelationId from r_f. |
| r_fh dispatch | Raw typed-pair memo exists, but completed[r_fh] is absent. It marks r_fh complete at4, then appends `ValueUpperRow(U)[1]=U_f` and attaches r_fh as a new head on the SAME K_u. |
| Second opposite replay | Lower head is unchanged; upper head is now r_fh→r_f. The saved-head rule's old-lower/new-upper quadrant emits the product (s_h,r_fh), whose child interns to r_fh. Its ordered Replay dependency differs from the preceding (s_h,r_f) dependency. |
| Requeued r_fh | `pair_is_current` now sees its own completion at4 and suppresses another physical append. Acknowledgements still belong to their separate ReplayOperationIds; suppression does not erase either dependency or physical duplicate. |

Here r_f/r_fh/s_h are allocation-qualified interned relation identities;
their numerical IDs and ReplayOperationIds were not observed. The two target
slots have the same raw/canonical item U_f and owner U, and r_fh's source-set
join is independently constructor-derived. This is an ordinary propagation
fragment, **not** a later production Work::Bound or the requested independent
consumer. It demonstrates concretely why physical multiplicity and relation
completion cannot be recovered from the four Function-port endpoint pairs.
It also supplies a specific saved-head/completion fragment to reuse in the
still-open loop-Lambda/global ledger, rather than another level projection.

Action28 then joins final helper result/effect to the loop block. The loop
Lambda's provider at action31 uses Int− and original t_x, its new RE R_L and
block result V_L. Its L lower meets the two earlier stored demand families
from direct and helper. Writing D_d* and D_h* for their actual retained
negative terms (including raw copy children) gives the separate field tuples:

```text
F_L vs D_d*: X ≤ Int−;   n_d* ≤ t_x;   R_L ≤ C_d*;   V_L ≤ U_d*.
F_L vs D_h*: Y ≤ Int−;   n   ≤ t_x;   R_L ≤ C;      V_L ≤ U.
```

The physical upper-atom insertion order on L is direct then helper on the
initial successful admissions. That does NOT order all relation fibers:
`attach` prepends distinct relations, and ordinary replay omits only already
recorded dependency products using its saved heads. Generation changes can
make an earlier pair's retained completion stale. Consequently these two
tuples do not establish the complete Lambda replay schedule or its multiplicity.

Action36 must capture the live loop interface at boundary1 and restore every
resulting bound before linking its fresh root. A tempting argument that its
fresh fields all have level1 is still insufficient: retained rewrites at
`dispatch_live_item` enter `recapture_candidate_extrusion` before enqueueing
their rewritten pair. The exact key is `(original TypedPairKey, reused output
ExtrusionEndpoint)` in `by_output`; equal endpoints alone do not select a group.
`reuse_keys`, original group source sets, qualification and `pending_cursor`
then determine whether a previously unqualified group activates. This global
ledger is not replaced by the local H/t noninterference slice.

The missing state is exact and still owned by Luna's source/proof continuation:
the remaining retained `typed_pairs` (raw keys and rewrite payloads),
relation-specific `completed` generations and saved replay heads not supplied
by the local fragments above, their ReplayOperationId child/ack/retirement
state, and all other same-class physical/evidence/fiber slots. The prefix's
two-group/pending ledger is supplied above; its later recapture/reuse history
through action27/31/36 is not. In particular the analogous effect self-slot
products and both loop-Lambda demand replay families have not been reconciled
against the full prefix memo at their actual pop order.
Their first consumer is loop Lambda replay; their later consumer is action36
capture/restoration and any actual later production Work::Bound selection.
This note does not set any of these unenumerated coordinates to empty.

Accordingly A lacks an authentic later occurrence and independent consumer;
B has no established earliest constructor rejection; C lacks complete relevant
schedule/cut coverage. The fixed outcome remains **UNFINISHED/OPEN**.

## 6. Reuse, mutual TODO and finite stop receipt

Reused with provenance: R72 `/root/r72_proof` successful-prefix qualification
and first signed operation; R73 `/root/r73_astra` provider/FreshUse distinction;
R73 `/root/r73_researcher` identity-context attack. All affected claims above
were rederived at current owners. R73 remains UNREVIEWED/UNFINISHED and its
reported 302s/300s Astra overrun is preserved, with zero carryover. R53
`/root/r53_ordinary_mixed_capture_proof` supplies only applicable signed-copy
mechanics; R55 `/root/r55_original_name_attack` supplies partial-map cautions;
R70 `/root/r70_ordinary_extrusion_proof` and
`/root/r70_extrusion_countertrace`, R71 `/root/r71_raw_canonical_proof` retain
their original successful-local/fiber premises. Their 39-pin contract hashes
are the dependency manifest; none is promoted by this note.

Rejected: R73's incomplete cut as a complete state; callable Argument from
R53; raw item equality as witness identity; FreshUse as Work::Bound; an idle
queue as empty memo; the level projection as a C proof; source action order as
checking-event order. No withdrawn bypass or new source consumer law is used.

Mutual TODO `R138-GLOBAL-LEDGER-1` refines, without replacing,
`R73-CUT-LEDGER-1` / `R72-LATER-OCCURRENCE-1`: use the exact 44-action source
vector and helper capture slice to reconstruct the direct/helper retained
rewrite, fiber, generation and replay-head history; then drive both loop
Lambda replay families and boundary1 Local. Required output is an ordered
constructor ledger containing every physical duplicate and relation lineage,
followed by A/B/C evidence. Falsifier: an omitted same-class physical slot,
fiber, saved-head product or recapture key changes the claimed later schedule.

If static reconstruction cannot supply that state, the minimal **PROPOSED
provisional implementation TODO**, requiring a new Luna contract/lease, is an
inert observer of action8/17 drain boundaries, helper action25 capture and
restoration boundaries, action31 loop Lambda replay and action36 Local. It
must expose existing physical/evidence/memo/group/replay state without adding
constraints, consumers or provenance edges. Its falsifier is the first actual
constructor event contradicting this source action/capture slice or showing a
previously omitted later Work::Bound/provider consumer. Exact instrumentation
symbols are `dispatch_live_item`, `capture_candidate_graph_inner`,
`begin_candidate_fresh_bound`, `candidate_context_begin_replay`, and
`recapture_candidate_extrusion`. No code edit or observer is authorized here.

No approved-behavior violation was established: NO_SAFE_CODE_SLICE. Production
and independent-consumer correspondence remain open. Fresh review belongs to
Luna; neither author lane may certify the combined result.

Checks: read-only source/rule inspection and 39/39 live dependency SHA-256
validation. Initial `python` hash command failed because python is unavailable;
the identical hash-only operation succeeded with python3. No parser, solver,
checker/probe, tests, build, benchmark, network, Git or nested CLI ran. No
scratch path was created. Exact new paths are this note and the single leased
inbox `tasks/agent-loop/inbox/20261020-r138-proof.md`. First explicit internal
clock 2026-10-19 23:09:15 UTC; conservative budget charging starts 23:08:00 UTC.
Grant 900 active seconds, zero Astra/descendants. Final elapsed charge and
writer-cessation receipt are in the frozen inbox. Precise launch timestamp,
CPU/RSS and effective runtime model metadata remain UNKNOWN.
