# Annotation live-constructor invariant: native emission obstruction and one-use transport

Date: 2026-10-12
Status: frozen research checkpoint; independent review pending; original gates OPEN
Claim classes: bounded constructor refutation; constructive source-to-fresh-map derivation; proposed emission transition
Assigned baseline: `5cb4ba6f9cc8fa65d347c3b53b6d4e6e5196d02f`
Exclusive lease: this file only; constructive proof leaf, no delegation

## 1. Frozen objective, authority and quantifiers

The parent hygiene claim H retains its original successfully lowered Oracle
source domain, scopes and binders. For every such program P, every actual
composed-negative concrete annotation a in P, every actual copy/use u, and
every actual coupled Call/output route k involving a, subtraction removes only
the attached contribution. Independent contributions with the same nominal
effect survive. Symbolic connections and checks of current/future concrete
lowers remain live. Attachment, provider, Call, output and residual witnesses
belong to the same construction. H is OPEN; none of the results below replaces
its source domain by the presently admitted Y3 subset.

Authority is [annotation hygiene](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–5; [attachment/admission](../design/2026-10-10-contextual-attachment-admission-design.md)
§§3–6, especially §3.1; [residual lineage](../design/2026-10-10-contextual-residual-lineage-selection.md),
“Selected policy”; [inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5; and [complete Call](../design/2026-10-07-complete-call-contribution-definition.md)
§2. One concrete atom set at one exact annotation occurrence has one attachment
identity; members retain ordinals and resolved operands. Another occurrence or
fresh instance has another identity. Composed-positive concrete allowance is
distinct from composed-negative local subtraction. Symbolic variables are
excluded from the concrete grant set but retain their connections and later
checks. Qualifying recorded parent/copy pairs may become equal; attachments and
residual constructor lineages are not identified by that equality.

The [source-construction audit](../progress/2026-10-12-live-attachment-source-construction-bridge.md)
and [live attachment/Call proof](2026-10-12-live-attachment-call-residual-proof.md)
are frozen inputs. Their scoped reviews do not close H. The latter's §3 proves
same-key fresh-view reuse; §5 of this note establishes the same-key premise
from an actual captured graph, rather than assuming unrelated endpoint and
context copies happen to choose compatible keys. The earlier audit already
rules out a lost pre-existing live attachment in HIR.

Fix the original row input

```text
a = (annotation owner o, exact row key p, ordered concrete operands Cvec,
     original symbolic names X, lexical scope sigma, composed variance v),
C = support(Cvec),
v = root variance times (-1)^(number of Function-argument descents).
```

`Cvec` need not be deduplicated; semantic set membership and retained source
member ordinals are separate. Endpoint polarity h is another argument: it
selects the lower/upper interface side, not the annotation's authority v.
The binder coordinate for x is the native row `t(sigma,x)`; equal spelling in
another scope is not this binder. The original lexical scope is retained even
when a generic coordinate is freshened.

**Required local invariant L.** For every actual annotation formation a in the
original source obligation, its constructor and each actual local fresh use u
must jointly form, before observation or cancellation:

1. One set identity `i(a,u)` with owner o, exact p, sigma, v and members
   `(i,j,Cvec[j])`; symbolic binders retain their native coordinates.
2. The actual boundary's endpoint/constraint incidence and an executable local
   operation referencing that same i. Positive allowance does not create a
   negative grant. A negative grant has its actual local scope and a live
   attachment operation; an ID or a nominal membership test alone is insufficient.
3. Ordered context and true-receiver checks carried with that same relation.
   The local operation acts on its attached route, and does not grant/subtract
   an independent contribution solely because its nominal operand is in C.
4. Within a fresh use, endpoints, context operators, member references and
   symbolic tails use one joint rename. Other fresh uses have independent
   local attachment instances. Original owners/scopes and binders are not
   silently rebound; actual provider/output/residual joins are still needed.

L is a necessary construction invariant, not a definition of all accepted
source behavior. It does not require every ordinary constraint to be solved
when generated. Its current-source implication fails in §4. The mathematical
property of a prospective transition in §6 is explicitly separate from actual
Y3 formation and from H.

Hypotheses for the bounded code results: the exact bytes listed in §9; genuine
resolved HIR rows and valid session handles; completed fallible calls in one
live session without exhaustion; and, for §5, a graph returned by the actual
capture owner and its successfully completed fresh preparation while the
referenced view/payload records remain retained and unchanged. No all-source
admission, full capture, complete worklist drain, executable word, lawful
provider, output POP or residual construction is assumed.

Exclusions: the withdrawn callback scheme supplies no expected type; arbitrary
concrete-formal enabling, a new source restriction, a new rollback goal and
global soundness/principality/termination/F5 closure are outside this packet.
The full original obligations remain OPEN, including parameterized operands
not represented by the inspected nullary `SourceEffectId` parser.

## 2. Actual source and native constructor equations

`source_annotation.rs:68–94,505–572` forms
`SourceEffectRow {position, concrete, variables}`. Concrete spellings resolve
to one `SourceEffectId {module,declaration}`; symbolic names occupy a separate
list. This parser admits at most one symbolic name. That is a fact about the
inspected producer, not a restriction newly imposed on H.

`candidate_source.rs:274–282,317–324,413–434,479–490,649–683` carries the actual
annotation into FormalAnnotation, LocalAnnotation, Ascription or definition
Annotation actions. The source's parameter/slot/occurrence, level and scope
are action operands, not recovered from nominal effects. Preflight at 117–131
rejects composed-negative concrete rows. The paired formal constructor has an
independent negative guard at `candidate_effect.rs:1034–1070`.

For the annotation context, Function descent at
`candidate_effect.rs:1392–1444` changes `(h,v)` to `(-h,-v)` for argument Value
and Effect; result Value and Effect retain `(h,v)`. Formal root variance is
Negative (`1090`); definition/ascription paired root variance is Positive
(`1229–1251`). Consequently a negative endpoint can implement a positive
allowance; endpoint sign does not make it a negative annotation grant.

For an explicit row with `v=Positive`, the successful
`candidate_signature_effect:1447–1576` construction satisfies:

```text
t = None                               if X is empty
t = Some(annotation_effects[sigma,x])   if X = [x]
vrow = views[p]                         if already constructed in this pair
vrow = fresh_view(o,p,Cvec,t,source=(v,sigma)) otherwise

h = Positive: Support(vrow) <: fresh_port_h
h = Negative: fresh_port_h <: Allowance(vrow)
```

`candidate_formal_effect_variable:979–997` looks up `(sigma,x)` and allocates
once on a miss. The view map belongs to one annotation pair, and uses exact p.
Both interface sides therefore share its set payload even though their ports
can differ. Separate view-map invocations allocate distinct view/payload
records. No statement that arbitrary Support/Allowance endpoints have source
attachments is made: operation-owned views have none; omitted-row views can
have a zero-word payload without `AttachmentSet`.

For `v=Negative` and `Cvec` nonempty, line 1507 returns an error before concrete
view formation. For an empty concrete set it forwards the actual symbolic tail
or returns the corresponding bottom/empty leaf. This branch creates no
negative concrete payload. The earlier empty-negative bundle at 1280–1313
retains inert source provenance; it is not a nonempty attachment or operation.

For an explicit supported annotation view,
`candidate_signature_view:733–774` and `source_weight:2174–2196` give exactly

```text
i = next weights index;   vrow = next views index
Weight[i] = (left_word=[], allowed=Cvec, right_pops=[], boundary=vrow,
             owner=o, position=p,
             AttachmentSet(v,sigma,ordinals=0..len(Cvec),unit_push_marker))
View[vrow] = (owner=o,position=p,allowed=Cvec,tail=t,source_weight=i,
              closed_weight=(i if t=None else None))
unit_push_marker = present iff v=Positive and Cvec is nonempty.
```

**Constructed metadata invariant M.** The above owner/row/member/scope/variance
equations, one identity per paired row occurrence, and actual symbolic-tail
connection follow by substitution into the two constructors. Arena append
gives fresh IDs for distinct completed allocations in the retained session.
Variables are never inserted into `allowed` or the ordinal list. This proves
M for these successful source constructions, not L and not arbitrary negative
source admission. `source_weight` copies operands and ordinals in O(|Cvec|)
work and space, apart from ID/owner cloning and existing arena bookkeeping.

## 3. Actual operations, checks and nominal comparison

`candidate_context_source:2483–2501` consults the actual upper Allowance:

```text
seed(lower,Allowance(vrow)) = PrefixLeft(i,Identity) if tail(vrow)=None
seed(other pairs)          = Identity
```

This is an executable **zero-word filter** for a closed Allowance.
`candidate_zero_word_filters:2613–2735` validates the payload/view association
and rejects nonempty left/right words before returning its filters.
`candidate_context_execute_relation:2744–2814` checks or registers the
Allowance on the actual task's lower endpoint, replays an existing bound where
needed, then records discharge. The retained Allowance bound and relation
origin distinguish check execution from mere metadata. This is real local
checking; claiming no annotation operation whatsoever would be false.

Open-tail views have `source_weight=i` but no `closed_weight`, so this seeding
does not produce a PrefixLeft operation for them. They retain the native
Support/Allowance atom path instead. `candidate_check_effect_operand:888–958`
implements

```text
Support(vrow) <: U  ==>  enqueue AnnotationMember(vrow,j) <: U, for all j,
                        and actual tail <: U when present.
concrete c <: Allowance(vrow):
    effect(c) in C  ==> success
    effect(c) notin C and t exists ==> enqueue the SAME c <: t
    otherwise      ==> mismatch.
```

The second rule does not replace c by its nominal identity, and variable
forwarding does not extend the concrete grant set. It nevertheless tests only
the resolved effect for success. For distinct concrete contributions c and d
with `effect(c)=effect(d)=E`, this Allowance branch returns the same success
when E is in C, irrespective of their distinct instance/origin records.
Thus success of that branch is allowance evidence, not evidence of which
attachment may be removed. Reinterpreting it as support subtraction would
lose the exact distinction required by L. The code makes no such subtraction
claim; this is an inversion obstruction, not a reported compiler bug.

Function children at `candidate_function_port_admit:2557–2608` use the actual
parent post-check context. Argument fields use Swap; result fields preserve;
child-local zero filters prefix that operation. This transports an operation
already supplied by the parent and creates no missing source word.

## 4. Refutation of the current constructor-to-live-attachment implication

Consider the claimed operational implication

```text
genuine resolved explicit source row a
  -> candidate_signature_effect -> candidate_signature_view/source_weight
  -> jointly indexed executable attachment operation required by L.
```

It is not an established theorem of the pinned implementation. The following
are two distinct bounded findings, without assuming any source execution
result:

1. A composed-negative nonempty C meets the direct guard before
   `candidate_signature_view`. The missing source-formation conclusion cannot
   be obtained by quantifying only over the already successful negative views;
   their nonempty domain is empty in this cone. This does not refute H or make
   those ordinary source programs invalid language inputs.
2. Separately, on the successful concrete view branch,
   `LocalWeight.left_word` and `right_pops` have Rust types `[();0]`
   (`candidate_context.rs:115–123`).
   The constructor equations in §2 therefore force both to be empty for every
   payload it returns, including a payload with `SourceUnitPush`. The actual
   executor in §3 only consumes the zero-word filter fragment. The private
   `materialize_unit_push:2200–2215` returns a `DetachedWeight` and installs no
   ContextExpr, relation, bound, registration or live word. Its detached result
   is not a live word. This establishes representational absence of nonempty
   words in the inspected implementation; it does **not** independently refute
   L for the successful positive-view branch, whose executable closed allowance
   is established in §3. The actual negative-constructor obstruction to L is
   §4(1).

This is a bounded static refutation of a purported **current-source bridge**,
not a source-qualified counterexample to semantic hygiene. The first absent
premise at the requested seam is precise:

> The annotation boundary owner emits an actual local operation referencing
> its freshly allocated set identity on its actual native relation, with a
> consuming operation path and the retained true-receiver check. Its emitted
> contribution and symbolic tail remain the actual source route's operands.

Raw occurrence/owner/member/binder data already exist; no inverse annotation
reconstruction theorem is needed. For negative concrete rows, their operative
paired constructor is earlier still absent behind the guard. Removing that
guard alone proves neither emission nor safe concrete-formal admission.

## 5. One actual fresh use: the source of the shared key

This section proves a narrower positive result from actual capture owners.
It does not assume a live word. Fix a retained source view vrow with payload i,
and an actual completed `capture_candidate_graph_inner` producing G. Consider
every captured endpoint occurrence of this view and, if reachable from retained
bound contexts, its captured context-payload occurrence. Then every one of
these occurrences obtains the same copied view and payload during one
successfully completed `prepare_candidate_fresh_use(G,u)`.

**Derivation of the common tail.** At `candidate_scheme.rs:445–456`, every
AnnotationMember/Support/Allowance endpoint for vrow reads this view's actual
tail t and interns it, using the endpoint's appropriate polarity. At 767–780,
context discovery reads the same `View[vrow].tail`; `payload_seen` retains at
most one `(i,vrow,tail-node)` record. The positive/negative tail nodes can have
different node indices, but `Capture::row:301–332` assigns the same canonical
`RowKey::Effect(t)` one graph-row index, independently of endpoint polarity.
Consequently all those tail nodes are `Node::Row` pointing to that same
graph-row index. For a closed view all have tail None.

Fresh row preparation at 1008–1020 obtains one mapped coordinate per canonical
source row. A generic row is freshly allocated at the use level; a nongeneric
row remains its existing representative. Canonical equality between captured
row records is handled by this same `canonical_rows` map, not by independent
fresh witnesses. Therefore endpoint loops at 1047–1071 and payload loops at
1089–1107 all compute exactly the same mapped tail `t_u` and invoke

```text
view_remap[(vrow,t_u)] = vrow_u
weight_remap[i]       = View[vrow_u].source_weight = i_u.
```

The existing same-key lemma now applies with its premise formed by capture,
rather than assumed separately. Copy at `candidate_effect.rs:806–830`
validates i against vrow, copies o,p,Cvec,v,sigma, and reruns the source view
allocator with `t_u`. Map lookup at 832–847 returns that one copy to every
endpoint and context reference. The copied payload's ordinals are recomputed
as the same `0..len(Cvec)`; concrete operands and lexical metadata are unchanged.
Two distinct original views remain distinct even when their mapped tails
become equal: the map key still contains the original vrow. Distinct successful
fresh-use invocations use distinct view maps and allocate distinct payload IDs
for these source views. Nongeneric tail sharing does not share local authority.

Context reconstruction at `candidate_context.rs:1266–1379` then satisfies
constructor equations, with one shared context map:

```text
R_u(Identity)                 = Identity
R_u(PrefixLeft(i,c))          = PrefixLeft(i_u,R_u(c))
R_u(SuffixRightPops(c,i))      = SuffixRightPops(R_u(c),i_u)
R_u(Swap(c))                  = Swap(R_u(c))
R_u(Replay(c,d))              = Replay(R_u(c),R_u(d))
R_u(WithoutLeftFilter(c))     = WithoutLeftFilter(R_u(c)).
```

Each child is older than its parent; induction on that constructor DAG proves
these equations, preserves Replay order and shared children, and returns the
same copied token for every reference to i. At
`candidate_scheme.rs:1221–1267`, fresh bound reconstruction passes the actual
endpoint terms and this use's context root to
`candidate_context_fresh_transport`; that transport records the source-bound
key and mapped relation. `candidate_begin_bound_restoration` then receives the
original bound evidence and source-bound provenance for restoration. This is
a source-to-transport bridge for the captured graph, not an arbitrary renaming
assumed to be well formed.

Limits are essential. Context discovery only visits post-check contexts of
the bounds actually captured. It rejects `BothFromRight` at
`candidate_context.rs:1413`; no correlated-both transport is proved. An
operation-owned view without a source payload supplies no attachment
conclusion. M transports jointly on this actual captured cone. L does not:
copy reruns the empty-word constructor, so the missing operation remains
missing. Capturing/renaming an undiscovered or unformed local obligation is
not implied by these equations.

Cost: view/payload copying is O(sum of copied member-list lengths); tail/key
lookup and context-map lookup use the existing hash maps. Expected work for
this inspected capture/rename cone is linear in visited graph rows, operand
occurrences, context nodes/edges and copied member lengths, with matching
space. This assumes ordinary hash-table behavior; no worst-case hashing,
allocation or whole-solver bound is claimed. Shared contexts are renamed once
per source node, and `payload_seen` prevents duplicate payload discovery.

## 6. Constructive minimal transition at the owning seam

**Class: proposed native emission transition; not implemented and not proof
that a source constructor executes it.** The missing premise should be supplied
where a already owns all inputs, rather than by reconstructing an attachment
from row equality at Call or residual elimination. A minimal retained output is

```text
Form(a,h,actual_boundary_relation r):
  allocate/reuse i and vrow by the exact per-occurrence map;
  retain M together with r's actual endpoints and source origin;
  retain an executable boundary word under i on r's ordered context;
  retain/register the actual Allowance(vrow) check on r's true receiver;
  return the same i and operation to the owning local continuation.
```

An explicit constructional instance of the word part is

```text
W_i = (left=[PUSH(i,C)], allowance=(C,t), right=[])
c_r = PrefixLeft(W_i,c_parent)
r'  = Relation(component,actual_lower,actual_upper,c_r,actual_source_origin).
```

`PUSH(i,C)` is a typed context instruction under the set identity, not a
fresh effect variable, nominal support deletion, or a pre-solved constraint.
The closed case's allowance is C; the open case retains `(C,t)`. A variable
does not become a member of C. This is the smallest concrete extension of the
existing dormant unit-PUSH preparation that emits a word **and** installs it
on the native relation. It requires a live instruction consumer: changing the
payload array type or calling the detached adapter alone is insufficient.
Existing zero-word execution cannot consume `W_i` and would reject it.

The receiving constructor must retain the appropriate written-boundary
operation order and check before any equality/memo omission, as required by
attachment/admission §4. The symbol `r` above is the actual source-emitted
boundary constraint; choosing an arbitrary equal-endpoint relation later is
not a permitted instance. Composed-positive construction returns no negative
grant. Where the approved composed-negative constructor supplies local
subtraction, its local continuation must retain the corresponding same-i
instruction, scope and consumer incidence. This note does not select an output
POP count, assign all descendant Function predicates to an enclosing Call, or
claim those consumer inputs are already formed.

**Immediate preservation proof for this proposed transition.** The fresh
allocation plus copied source inputs supplies M. PrefixLeft references exactly
that i and the existing parent c; r' retains the actual r endpoints/origin.
No symbolic coordinate is created, deleted or replaced: Support/Allowance
continue to use the same t. A different attachment j remains j in all retained
instructions, even when its operands include E in C. Thus immediate source
formation does not identify unrelated attachments, create a negative grant
from a positive allowance, or drop symbolic flow. These conclusions follow
by constructor substitution, not nominal equality or a checker supplied with
the desired transitions.

The **local algebraic frame**, if a later actual instruction cancels a matching
PUSH/POP under i, updates only the i entry; the j entry for `j!=i` is unchanged.
This is a statement about indexed operation normalization, not about complete
output support. It does not show that every independent source contribution
has a distinct attached route, that the correct POP is emitted, that residual
head subtraction obeys that frame, or that a surviving entry reaches the final
output. In particular, equal-E Allowance success in §3 proves none of them.
Those are exactly the remaining conjuncts of L/H, rather than assumed
consequences of this proposed state transition.

**One-use extension equation.** If the owning constructor actually emits the
above word into the captured context graph, then the same source-derived maps
of §5 must satisfy

```text
R_u(PUSH(i,C)) = PUSH(i_u,C)
R_u(t)        = t_u
R_u(c_r)      = PrefixLeft(W_i_u,R_u(c_parent)).
```

This is the required implementation correspondence equation for the proposed
new instruction. It is conditional: current copying rebuilds only empty
words, so it does not establish that equation for a future live instruction.
No new source restriction or generic-admission permission follows from it.
Immediate emitter work is O(|Cvec|) plus one native context/relation insertion;
retaining the original context as a child avoids copying its entire tree.
Receiver registration/replay and recursive admission costs belong to their
actual consumers and are not bounded by that local cost.

## 7. Complete Call, output and residual join still absent

`shadow_apply.rs:1312–1397` validates actual Apply/source-input incidence and
forms the native four-port demand. At 1425–1444 it forwards both callee
evaluation and invocation effects to the actual application effect. That
incidence is useful native evidence, but contains no source i or local
subtraction predicate. Complete Call §2 additionally requires the whole
argument, actual returned provider/current entry, return/future interface and
every independent alternative with its original evidence. A four-port demand
cannot supply those by itself.

For the enclosing output, a genuine owner must connect the same annotation
instance and actual Call binder/route to both actual output components and
their local operations. The [Oracle transfer audit](../progress/2026-10-12-oracle-effect-source-transfer-audit.md)
§3 shows a bounded direct-formal implementation pairing with separately stated
wildcard/admission hypotheses; it is historical source evidence, not a Y3
all-source supplier. Its one direct pairing does not set a universal POP count
or a descendant-predicate rule. Direct formal names and local aliases remain
different actual source routes; §5 only supplies the alias's captured-map join.

Each actual residual constructor must create its own lineage ell and gamma,
retain the exact source/heads/context, and supply BOTH obligations

```text
source <: retained_heads union gamma_ell     live feedback
gamma_ell <: each exact original tail        lineage-owned projection.
```

Applicable current/future source lowers must reach every retained recipe,
including after qualifying parent/copy equality. Gamma upper feedback,
Function swap/result/both correlations, actual provider identity and
contribution/output survival must remain in that same derivation. The current
`discharge_residuals` map is only the post-filter ContextId at relation discharge;
its name supplies none of these concrete residual constructors.

No marginal attachment, provider, output or residual witness can be chosen
independently to repair the absent conjunction. Source reachability, consumer
activation, complete replay, ordinary inference, H, soundness, required
principality, mixed-component termination and production/F5 gates remain OPEN.

## 8. Economy audit and one next action

The prior negative-constructor and coupled-carrier attempts already reach this
emission premise. This packet supplies a source-derived common-tail premise
for one captured fresh use, but does not count that fact as progress on the
absent source operation. It stops before another equivalent cancellation or
empty-word proof can be called parent closure.

Under [proof-obligation economy](../../rules/compiler-engineering.md), source
hygiene and natural annotation inference are A/B. Reconstructing original row,
scope, binder or identity from equal nominal endpoints would be D debt: the
annotation constructor has those inputs. Retaining the source operation and
its actual native relation is the constructional remedy supported by the
approved internal carrier; it does not change semantics or retire the parent.
All-view characterizations remain separate C research where applicable.

One next action: the primary assigns a bounded, provisional constructor/consumer
packet at this exact source seam, using §6's retained incidence and operation
equations as its decisive invariant, before dependent negative-formal enabling.
Its frozen source evidence must then return to the constructive and fresh
independent review lanes. No compiler implementation is authorized by this note.

## 9. Checks, resources, routing and dependency freeze

Static inspection only: bounded `cat`, `sed -n`, `rg -n` and read-only hash/link/
whitespace inspection. Two initial read-only Git commands (`status --short` and
`rev-parse HEAD`) confirmed the visible baseline; no Git mutation occurred.
The packet's stricter no-Git instruction was followed after those reads; final
baseline/dependency integration validation remains primary-owned. An initial
glob search for nonexistent `candidate_signature*` returned exit 2; the actual
owner was inspected in `candidate_effect.rs`. Some combined output was
truncated; the decisive rules and source windows were reread separately.

No tests, builds, execution probes, Oracle execution, benchmark samples, shared
record edits, question consumption, external contact or delegation occurred.
At most five tiny static read commands were submitted concurrently; later
source reads were bounded. No heavyweight process ran. CPU/RSS and elapsed
wall time were not instrumented. Primary retains verification ownership; this
leaf's output is frozen at handoff and is not independently certified.

Requested assignment: constructive `prover`, normal GPT-6.1 Sol/high according
to the primary's normal role policy. The callable schema exposes `prover`;
`.codex/config.toml` registers it and sets Sol/high subagent defaults;
`.codex/agents/prover.toml` omits model/effort pins. Observed identity is
`/root/annotation_live_constructor_proof`; effective runtime model/effort are
unknown. No Astra override or hot reload is claimed. No reviewer was launched
by this leaf.

The following fingerprints are of the exact retained working bytes read.
Dependency hashes did not change during the final freeze inspection; none of
these dependencies was written. Source-byte equality with the pinned commit
must be revalidated by the primary before integration.

```text
a348a47530e57c2b3475a4c0d9f020e24ba04ea58a06292847892640567e61cb  crates/yu-hir/src/module/source_annotation.rs
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49  crates/yu-solver/src/candidate_source.rs
ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df  crates/yu-solver/src/candidate_effect.rs
4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987  crates/yu-solver/src/candidate_context.rs
9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1  crates/yu-solver/src/candidate_scheme.rs
fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0  crates/yu-solver/src/candidate_extrusion.rs
cbd2e0c49a3f1fbe3c5fc78a06d469faedf4aa261525b24a0c9584e9956c2411  crates/yu-solver/src/shadow_apply.rs
503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a  notes/design/2026-10-10-annotation-effect-hygiene-integration.md
717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc  notes/design/2026-10-10-contextual-attachment-admission-design.md
d5c46b74d678028046bdfa0f7fd2b71bb2abfb112987000fe43e0fa5875d5d98  notes/design/2026-10-10-contextual-residual-lineage-selection.md
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389  notes/design/2026-10-11-yulang-inference-top-level-principles.md
4c83a095dce3636ada842bfc32c18cf0ef598db0e361861fb8e659745b74411e  notes/design/2026-10-07-complete-call-contribution-definition.md
6235b6d777b4e85a3ee5121ce2eaa356ac52a771564c43907f4fe00684a1ac67  notes/progress/2026-10-12-live-attachment-source-construction-bridge.md
efafd2a067a2b7db708f85237eb0ac377398c1aa042dc67772622acd87ddf27a  notes/theory/2026-10-12-live-attachment-call-residual-proof.md
f222d83d51af22f26b786bad6bc07d27a2b2fb5b97e0dadbada9159d667bbb32  notes/progress/2026-10-12-oracle-effect-source-transfer-audit.md
9b17e2b4116ff265e0a218daf799e01d8a76f61de2a8e7fa17be869b991b459d  rules/agent-orchestration.md
3f70daf755fd6af59959fa48a35aa2d5153639621cc18edc58934246f2aabb69  rules/research-lab.md
e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1  rules/design-authority.md
4567cc0f6997c116114cba3322563cb0ddbe5c73ab3403e5272f0e638cb73ed9  rules/compiler-engineering.md
2561a7168ba8b2d655cc928c8adac565755ec7e3b6b4175e8ac87be4bcdaa5e6  rules/git-concurrency.md
dae388e4e811c346727ec6688472c7fcf6341ddc5466168cfaa03fdcc0b8e17a  .codex/config.toml
485a26c7409e16c692ad10095031ab0e7084726ec5da5666082b3bbc4a5daf98  .codex/agents/prover.toml
```

## Commit packet

- Exact frozen lease: `notes/theory/2026-10-12-annotation-live-constructor-invariant-proof.md`.
- Baseline: `5cb4ba6f9cc8fa65d347c3b53b6d4e6e5196d02f`.
- Changed dependency hashes: none written; exact read fingerprints above.
- Claim/review: bounded native constructor refutation and captured-source
  common-tail/fresh-map derivation; proposed emission transition only;
  independent review pending; L/H and complete Call remain OPEN.
- Checks already run: static owning-constructor/consumer reads and final
  dependency/link/whitespace inspection. No executable verification.
- Proposed one-line message: `research: derive annotation fresh-use incidence and isolate live emission premise`.
- Shared-record deltas left for primary/curator: record the actual-capture
  common-tail premise for joint payload/view transport; retain the same OPEN
  live source-operation/true-receiver/output/residual gate; distinguish the
  existing executable closed zero-word allowance from missing attachment
  words. No shared task, theory-status, index, design or question file changed.
