# Computation forwarding through one source-generated signed copy

Date: 2026-10-15. Status: independently reviewed bounded source/operational derivation.
Baseline: `69fc4656a6e331f43f4c938617db38a4f1585790`.
Branch: `research/simple-sub-intrusion`. Exclusive lease: this file only.
The original general H1/H2/U, complete-Call, hygiene, soundness, principality
and production gates remain OPEN. Independent review and repair closure are recorded below.

Repair provenance: an independent compiler-referee review of frozen SHA-256
`d18e6efa2a92310be93917a45207d140179ea30dca31f40b782e40403701de83`
identified a major source-correspondence error in the annotated argument port.
This one batched producer repair corrects that port and its dependent claims;
independent review of the repaired snapshot remains pending. The original
source, binders, quantifiers, bounded conclusion and exclusions below are kept.

## 1. Frozen claim and dependencies

Objective: extend the first-use admission result with one genuinely copied
source case. Method: source constructor/level trace, then the actual signed
work-stack schedule, capture, restoration and comparison consumers. This does
not reprove the isolated first-construction/first-use lemma in
[FreshUse admission](2026-10-15-computation-freshuse-admission-bridge.md) §§1–4.
Its §5 is the starting unresolved premise.

Fix the following ordinary named-local source shape, using a finite resolved
concrete formal effect set S (shown as `io`), with original distinct binders
`outer`, `k`, `forward`, `t`, `used`, and their original lexical scopes:

```text
my outer k = {
  my forward (t:[io] int) = t;
  my used = k forward;
  used
}
```

The displayed spelling is a static source construction witness, not an executed
parse/test. Named headers, local publication, parameter/local Name resolution,
blocks and Apply already have actual HIR/LocalSource constructors; this route
does not depend on the new inline-lambda parser. Assume the ordinary resolved
annotation environment for S from the preceding admission lemma. There are no
recursive or additional uses, binding annotations, assignments, prior failed
attempts, or earlier parent/copy groups involving this private construction.
These are bounds of this example, not language restrictions.

Quantify over every finite successful native construction of this source shape
and subsequent enclosing `outer` capture/FreshUse, before unrelated later
constraints change its private graph. The prior isolated local FreshUse of
`forward` at the argument Name is part of this route and is explicitly retained:
the new signed copy occurs AFTER that use, BEFORE the enclosing `outer`
FreshUse. No claim of a copy before `forward`'s first-ever FreshUse is made.
Successful completion is an execution hypothesis, not a proof of termination,
resource availability, absence of diagnostics or accepted runtime execution.
No desired bound, signed-copy map or SCC equality is supplied as a premise.

Required bounded conclusion: the actual copied positive Function P' retained
inside the actual demand on k has AE=t− and RE=r+, and one reachable physical
chain

```text
t− <= n− <= r− <= r+
```

for the SAME original `forward` provider and its SAME argument use. Enclosing
capture and ONE subsequent FreshUse map restore this chain before publication.
The copied value ports and all links used in this chain have their actual
parent and bound provenance. Subsequent Function comparison supplies the
usual scalar AE/RE implication for this actual provider when reached.

The original global conclusion is unchanged. General arbitrary copied/merged
providers, repeated recapture, contextual discharge, dynamic receipt/Force,
whole-source soundness and principality are excluded from this bounded result
and remain in their parent gates. Scalar inclusion does not establish complete
Call meaning or eventual effect execution.

Authority: top-level inference principles §§1–5, especially §1.1; the selected
ordinary forwarding decision in `notes/design/2026-10-15-callback-identity-forwarding.md`;
[forwarding preservation](2026-10-15-computation-forwarding-preservation.md)
§§6–7. Workflow: agent-orchestration “Model routing and Astra escalation” and
“Proof delegation and decomposition”; research-lab “Evidence quality and
stopping unproductive loops”; compiler-engineering “Natural compiler behavior
and proof-obligation economy”; git-concurrency “Disjoint-file mode”. Existing
authority, internal research, no semantic or implementation decision. Primary
owns verification, integration, adjudication and fresh independent review.

## 2. Source generation forces the copying occurrence

HIR `module/local_source.rs:480–532` constructs a local named function as
Lambda(s) followed by its real body, installs original parameter identities,
and publishes the local after restoring its initializer lexical scope. The
ordinary top-level named-header construction is at `:430–471`. Thus the source
above produces direct `Name(Parameter(t))` as `forward`'s body, and the later
argument resolves to `Local(forward)`; k resolves to its original Parameter.

`candidate_source.rs:651–731,782–815` starts `outer` at level 1, preserves level
through its Lambda, and visits each Block initializer at level 2. `forward`'s
Lambda, original formal registration, and direct Name body are therefore at
2; the generalization boundary of `forward` is 1. The Apply in `used` is also
at 2, whereas its callee k refers directly to the parameter row at 1.
`candidate_source.rs:912–950` distinguishes parameter Names from published
local Names; the latter routes through `Action::Local`, not an open recursive
initializer. `:983–1027` retains the actual Apply recipe and its original
checking occurrence.

Apply the preceding isolated lemma once to `forward`'s first local Name use at
level 2. Call its ONE actual map mu0. Write v for mu0 of the original parameter
value row, and t,n,r for mu0 of original formal AE, direct Name effect, and
Lambda RE. The actual argument value row a (also level 2) has positive Function
lower P=(Int−,t,r,v), and physical upper-row edges t<=n, n<=t, n<=r. The
annotation retains Int+<=v<=Int− on the parameter value row; it supplies the
Function's argument port separately. Specifically,
`candidate_formal_value_pair` returns the immutable Int+/Int− atom pair
(`candidate_effect.rs:1122`); `candidate_formal_annotation` stores its
negative term in `formal_domains` (`:1217`). Lambda construction reads that
domain for its argument (`lib.rs:11280–11282`) and takes the direct Name body's
result from the positive parameter row (`:11290–11298`). Capture/FreshUse mu0
maps that row to v while retaining the atom. Thus the two value ports are
Int− and v, with no argument occurrence of v. These facts retain the original
provider/use association; mu0 is not reselected per port.

`shadow_apply.rs:1541–1579,1631–1638` constructs the actual negative Function
demand D− on k, with argument a, actual argument-effect row, invocation-effect
row, and result row, all at Apply level 2. The typed constraint is k<=D−.
`lib.rs:12518–12529` consequently calls

```text
candidate_extrude(Value(NegativeFunction(D)), Negative, 1).
```

This is a specific source-generated `(endpoint,polarity,target)` occurrence.
A structural Function has no independent level; its row children force the
nontrivial copies. The negative Function's argument is visited positively;
a at 2 is copied to a+ at 1. Its selected positive exact lower P is then visited
positively in THAT SAME extrusion operation. `Work::Bound` installs P'<=a+;
`Work::Function` builds D' with this a+ argument, and the rewritten typed item
stores D' as an actual upper on k (`lib.rs:12534–12556`,
`candidate_extrusion.rs:838–868`). There is no inferred choice of a hypothetical
provider at this step.

Value seed context is identity (`candidate_context.rs:2864–2871`), and
`candidate_context_execute_relation:3227` returns false for it. Thus this source
constraint reaches dispatch. A scoped deferred demand is retained on Value
links; it does not make this scalar construction a consumed receiver check.
Extrusion effect links reset that Value scoped payload at their existing owner
(`candidate_context.rs:2547–2567`), rather than inventing a receiver discharge.

## 3. The native schedule creates the missing cross-polarity bridge

Use the actual operation-local key `(endpoint,polarity,target)` from
`candidate_extrusion.rs:5`. Signed row names below designate rows from this SAME
operation at target 1; a superscript/sign distinguishes polar copies, not a
second original provider. The original-to-use map remains mu0 above.

The positive Function visit schedules its four children in order
`Int−,t−,r+,v+` (`:225–258`), producing P'=(Int−,t−,r+,v+).
Int− takes the non-row, non-Function structural identity branch (`:259–260`):
it is unchanged and allocates no parent/copy pair. Row visits allocate, retain
actual signed parent records and insert one-sided source links BEFORE
selected-bound traversal (`:90–167`). In inequality orientation those links are:

| Actual copied port/closure row | Retained parent key | Physically stored source link |
| --- | --- | --- |
| t− (AE) | (t,Negative,1) | t−<=t, on t's lower side |
| r+ (RE) | (r,Positive,1) | r<=r+, on r's upper side |
| v+ (result value) | (v,Positive,1) | v<=v+, on v's upper side |
| n− (body closure) | (n,Negative,1) | n−<=n, on n's lower side |
| r− (selected body upper) | (r,Negative,1) | r−<=r, on r's lower side |

The provider's result visits v only positively; its argument atom has no signed
row key. In particular no argument-side v−, parent (v,Negative,1), source link
v−<=v, or consequent v−<=v+ is derived. t,n,r remain distinct original rows;
in particular r− and r+ are distinct keys. No row-global map is asserted.

The decisive ordering is `work.pop().or_else(|| pending_bounds.pop())` (`:77`):
all structural work finishes before deferred bounds are followed. The visit to
t− snapshots original t's selected upper n and queues it. The visit to r+
then inserts original r<=r+ BEFORE that deferred upper closure is traversed.
P' itself is reconstructed from exactly these four copied ports before the
pending closure completes; the extrusion returns only after both stacks drain.

Now consume the pending upper closure, using `Work::Visit` and `Work::Bound`:

1. The saved original t-upper n causes a negative visit of n, yielding n−,
   and physical copied bound t−<=n−.
2. n's selected uppers include original t and r. The negative t visit reuses
   t−, giving n−<=t−. The negative r visit allocates r−, giving n−<=r−.
3. Crucially, the negative visit of r snapshots its CURRENT upper side. That
   side contains the r+ link inserted during structural work. r+ is already
   at target 1, so visiting `(r+,Negative,1)` returns r+ unchanged (`:90–94`).
   `Work::Bound` therefore physically installs r−<=r+.

Thus the source-generated copied provider has
`t−<=n−<=r−<=r+`. The intermediate r−<=r+ was not present in the original
three-edge template; it is derived from the source link and scheduling. Looking
only at bounds present when the overall extrusion starts would miss it.
This is why independent marginal copies or a static snapshot of all original
bounds do not establish this bridge.

For completeness, the argument port remains the same immutable Int− atom.
The result's positive selected-bound traversal copies its original Int+ lower
unchanged and installs Int+<=v+; it does not copy v's negative Int− upper in
this visit. No cross-polarity value-row bridge is needed or asserted. Removing
the nonexistent argument-row visit leaves the structural t− then r+ order
unchanged, so r<=r+ still exists before the pending negative effect closure
snapshots r. Other outer D ports get their own signed copies; none is
substituted for these provider ports.

Each actually selected bound above is installed by `candidate_insert_copied_bound`
(`:331–346,416–434`), then `candidate_transfer_bound_origins` is called with
its ACTUAL original `BoundKey` and common extrusion reason `(operation=D−,
polarity=Negative,target=1)`. In particular r−<=r+ is transported from the
new source bound `(r,Negative,r+)`, whose emission cause is `ExtrusionLink`.
The physical copy bootstrap and exact origin transfer remain distinct.
The unchanged Int− atom emits no extrusion source link or transferred bound
origin; Int+<=v+ uses the actual selected positive value BoundKey of v.
`candidate_effect.rs:575–616` transfers executable fibers through the source
bound cursor; origin-table metadata separately retains
`MissingOriginAssociation` when that association is absent. This derivation
does not turn metadata into an executable fiber or clear such a coverage gap.
`candidate_insert_bound_with_evidence:442–620` inserts physical slots and
registers capture incidence, rather than only recording an abstract relation.
No replay is asserted solely because a copied bound was inserted.

## 4. Intrusion qualification does not supply a missing equality

The actual checking event for `k forward` has origin Local(used) and receiver
Parameter(k). `candidate_value_graph.rs:63–121,163–176` switches owner at the
local initializer and retains this exact event, not separate marginal origin
and receiver sets. Its source references are used->k, used->forward,
forward->t, and outer->used; Parameter(k) has no outgoing source references in
this isolated shape. Therefore used and k are not in one SCC
(`:208–209`), and this event does not qualify.

`retain_extrusion_parent` still retains EVERY actual signed pair above with
its occurrence/source set/comparison (`candidate_intrusion.rs:236–294`). It
adds no equality request for this unqualified occurrence. `finish_candidate_extrusion`
retains the produced group against its actual rewritten output (`:297–318`).
No later qualified reuse is assumed. The displayed chain is therefore supplied
by native bound copying, independently of an invented parent/copy equality.
General qualified reuse and merges keep their existing obligations.

## 5. Reachability, restoration, and the real comparison seam

The enclosing `outer` Function contains its original k value row as its
argument port. Capture at boundary 0 expands k's upper D', D''s positive
argument row a+, its positive Function lower P', and that provider's four ports
(`candidate_scheme.rs:499–553,604–660`). The argument port is the immutable
Int− leaf; the row ports are t−, r+ and v+. All these copied rows are at 1>0
and remain generic in this isolated history. From P''s AE=t−, outgoing upper bounds
reach n−, r− and r+ in order (`:662–706`). Thus every edge of the new chain is
reachable from ONE authentic root; inverse parent traversal is unnecessary.
Capture retains source BoundKeys, orientations, relation fibers and evidence
(`:557–602`), and reaches its closure before returning (`:803–837`).

Enclosing FreshUse uses ONE actual canonical-rows table mu1
(`:1057–1103`). It reconstructs P' as
(Int−,mu1(t−),mu1(r+),mu1(v+)): the captured Int− node remains a leaf
(`candidate_scheme.rs:474`) and reconstructs the same collected leaf term
(`:1210`), rather than entering the canonical-rows table. It restores
ALL captured edges through `begin_candidate_fresh_bound:1333–1379` and
`candidate_begin_bound_restoration` (`candidate_extrusion.rs:695–714`). Physical
insertion precedes the restoration handle. All restorations precede root
publication (`candidate_scheme.rs:1040–1054` for DefinitionUse;
`:1616–1653` for LocalUse). Hence it physically admits

```text
mu1(t−) <= mu1(n−) <= mu1(r−) <= mu1(r+).
```

The exact original-to-compared association is mu0, followed by the displayed
SIGNED occurrence, followed by mu1. There is one provider lineage and one
chosen enclosing use; this composition is not a uniform row substitution.

Restoration with no opposite bounds finishes without child work. Otherwise it
drives each selected opposite replay before advancing
(`candidate_extrusion.rs:717–802`); `candidate_context_drive_replay` with
provenance requires actual child consumption/retirement (`:3595–3611`). This
establishes completion of selected work on successful return. It does not prove
complete replay coverage for arbitrary future merged incidence.

If a later actual identity-context scalar Function comparison reaches this
reconstructed positive P' against an actual negative demand,
`lib.rs:12591–12633,12747–12782` admits its
four authentic port relations before enqueue. In particular it supplies
`e_A<=mu1(t−)` and `mu1(r+)<=e_C`. The actual Apply consumer admits
`e_C<=e_out` (`shadow_apply.rs:1652–1670`). Therefore every satisfying
interpretation of THESE actually admitted scalar constraints satisfies

```text
e_A <= mu1(t−) <= mu1(n−) <= mu1(r−) <= mu1(r+) <= e_C <= e_out.
```

The existence and full contextual disposition of every later higher-order
comparison are not inferred from the stored k upper. Nonidentity receiver
checks, protection/receipt/Force, complete Call and source-global soundness
remain separate. No claim of a successfully executed outer invocation is made.

## 6. Handoff, limits, and checks

This pass supplies a bounded copied-provider construction and its physical
capture/restoration bridge. It identifies a constructional reason for the joint
route that was absent from the preceding note: dynamic selected-bound snapshots
occur after all structural source links, including opposite-polarity ports.
No compiler repair is justified by this derivation alone.

Repair dependency audit: the annotated value-domain correction changes the
Function tuple, structural child schedule, parent table, value-bound claims
and captured/restored argument port. It removes the invented v− lineage.
The AE/Name/RE owners and their bound origins are unchanged; the required
effect chain uses only t−, n−, r− and r+. Capture follows that chain from AE,
and restoration uses the same mu1 for those rows. No effect permission,
attachment, executable fiber, receipt, receiver or discharge is supplied by
the Int− atom or by the corrected Int+<=v+ value bound. The consumer argument
relation now checks against Int−; the two scalar effect-port relations used
in §5 keep their original owners and orientation. This repair does not narrow
the bounded theorem or supply any omitted hygiene/complete-Call premise.

Proposed implementation handoff invariant, requiring broader proof before
adoption: when a Function positive RE copy is structurally visited before its
negative AE-selected closure, retain the newly generated RE source link in that
closure's subsequent snapshot and preserve its actual BoundKey provenance.
Owners are `candidate_extrude`'s work/pending ordering and snapshot sites,
`candidate_insert_copied_bound`/origin transfer, then capture and FreshUse.
A single up-front bound snapshot, interleaving pending bounds before all ports,
or dropping the selected extrusion-link origin would invalidate THIS argument.
The primary may assign focused verification/assertions at those owners; none
was added or run under this lease.

Economy audit: the parent is A/B for ordinary preservation/natural forwarding;
its D component is reconstructing a joint route from separate polar endpoint
records. Existing storage, operation-local keys and origin transfers supply
this example's route without another certificate registry or source
restriction. This is one changed source/scheduling method; no third equivalent
attempt was made. Arbitrary shared/merged histories still need the exact
constructor invariant, not another assumed-map lemma.

The producer's next action at freeze was fresh independent proof review of the derivation,
particularly the nested pending-stack order and the copied source-link evidence;
then apply its bounded result to the unchanged general parent.

Checks: read-only `rg`, `sed`, `cat`, `git rev-parse HEAD`, `git status --short`,
`git branch --show-current`, and SHA-256 capture/recheck. No tests, builds,
experiments, benchmarks, Git mutation, children or external messages. One static
pass; lightweight sequential readers/hash commands only, zero heavy processes,
zero measurement samples. Allocated bound: one static pass, at most 12 minutes;
wall-clock duration was not independently measured. Requested runtime:
`gpt-6.1-sol` / high. Observed
model/effort metadata: unknown. Prover role file omits pins; no Astra or hot
reload is claimed. Producer output is unreviewed; primary retains all closure
and verification authority. No shared task/index/theory record was edited.

### Independent review and application

M2 proof review used compiler referee `signed_copy_review`. It found one major
source-correspondence error: the annotated Function argument is the immutable
Int− domain, not the returned parameter row v. A fresh prover repaired the
actual tuples, child schedule and parent table without narrowing the source
or effect claim. Fresh referee `signed_copy_delta` found no residual findings
in the repaired ports, schedule, provenance, capture/FreshUse and scalar
comparison dependency cone; previously clean areas were carried forward.
The reviewed repaired snapshot hash was
`d88af50ad7aa7a7a83c238e545d7f26d1b2dda5544926f37cdc039c9bee3833a`.
This review/status section was added afterward by the primary.

The primary independently rechecked all 14 dependency hashes. The bounded
source-qualified signed-copy subcase now supplies the corresponding missing
premise in the first-use admission bridge §5. The general parent remains OPEN
for arbitrary shared/merged histories, later recapture and actual contextual
consumers. Its next owner is the source-qualified copying/capture construction
for those histories, preserving one provider/use association and the actual
bound provenance; the present result does not assume that remaining premise.
No compiler change or executable proof evidence is claimed.

Direct dependency SHA-256 at freeze:

```text
b0f7778934a37ec9c642f7e6232cb61e37a1b0768f6af92556cf873f6b2a69f7  crates/yu-solver/src/lib.rs
90db34173d366ed826b34492da0fb2f1c5422b1b41e43fcda14892ec8415e7ab  crates/yu-solver/src/candidate_source.rs
deee5a0892b02bc9ee23a1f2a35c76175094c558ed7dfb2cf55a7e115ac54225  crates/yu-solver/src/candidate_effect.rs
436687cbc8c4ea372d0066f3f8a8e46cfc28223ade163f49864cd3c5039c60e6  crates/yu-solver/src/candidate_scheme.rs
2c535e0906a9cf6221fa4746ae815dc45ce18cf37f19a8e811f996d8422b7f6b  crates/yu-solver/src/candidate_extrusion.rs
2158e7377686189ed90d8b8d8803dbb446368abb52b7e0cb24b2282ebe41007c  crates/yu-solver/src/candidate_intrusion.rs
9f71c8c40d6850bffccb27d7393bf6219f0ceca5cf1fe1e738073ea943706083  crates/yu-solver/src/candidate_context.rs
1a3c55abf2da669342076465c53d72aff185a9d7307374a9011d47ddd7458ef5  crates/yu-solver/src/candidate_value_graph.rs
270ee70b331e4095f404fafafdf0731b57dd451c130cdf251aea2b5944d7cc6c  crates/yu-solver/src/shadow_apply.rs
96a77474b9e63eecaf3b5be926e82af9a88d531b40fd758f6009b33ba87c4f44  crates/yu-hir/src/module/local_source.rs
09511a51539ca2a14cd7a40d2b9a5da00f72417d1ec5f97a4ba6bfd6ec20c2e1  notes/theory/2026-10-15-computation-freshuse-admission-bridge.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79  notes/theory/2026-10-15-computation-forwarding-preservation.md
c544ed3c7b83686a740aa43b1db92d901de31a3b197f81f90a4c9dbdae561134  notes/design/2026-10-15-callback-identity-forwarding.md
```

Original producer commit packet (review status at handoff, superseded above): exact leased path
`notes/theory/2026-10-15-computation-signed-copy-source-bridge.md`;
baseline `69fc4656a6e331f43f4c938617db38a4f1585790`; direct inputs unchanged
against their baseline objects at freeze. Unreviewed research checkpoint;
no closure promotion. Proposed message:
`research: derive signed computation copy bridge from native work order`.
Shared-record deltas for primary/curator: record this bounded source-generated
copy supplier and the structural-before-pending invariant; retain general
H1/H2/U/Call and arbitrary merged-provider bridge OPEN. Record fresh review only
after it actually occurs.

Repair check packet (2026-10-15): one static delta pass, allocated at most ten
minutes; no builds, tests, experiments, measurements, delegation or Git
mutation. Read-only source/authority reads, exact frozen-input SHA-256 check,
dependency hash recheck and focused textual inspection were used. Observed
HEAD at repair start was `71f649bbc1a856c6255e34decf2304edd52ed5af`;
the pinned proof baseline above is retained. Original producer metadata and
its twelve-minute allocation above describe the initial pass. This repair
requested `gpt-6.1-sol` / high; observed runtime model/effort metadata remains
unknown. The repaired artifact is frozen for fresh independent delta review;
no producer certification or parent closure is claimed. Proposed repair
checkpoint message: `research: correct annotated domain in signed-copy bridge`.
