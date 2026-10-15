# Named callback frames: source bridge and eligibility obstruction

Date: 2026-10-15
Status: independently reviewed constructor characterization, conditional
frame-selection derivation and source counterexample; original parent OPEN.
Review: compiler_referee found no findings in C1/C2/C3 and their declared scope.
Native baseline: `cc37db38ac48ef88ffbc68f1fbd0cab1b5a351c2` (N).
Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1` (O), frozen at
`/tmp/yulang-hygiene-audit-my68a_85/oracle`.
Lease: this new note only; other files remain untouched.

## 1. Frozen objective, quantifiers and claim classes

The selected behavior remains: ordinary id and other non-handler functions
forward every unhandled effect; wrapping the original `h i` in id preserves
its return escaping g's inner sub. The authoritative compose decision also
requires release of attributed e throughout the actual f output, including
f=id, preserving membership and independently justified protections.
These decisions neither adopt all Oracle source-shape distinctions nor make
an authenticated native formal name synonymous with an Oracle eligible call.

The original supported-source hygiene, complete Call, soundness and required
principality gates remain OPEN. This packet does not narrow those domains.
Its smaller constructor statements are:

* **C1, bounded characterization:** a successful plain named header with n>0
  parameters constructs n ordered native Lambdas and n ordered Oracle Defined
  frames from those original parameter binders; both enter the body after all
  n introductions. Nested plain named headers extend this correspondence.
* **C2, conditional derivation:** for every successfully lowered call c to an
  original unannotated formal p, suppose the actual Oracle callee is eligible
  at `tail.rs:741–798` and the active function-frame stack consists of these
  named groups. Its selected frame is the current group's terminal frame if
  p belongs to that group, otherwise p's introduced frame in an ancestor group.
* **C3, refutation:** original-formal identity and named-group facts, even
  together with current native formal-call authentication, do not establish
  the eligibility premise of C2 for all supported native named-header bodies.

All source binders below denote their original declarations, not matching
spellings, equal rows or independently chosen witness marginals. A group
G has ordered binders p(G,0)..p(G,n-1), original Lambda occurrences L(G,i),
and terminal body B(G); T(G)=L(G,n-1). Source correspondence maps original
binders to Oracle DefIds and native HirParameterIds, not their numeric equality.
FreshUse must subsequently rename the complete correlated evidence under the
same instance map; this note establishes no dynamic activation identity.

Authority: [top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–3; [compose decision](../design/2026-10-15-compose-scoped-effect-release.md)
“Scope of the operation”; [annotation integration](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§1.1; the direct user forwarding decision above. Reuse the independently
reviewed [receiver construction](2026-10-15-callback-identity-receiver-construction.md)
§§2–5 and [ownership/capture](2026-10-15-effect-scope-ownership-capture.md)
with their original hypotheses. No algebra, typed-boundary or filtering
theorem is reproved or promoted here.

## 2. Actual constructors supply the named-group evidence

N `crates/yu-hir/src/module.rs:1389–1420` creates the parameter vector from
the same admitted header parameter array passed to `local_source::form`.
Consequently the zip at `local_source.rs:387` is exhaustive at that caller.
`form:353–418` emits one Lambda per ordered original parameter, binds that
ParameterId, advances to its body slot, then schedules the original body in
the final slot. This proves the root case of C1 without reconstructing a
group from equal source keys: several Lambdas intentionally share plan.node.

For a local named header, `local_source.rs:975–1059` creates its local binder
and ordered original parameter IDs. `Work::Initializer:431–467` installs the
self binder for a nonempty header, emits those Lambdas in order, and schedules
the body in the terminal slot. Publication/restoration preserves enclosing
bindings. A zero-parameter initializer emits no Lambda: its initializer region
is not thereby a function frame. Parameter lookup keeps original binder
identity through shadowing; the required source association is the resolved
ParameterId, not a name comparison at the consumer.

The matching actual O entrypoints are module declaration lowering
`lowering/body/mod.rs:2280–2330`, `expr/mod.rs:300–337` and
`method_body.rs:55–82`, and local binding lowering
`block_local.rs:550–594,866–897`. Nonempty named headers use Defined mode
with a self value, even when the source is not recursive. Thus
`lambda.rs:644–780` pushes all n Defined frames, records each original formal's
introduced frame, and registers the active skeleton [base,base+n) before
lowering the body. `lambda.rs:852–870` wraps/pops those actual frames in reverse.
The self value supplies a static skeleton; it does not prove recursive runtime
activation or replay correctness.

Constructor induction for C1: root header establishes the ordered association;
descending through ordinary expression structure changes neither association
nor function stack; entering a nonempty nested named header appends its ordered
range; its body sees the extended lexical bindings; leaving restores the
enclosing environment/range. Zero-header local initializers retain the current
function context. Apply/Name occurrences refer to those original bindings.
This induction covers paths whose only function-frame constructors are these
named headers; explicit lambdas/for/labeled sub need their separate rules.
It is not a proof of every source resolver or arbitrary pattern form.

## 3. Frame-selection derivation, separate from eligibility

O `tail.rs:801–828` first requires p's introduced frame I. With current
Defined top frame C, it selects I exactly when an active skeleton A satisfies
I < A.base and C lies in A's frame interval; otherwise it selects C.

Let N be the innermost current named group. By C1 its top frame is T(N), and
its skeleton interval contains that frame. No proper ancestor group's interval
contains it: nested groups append frames after the ancestor's terminal frame.
There is no currently deeper named group. Hence the only active skeleton
whose interval contains C is N's. If p belongs to N, I>=N.base, so the crossing
test is false and selection is T(N). If p belongs to an active proper ancestor,
I<N.base, so N witnesses crossing and selection is exactly I. This proves C2.
It preserves the original formal index; it does not replace I by the ancestor's
terminal frame. Eligibility is still the independent premise in §4.

| Actual source context and eligible original call | Selected Oracle frame |
| --- | --- |
| `my compose f g x = f (g x)`, direct g/f calls | x frame T(compose) |
| `my g h = h 0`, direct h call | h frame, also T(g) |
| `my g h = { my step z = h z; step 0 }`, h in step | original h frame |
| `my outer h x = { my step z = h z; step x }`, h in step | original h frame, **not** x frame |
| `my g h = { my q1 = h 0; q1 }`, h in zero-header initializer | h frame; no q1 function frame |

Thus original single-formal g hides the introduced/terminal distinction. The
multiargument captured example distinguishes it without running source.
Two fresh g uses reuse the source rule but require distinct instance maps;
injective FreshUse preserves the corresponding distinction conditionally on
actual correlated transport. It does not create the source owner.

O `tail.rs:741–798` allocates/reuses a key by (selected frame, original formal),
pushes it on the actual result-effect demand and lower, and records its matching
pop in that frame. `lambda_predicate_subtracts:1058–1073` and
`lambda_output_predicate_vars:1093–1110` apply that frame's accumulated pops
to **both** entire body effect and value. C2 therefore locates the source
consumer; it does not authorize only an immediate Effect-port release.

For compose's direct calls that consumer is x's whole actual body output,
including f's actual output. For a captured earlier formal, its selected frame
may instead export a value containing a later Lambda. Partial application can
leave that output latent. Effect-only metadata cannot discharge this case's
value transport, escaping closure lifetime, or repeated/recursive activation.
The original g direct-return control has no omitted-formal call at its return
source, so this constructor introduces no callback key there. Its local
catchability still uses the established direct-return/handler premises, not C2
alone. Original for-body capture is Anonymous in O and requires the previously
reviewed active-sub case, outside this named-only induction.

## 4. Earliest obstruction: native authentication is broader than Oracle Var

Compare source bodies in the same two-parameter named group:

```yu
my direct f x = f x
my wrapped f x = ({ my unused = 0; f }) x
```

The relevant structural facts are identical up to binder renaming: the callee's
final original formal is the first parameter, its origin/current group is the
same, and the terminal frame is x. N supports the nonempty block constructor.
But O `block_local.rs:1284–1306` constructs
`Expr::Block(vec![head.stmt], Some(tail.expr))` for the wrapped callee.
O `tail.rs:845–850::local_callee_def` accepts **only Expr::Var**, so wrapped
returns the bare application-return view before frame selection. Direct f is
the actual resolved Arg Var and reaches selection. This is a source-constructor
counterexample, not an executable observation or a runtime-result theorem.

N `candidate_source.rs:1088–1104` propagates `formal_names` from a Block's final
expression even with bindings. `candidate_call.rs:469–568` authenticates that
route through Block, Group and Ascription to the original Parameter Name and
its actual Lambda registration/demand. That authenticity does **not** imply
O's separate Expr::Var premise. Neither the original-formal body attachment nor
additional group metadata changes this fact. C3 follows.

This does not show that selected semantics require native omission of protection
on the wrapped route. Ordinary forwarding is authoritative; Oracle's incidental
Var recognition cannot override it. Nor does it establish which native marker
construction is correct there. The missing premise is the source-to-introduction
rule for authenticated non-Var callee routes under the selected forwarding
semantics. Treating those routes as ineligible by fiat would change the task;
treating them as Oracle-eligible would assert a false correspondence.

## 5. Minimal retained facts and exact handoff

G1's metadata-only retention at the real root/local header constructors is
independent of the failed eligibility implication. Minimum source facts are:
original definition/local group identity and NamedHeader role; ordered original
ParameterId/Lambda occurrence pairs; terminal body occurrence; lexical containing
group association. The originating formal registration already supplies its
original identity. Consumer joins must use those typed identities, not source
key coincidence or numeric/source-name heuristics.

A useful next observational Call join retains: original formal and introducing
group, lexical group at the actual call, original group terminal facts, and
actual callee route (including the nonempty Block above). Preserve existing
native authentication/introduction and availability. It may record unavailable
classification as None; that is an observation boundary, not source rejection.
Do not label the artifact selected_frame or Oracle eligibility. Its purpose is
to expose precisely which source premise controls the construction, allowing
the next proof/effect observation to compare direct and wrapped source under
the selected unhandled-forwarding rule. No release code follows from C2 alone.

Explicit Lambda syntax has distinct owners in O: a zero-header module binding
lowers its RHS head with Defined mode (`method_body.rs:64–65`), but a zero-header
local binding uses Anonymous (`block_local.rs:873–874`). A returned Lambda in a
named header body is lowered by ordinary `lower_expr` with Anonymous mode
(`lambda.rs:877–889`, `expr/mod.rs:264–275`). Anonymous without active sub has no
selected frame; with active sub it can select the original introduced frame.
New anonymous formal origins require their own constructor correspondence.
Baseline N does not admit these explicit-Lambda/for/sub source constructors;
G1's named facts do not establish their roles or latent output activity.

Remaining owners: G1 header retention; observational Call-route join; approved
source introduction across wrappers; actual selected output's typed Effect
and latent Value transport; capture/generalization/FreshUse replay and dynamic
lifetime; handler consumption and VM execution. Current receiver attachment
is observational. Baseline N includes the typed-qualifier transport repair;
its finite helper evidence does not close these frame/eligibility premises.
Full source/runtime and native supplier closure remain OPEN.

## 6. Frozen dependencies and checks

SHA-256, N bytes read with `git show N:path`, not changing working files:

```text
yu-hir/module.rs         70678eb23bf50813f77b7be3f90442c3b3faea2c754593cf6f35d3f7c0fcf645
yu-hir/module/local_source.rs bfd2d79347d80481c5b15cc93be62006fabbcd21762a8635a1897efac3e7b51c
yu-solver/candidate_source.rs 90db34173d366ed826b34492da0fb2f1c5422b1b41e43fcda14892ec8415e7ab
yu-solver/candidate_call.rs   359566bccaa150cbe001c060475cce3d0a3e35a37a9e45d118c0f485df2e88cf
O expr/tail.rs           ac406b309fbb0ba558a18e37aba63a8e7ffeabbc377a111566b1f97d786f93b8
O expr/lambda.rs         2e0206bdcfdfbe98d13c12eec7ba8f7964383bc08c92947352ad370754024db9
O expr/block_local.rs    661386fe559d8e207a9597962cfee3c11f05f21aa2888e22b2c0143825051898
O expr/method_body.rs    3319db30fd3d6771eea156a2b902372c59db75ce1e27f64fcb44d987c3e52b74
O lowering/body/mod.rs   f5e82c2109a11938cab6a5b48d8a155f6ac3029c4d26cb7f4570790e8d5f9cb1
O expr/mod.rs            bbece8eddeba93cff358f4d14eeb9d818f4ac9170b327668457340f166e08c6b
O expr/chain.rs          e7b4c12f4abb58ad8b9c57045e61aa2aa94ba549bc0442b814417a33c16d47f6
prior receiver note     8462a7c048ff622b46d9a6486b7d0afe1abdea7589169ecfb09b9a886b73353b
```

Method/checks: syntax/constructor induction, direct source reads and dependency
hashing; no source execution, builds, tests, network or child delegation.
Requested routing: configured Sol/high prover; actual runtime model/effort
metadata unavailable. One bounded leaf, within the allocated 20-minute budget.
Fresh independent compiler_referee review found no findings: C1 is a bounded
constructor characterization, C2 is conditional, and C3 refutes unconditional
callee-eligibility correspondence. No global source/runtime closure follows.

Commit packet: only this leased path; baseline N above; dependencies pinned
above, no compiler dependency writes. Suggested checkpoint:
`research: characterize named callback frames and isolate callee eligibility gap`.
Primary/curator delta: consume C1/C2 as bounded source evidence, record C3's
refutation, keep the original parent OPEN, and assign the factual Call-route join plus its
selected-semantics introduction premise. No shared records are edited here.
