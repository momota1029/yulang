# Compose release: finite transformations and the native entry route

Date: 2026-10-15
Status: independently reviewed algebraic derivation and bounded native constructor correspondence; original source/native theorem OPEN
Baseline: `261605657dbcd391d87b7eaa2c68b2a59349fa47`
Exclusive output: this file only
Authority: [compose decision](../design/2026-10-15-compose-scoped-effect-release.md), sections “Direct decision” and “Scope of the operation”; [directional decision](../design/2026-10-06-directional-inferred-effect-protection-addendum.md), §§2–4; [parameter roles](../design/2026-09-29-scc-intrusion-redesign-charter.md), §21; [inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md), §§1–3.
Review: fresh `compiler_referee` (`review_scope_algebra`) found no blocking or major issue. Its minor full-fact-coordinate finding was repaired by retaining `(w,T,U)` explicitly in section 3; primary checked that textual delta. No source hygiene or live replay implementation is certified.

## 1. Frozen parent statement and exclusions

The original parent concerns ordinary source generation, accumulation,
propagation, levels, extrusion, qualifying parent/copy intrusion,
generalization and fresh use for the selected source:

```text
my compose f g x = f (g x)

('a ['e] -> ['f] 'b) -> ('c -> ['e] 'a) -> 'c -> ['e?, 'f] 'b
```

Quantify over compatible source providers, their complete Call witnesses,
the original shared scoped assignment and all effect contributions actually
emitted by those providers. The five displayed type/effect variables retain
their original binders. Neither a separate assignment per port nor independent
marginal witnesses may replace that assignment. Contributions attributed to
the original `'e` component are protected while supplied to `f`. On departure
from `f`, remove that component's protection scope also from occurrences
inside the contribution represented by `'f`, including `f = id`. Preserve
membership, contribution attribution, original grants and every independent
protection scope. Required natural inference/principality is part of the parent.

This note does not prove that parent. It constructs a finite transformation
algebra and proves a scheduling property, then identifies an actual native
entry/return chain and its remaining scope-attachment premise. It does not
change complete Call meaning, assume a global row bit, introduce subtraction,
grant a handler, or use effect-family equality to select a contribution.
No new protection on every argument-effect port is licensed by the directional
rule. No unconditional argument-effect join into an application output is
introduced: an explicitly retained Computation argument may never execute.

## 2. Concrete operation, with its inputs left visible

Let `w` be one full existing typed contribution/route witness, before the
projection that existentially forgets its intermediate Flow/Observe/Receive
derivation. Its attachment, provider, receipt, residual lineage, `K,D` and
original assignment remain part of that same witness. Let `U(w)` be the finite
set of protection-scope tokens active at the observation under consideration.
A token denotes one original protection binder/instance, not a row number,
effect family, or lexical name shared by unrelated fresh instances.

For an already justified token `s`, define operations on that protection
coordinate only:

```text
Add_s(U)     = U union {s}
Release_s(U) = U minus {s}
```

These functions do not select `w`, establish attribution or supply a grant.
The input to a release operation includes the original scope reference and
the already authenticated route on which the marked output emits `w`.
Independent scopes are different tokens and remain present. Old observations
inside the receiver retain their own views; the outgoing view receives the
transformation. Mutating the source row or adding a released alternative next
to an unreleased copy at the same outgoing observation does not implement this.

The operations should compose on retained native relation contexts. The
mathematical use of full `w` specifies which existing fiber must be preserved;
it is not a proposal to enumerate or reconstruct all semantic paths.

### Finite normal form

For finite disjoint sets `A,D`, write

```text
T[A,D](U) = (U minus D) union A.
```

Identity is `T[{},{}]`; Add and Release are `T[{s},{}]` and `T[{}, {s}]`.
If edge 1 precedes edge 2 on the actual route, composition is

```text
A = (A1 minus D2) union A2
D = (D1 union D2) minus A
T[A2,D2] after T[A1,D1] = T[A,D].
```

Proof: expand the left side as
`(U minus (D1 union D2)) union (A1 minus D2) union A2`.
Every element in `A` is forced present, so deleting it from the removal set
does not change the function. All other elements retain the expanded formula.
Thus `A,D` are disjoint and the displayed equation holds for every `U`.
Associativity follows from function composition; the normal form is unique
by testing the empty set and singleton inputs. The last operation concerning
each scope wins; the form has at most one entry per scope appearing on the
route, with three states: preserve, force present, force absent.

In particular `Release_s after Add_s = T[{}, {s}]`, **not** unrestricted
identity. It equals identity only for incoming `U` without `s`. This freshness
premise must be justified at the original binder/instance owner. For `t != s`,
operations concerning `s` commute with operations concerning `t`; release of
`s` cannot remove `t`. A release followed by a later independent Add of `s`
is not simplified into the reverse order.

This bounds each route's transformer representation, not the number of
distinct route fibers or a compiler's entire resource use. Numeric equality
of transformers is no reason to identify attachments, providers or witnesses.

### Input tags and conditional introduction of a new scope

The implementation handoff additionally needs to distinguish withholding a
new output scope on input routes from removing an inherited scope. Use two
separate finite token sorts: input-route tags `T` and active protections `U`.
The following is a concrete proposed kernel, not a theorem that native source
routes already carry these tags:

```text
StampInput(u)(T,U)    = (T union {u}, U)
ProtectBody(s,u)(T,U) = (T, U union {s}) if u not in T; otherwise (T,U)
Release(s)(T,U)       = (T, U minus {s}).
```

Its normal form is a finite set `J` of added tags, and a finite map from
scope `s` to `(keep_s, B_s)`. An absent map entry means `(true,{})`.

```text
T' = T union J
s in U' iff (keep_s and s in U) or (exists u in B_s: u not in T).
```

For `first.then(second)`, with untouched coordinates supplied their identity
defaults, the complete formula is:

```text
J = J1 union J2
keep_s = keep1_s and keep2_s
B_s = (if keep2_s then B1_s else {}) union (B2_s minus J1).
```

Proof: substitute `T1=T union J1` and the first formula for `U1` into
the second. Distribute `keep2_s` over its two disjuncts. The guard from the
second transform is `exists u in B2_s: u not in (T union J1)`, which equals
`exists u in (B2_s minus J1): u not in T`. These are exactly the displayed
terms. Tag composition is ordinary union. There are no omitted cross-scope
terms: each scope's membership equation refers only to that same scope's
incoming membership and the shared input-tag set.

StampInput has `J={u}` and an empty scope map; ProtectBody has `J={}` and
the single entry `(true,{u})`; Release has `J={}` and `(false,{})` at `s`.
Sorted unique sets plus deletion of identity map entries give a canonical
form. Uniqueness is extensional over **all** finite input tag/protection
sets: `J` is determined by empty input tags. The guard set `B_s` is recovered
from inputs containing all its candidate guards except one; then `keep_s`
is recovered by taking input tags containing both candidate guard sets and
varying the incoming membership of `s`. Thus associativity follows from
function composition and uniqueness, rather than a separate rewrite heuristic.

Do not erase `B_s intersect J` from the final representation. A ProtectBody
before a StampInput of the same tag tests the **initial** tags; a StampInput
before that ProtectBody suppresses the new mark. The composition formula's
subtraction uses `J1`, not the final `J`. Do not reverse this route order
because bound discovery happened in another order.

For every injective joint renaming of the two token sorts, applying a renamed
transformer to renamed state equals renaming its original result. Union,
difference, membership, defaults and the formula above all commute with that
renaming. This proves FreshUse alpha-equivariance for this kernel, including
the scope's guard tags. It does not prove the compiler constructs that shared
renaming. Tag-set growth per transformer is bounded by its distinct StampInput
tokens; each guard set by distinct ProtectBody tags for that scope. No bound
on all distinct source fibers or recursive instances follows.

This is a constructive algebraic theorem beyond a supplied `Release_s`
predicate: it specifies the exact composition of input-route recognition and
scope change. Its operational applicability still requires authentic input
tags at their owners. A repeated static tag cannot stand for independently
nested/copied invocation instances without a separate instance theorem; sticky
tags can otherwise suppress a later body's fresh protection incorrectly.

### Exact correspondence to the frozen native kernel

The primary subsequently supplied the frozen new
[`candidate_scope.rs`](../../crates/yu-solver/src/candidate_scope.rs), SHA-256
`9fdb36b4bbd66d702fbd3fcfaf593bfbc5dce0c52ff3252442aeb998bbb52c2a`.
This is an additional implementation snapshot, not a file present in the
baseline commit. The following is source correspondence, pending independent
review; no build/test result is claimed by this producer.

| Mathematical coordinate/operation | Actual owner and correspondence |
| --- | --- |
| Scope and input token sorts | Distinct `EffectScopeId` and `InputRouteId` newtypes. |
| `J` | `ScopeTransformer.stamped`, a sorted duplicate-free vector. |
| `(keep_s,B_s)` | `ScopeEntry.keep_initial` and `AddCondition::Missing(tags)` at `scope`. `AddCondition::holds` tests whether any guard tag is missing from the original input set. |
| Identity | `ScopeTransformer::identity` uses empty vectors and thus the identity defaults. |
| Three generators | `stamp_input`, `protect_body`, `release` construct exactly the normal forms displayed above. Release retains `(false,{})`. |
| First then second | `ScopeTransformer::then` computes `keep_second`, gates `first_add`, filters `second_tags` against `self.stamped`, unions the retained guards and keeps the entry iff `!keep_initial` or its guard set is nonempty. This is the derived composition formula coordinate by coordinate. |
| Applying a transformer | `evaluate` canonicalizes input slices, unions stamps, merges scope entries with original protections, and uses `entry.add.holds(&initial_inputs)`, not the post-stamp `inputs`. It returns exactly the two normal-form equations. |
| Renaming support | `remap` evaluates each ID map once per distinct transformer-support ID, consistently reuses those images, sorts renamed sets, and rejects scope/input collisions within that support. It preserves identity omission and release tombstones. |

All constructors produce sorted distinct supports. `then` preserves these
invariants because sorted set union/difference preserves order and uniqueness;
its merge visits each scope once. `remap` sorts its injectively renamed supports
and rejects duplicates. Thus the binary searches used by these methods have
their required representation premise for every value constructible through
this private API. `evaluate` additionally canonicalizes unsorted/duplicate
input slices, so the mathematical state is their set interpretation.

The nontrivial order discriminators follow directly from the actual formulas:

```text
StampInput(u).then(ProtectBody(s,u)) : identity on U, stamps u
ProtectBody(s,u).then(StampInput(u)) : adds s iff u absent initially, stamps u
ProtectBody(s,u).then(Release(s))   : forces s absent, retains release tombstone
Release(s).then(ProtectBody(s,u))   : s present iff u absent initially
```

No identity entry may replace the third row: inherited `s` must be removed.
Withholding a new scope in the first row preserves an already inherited `s`.
These are universal deductions from the code/formula correspondence, not
executed examples or source-semantic theorems.

`remap` can enforce injectivity only within its own finite support. The
alpha-equivariance theorem for an application also requires a single
consistent injective map over the input state's relevant IDs, including
external scopes/tags not mentioned by the transformer. Mapping a fresh token
onto an unrelated external active token would violate that theorem's premise
even if `remap` locally succeeds. This is an explicit caller obligation.
Fallible allocation returns no partially constructed transformer/state;
`then`/`evaluate` borrow their inputs immutably and construct owned results.
This local fact is not whole-solver rollback or publication safety.

## 3. Late contributions and accumulated bounds

Here is the exact operational hypothesis, rather than an assumption that
storing constraints activates them. Each admitted route edge retains its
immutable transformer and its original source/dependency witness. Inserting
an edge replays all already available predecessor facts; inserting a fact
replays all already available successor edges. Their pairing is eventually
processed, or a retained continuation owns it until processing. Deduplication
does not discard different source/dependency fibers. No consumer publishes a
conclusion whose required pair or route disposition is still pending.

Under that hypothesis, apply the transformer pointwise to a set of full
facts `(w,T,U)`, preserving the original source/dependency witness `w` and
transforming the input-route tags `T` and protection scopes `U` together.
Pairing and deduplication retain `T`: equal witnesses and protection sets
with different input tags can behave differently under `ProtectBody`.
Pointwise
image preserves arbitrary unions and is monotone under fact-set inclusion,
including when the pointwise operation removes a protection token. Thus no
destructive update to accumulated facts is necessary.

**Scheduling lemma.** For any finite derivation through the admitted edges,
every fair execution of the preceding two-sided pairing rule eventually
derives its transformed fact, independently of edge/fact insertion order.
Proof is induction on derivation height. A seed is present by hypothesis.
When the final edge and all predecessor facts are present, the later insertion
of that edge/fact pair schedules the edge application. Fair completion emits
the conclusion. For a rule with several premises use the actual joint premise
tuple, not separately selected witnesses. Each conclusion remains derivable
after further insertions by union monotonicity. Conversely every emitted fact
has its seed/edge derivation by induction on emission order. Therefore the
limit equals the least closure of these specific rules.

The lemma permits cycles through their finite derivations. It proves neither
termination nor that a finite compiler has represented every required scope
instance of recursive reentry. Native bound replay, suspension and fresh-use
restoration must actually implement the pairing hypothesis for the enriched
fibers; their mere data retention is insufficient.

The outgoing observation must use the transformed view on **every** qualifying
output route. If an untransformed alias also reaches that same observation,
an existential protection query can still find its unreleased witness. A
separate `'e?` summand is therefore insufficient, exactly as the selected
compose decision states. Existing inward observations are not automatically
incidences at the outgoing handler observation.

## 4. Native source constructors: a real identity chain

At the baseline the relevant native constructors are concrete:

1. `candidate_source.rs`, `LocalSourceForm::Apply` formation, retains original
   callee/argument source expressions, occurrence, argument-effect component
   and application-effect component in `ApplySourceInput`.
2. `shadow_apply.rs::admit_candidate_fact`, Apply arm, forms the negative
   Function demand using the actual argument effect as ArgumentEffect and a
   fresh invocation row as ResultEffect. Slot 2 admits invocation effect into
   application effect. Slot 1 independently admits callee-evaluation effect.
   There is no direct argument-effect/output join here.
3. `lib.rs::admit_lambda_fact` forms fresh entry and returned effect rows for
   the unannotated Value parameter. Lambda slot 3 admits `entry <= returned`;
   slot 4 admits `body_effect <= returned`. Only slot 3 gets the exact retained
   `InferredEntryOriginId`, before endpoint canonicalization. For `id x = x`,
   Name lookup after Value rebinding is pure, so the forwarded argument effect
   uses slot 3; no special identity-function constructor is needed.
4. Native Function dispatch in `lib.rs` emits ArgumentEffect child
   `upper.ArgumentEffect <= lower.ArgumentEffect` and ResultEffect child
   `lower.ResultEffect <= upper.ResultEffect`. Those are the actual variance
   directions, not an appeal to the printed arrow's appearance.

Consequently, **whenever that actual lambda lower and Apply demand are compared**,
the emitted scalar bounds contain, with the displayed original ports,

```text
Earg <= provider.entry <= provider.returned <= invocation <= application.
```

This is an established constructor-relative chain at the pinned source; no
new type equation, solve-at-generation step or family identity is required.
It proves bound generation for that comparison. It is not complete source
reachability of every higher-order formal/FreshUse comparison, activation of
every pair, or the protection interpretation of the chain.

`candidate_call.rs::DirectionalIntroduction` retains the omitted formal,
checking occurrence/cause, complete demand and original upper ResultEffect
row. Its comment explicitly says symbolic evidence, with no handler/filter
consumer. `candidate_context.rs::candidate_function_port_admit` retains
ArgumentEffect as Swap and ResultEffect as Preserve under the actual parent.
Neither constructor currently attaches the operations of §2. The retained
`InferredEntryOrigin` likewise says it is inert construction evidence.

## 5. The extra distinction an implementation must preserve

The source directional rule marks the **original upper ResultEffect occurrence**.
It does not mark every argument effect, and explicitly withholds a blanket
provider-event theorem. A candidate realization that indiscriminately adds
the new callback scope to every concrete fact reaching that result row would
also paint argument-evaluation contributions forwarded by Lambda slot 3.
Then releasing the argument's original `E` scope leaves a newly painted `F`
scope in `compose id g`. Cancellation of an `E` pair does not fix that defect.

The minimal constructor distinction is already visible before solving: the
Value entry edge is slot 3, and the body edge is slot 4. A proposed invariant
for investigation is: realizing a newly introduced output scope treats an
actual argument-entry route separately from a provider-body emission route,
and preserves independently inherited scopes on either route. In particular,
withholding a **new** `F` on an input route must not erase an inherited `F`.
The lack of an `InferredEntryOriginId` is not a positive body certificate:
many unrelated constructors also lack that handle.

This distinction gives the following decisive constructor-relative calculation,
if its source realization is established:

```text
g's own output:            U union {E}
f actual argument entry:   U union {E}       (preserve inherited scopes)
id slot3/returned route:   U union {E}       (no new body-origin F)
marked outgoing view:     (U union {E}) minus {E} = U, if E not in U.
```

An independent token `T` in `U` survives. An independently emitted `f` body
contribution retains its own scope `F`. The same distinction is relevant to
the omitted relay: a callback's own body-emitted `signal` can carry callback
protection, while an actual direct argument computation is not given that
new protection merely by flowing through entry. This calculation proposes
neither a universal direct-argument eligibility theorem nor a rewrite of the
source rule; actual receiver, contribution and grant witnesses are required.

At the output release, select the original `E` binder and its authenticated
contribution routes. Do not remove every scope found on Earg. A joined argument
row can carry independent protections, and row canonicalization cannot choose
which one the public `'e?` refers to. Concrete sums, aliases and latent/future
uses require their actual source binder/route attachment, not a heuristic.

## 6. Generalization, intrusion and grant frame

An injective binder/instance renaming `rho` commutes with Add, Release and
normal-form composition by elementary set membership. Hence a FreshUse that
renames an output release and its corresponding input scope through one
shared `rho`, while fixing genuinely shared external scopes, preserves the
algebra. Two independent generic uses must not share a freshly bound token.
This proves alpha-equivariance, not that current capture/freshening performs it.

`candidate_scheme.rs::prepare_candidate_fresh_use` currently builds shared
row, effect-operand, context and evidence maps; `begin_candidate_fresh_bound`
retains source BoundKey, mapped relation, antecedent and `context_use` before
restoration. `candidate_context.rs::rename_fresh_contexts` renames existing
contexts. No scoped-release binder map exists in this baseline. Its addition
must use that same per-use dependency, including late restoration; copying
only already observed effects would fail §3's late-contribution lemma.
Extrusion and qualifying parent/copy intrusion may identify type endpoints;
they must not identify independent scope/route witnesses as a consequence.
The selected value-SCC qualification remains its own unchanged premise.

For the [existing filter result](../progress/2026-10-05-handler-protection-filter-derivation.md),
the operations here change only the active protection coordinate of the same
full witness. Raw incidence and original local-owner/explicit-admission facts
remain intact. Thus its `Grant? = Grant` equation applies once this actual
source-to-route attachment is supplied. Grant calculation must not discard a
released witness; a grant on that witness may override an independent surviving
protection under the ordinary rule. No handler selection or consumption follows
merely from removing a token.

## 7. Minimized obstruction and construction handoff

The first missing premise is a **joint original constructor certificate**:
for the same source Call/demand and original scope binder, identify the actual
argument-entry versus provider-body contribution route, select which original
scope the outgoing release names, and retain that association through Function
ports, bounds, replay and FreshUse to the eventual protection consumer.
The constructor-relative identity chain in §4 supplies the native scalar
ports; it does not supply this certificate's semantic interpretation.

There is also a concrete source-supplier gap reported by the primary's
complementary audit: `my relay cb = { my alias=cb; alias() }` does not obtain
the direct-formal `DirectionalIntroduction` because the callee is a local
alias rather than `Name(Parameter)`. This is a supplier incompleteness, not
a refutation of the selected source semantics. It prevents promoting a
direct-name compose construction to all higher-order source paths. The parent
source domain remains unchanged and OPEN.

Two insufficient routes have been explicitly rejected here: a blanket fresh
Protect/Release on every Apply ArgumentEffect changes the directional premise;
a release-only calculation over an indiscriminately repainted returned row
leaves the unwanted new `F` in identity forwarding. The prior conditional
filter similarly does not supply its own selector. Another equivalent filter
or pair-cancellation proof leaves this same premise untouched.

Proof-obligation-economy audit: correct attachment and activation are class A/B
because they determine actual handler hygiene and ordinary compose inference.
Recovering slot3-versus-slot4 after row merging is class D reconstruction debt:
the Lambda constructor already knows it. Preserve that local distinction at
construction, together with the actual Function/Apply parent and original
scope reference; do not infer body provenance from missing tags or endpoint
equality. The relation between that retained distinction and full source
emission/receipt remains a genuine A/B semantic bridge and cannot be retired.

One next action: implement or instrument the smallest reversible constructor
certificate at actual Apply/Function-port/Lambda-entry owners, with a consumer
that exposes the same joint association for `compose id g` and the direct
argument control. Keep the parent and production gate OPEN until its source
meaning and complete replay are independently established. No broad dependent
implementation, whole-source theorem or principality follows from this note.

## 8. Snapshot, checks and omissions

Reads: governing rules and role pins, authority documents above, prior filter,
and the named native owners. No builds, tests, executable semantic probes,
benchmarks, Git mutations or child processes were authorized or run. Static
artifact whitespace and dependency-hash checks are recorded in the producer
handoff. Normal Sol/high was requested by the packet; effective runtime
model/effort metadata is unavailable, therefore observed settings are unknown.
No delegation or Astra escalation occurred.

Omitted: general source reachability, original complete Call construction,
annotation/provider-event adequacy, nested retained computations and latent
future interfaces, recursive scope-instance coverage, replay completeness,
termination, abnormal-path publication safety, native hygiene correctness,
soundness and required principality. The normal-form/scheduling proofs are
mathematical derivations, pending fresh independent review; their source
application has the explicit premises above.

Dependency SHA-256 values at the pinned baseline:

```text
b38a175da1ee3e9998e0d9ace3559132c82aac9fea671a72fdb7410faaaaa00a  notes/design/2026-10-15-compose-scoped-effect-release.md
f11c6594e43c29fbfdbca1638b5c548cecc12a5beb192cac743e60f022c1cc73  notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md
547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed  notes/design/2026-09-29-scc-intrusion-redesign-charter.md
6301ca80eec137df3f2c2c44e2edaa7dbdf1ed7a78c69617228888e63654e461  crates/yu-solver/src/candidate_context.rs
99bae3f638656766f5f9642578a470c828b2313883d0d3aefd268f1767fd083a  crates/yu-solver/src/candidate_effect.rs
cc5778b936a5495182c08d4853ab9ef006d079df5e169dd94df629c2d82f3199  crates/yu-solver/src/candidate_call.rs
c8ef7cc472f0dcb60d793c6f9b4f6ba1aefb76f919ff2a3ce9310f85eb647dcd  crates/yu-solver/src/candidate_scheme.rs
831dc28b977a5e01e6f0ef0faa795495d78ecb2cc01678db48e9cf7ea5132eac  crates/yu-solver/src/shadow_apply.rs
e902da1c9a7f0fb4dcd806c87563d1ae46d35bbb999e69b7fee51c3c0f6e4bf5  crates/yu-solver/src/lib.rs
```
