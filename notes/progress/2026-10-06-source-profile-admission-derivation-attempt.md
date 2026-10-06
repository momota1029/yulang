# Selected source profile and initial admission: constructive derivation attempt

Date: 2026-10-06
Baseline: `393b77b64cef03e74b3f1e76adb22c2aac5c981d`
Branch inspected: `research/simple-sub-intrusion`
Status: independently compiler-referee-reviewed bounded research; derivation unclosed
Claim class: bounded source-rule inversion and conditional forward derivation
Lease: this note only; no semantic or implementation authority

## 1. Objective and result

Construct a complete original role-indexed Function profile and at least one
independently typed/admitted original invocation row for exactly

```text
my apply f = { my step x = f x; step }
```

so the reviewed conditional [SV constructor](2026-10-06-directional-source-view-instantiation-construction.md)
can be instantiated. The method is forward source derivation followed by
last-rule inversion at the first unclosed judgment. No Oracle, production
output, numerical model, or checker is used as a semantic oracle.

**Result:** the inspected rules construct the graph, parameter/result roles,
shared original formal root, original upper-use occurrence and directional
fragment. They do not yet yield the complete original profile required by SV.
A closed returning Unit identity provider removes effects, latent result
structure, recursive calls and nonreturning execution from the attempted
witness, but does not discharge that profile premise. Independently typed
initial challenge admission is a separate unclosed step even if a profile is
supplied. Consequently this note constructs no nonempty original admitted
row and asserts no source rejection, language ambiguity, or need for a new
language decision.

This is a limitation of the displayed derivation route and inspected rule
inventory. It is not an impossibility theorem for another formalization.

## 2. Baseline, exact governing sections and claim classes

The target was absent and the inspected worktree was clean at the pinned HEAD.
All substantive inputs below were read at that baseline; no producer input
depends on another worker's unfinished output.

| Input | Governing scope used |
| --- | --- |
| [Inferred call views](../design/2026-10-05-inferred-function-call-views.md) §§1.1–5 | Shared contract/slot direction; internal seed and actual role distinction; Q independence; explicit open completed formation/typing gates |
| [Callback delivery](../design/2026-10-03-callback-context-delivery.md) §§1–5 | Literal B; ordinary literal introduction; existing Pure provider retains role/entry; slot supplies its original invocation view |
| [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md) §§2–3.6 | Independently interpreted whole-tuple primitive and descriptor relations; finite emission inventory; separate admission inventory; conditional C-realization |
| [Typed core](../design/2026-10-02-typed-computation-core-elaboration.md) §§6–7 | Parameter/result skeletons; Name/Lambda/Bind/Call synthesis; complete-call/checking premises retained |
| [Nested-block addendum](../design/2026-10-06-nested-block-function-source-realization-addendum.md) §§2–4 | Exact source graph, sequential binding and same outer capture only |
| [Directional addendum](../design/2026-10-06-directional-inferred-effect-protection-addendum.md) §§1–4 | Binding user rule: protected inferred variable to upper output occurrence; no provider-lower backflow |
| [Reviewed SV](2026-10-06-directional-source-view-instantiation-construction.md) §§3–6 | Static supplier followed by actual typed receipt/prefix/result/capture; compatible complete profile and independent typed rows are inputs |
| [Source Call construction](2026-10-06-source-call-generation-construction.md) §§3–7 | Generated dependent Function root and initial address; semantic call constraints; precise original P/A cuts |
| [Joint source judgment](2026-10-06-directional-joint-source-judgment.md) §3 | Selected source registration and exposure derive the seed-at-exposure witness |
| [Typed boundary](../design/2026-10-02-typed-boundary-realization-draft.md) §6 | Original source profile is supplied to introduction; transport moves existing typed packets |

Established dependency results retain their reviewed bounded scopes. Their
reviews do not certify this note. The new argument below is author-checked
research. Candidate endpoint assignments and profile completions are labeled
as candidates; no conditional theorem is promoted to source existence.

The current task's receipt/supplier continuation fixes the precise target:
upstream complete profile, independent typed rows and initial admission. The
source meaning, directional decision, callback B, actual callable roles and
production Option A/2 are retained. No selected meaning is reopened.

## 3. Forward derivation: what can actually be produced

Fix the original source binder tree `sigma` and **one** original
`xi=(nu,K,D)`. Endpoint choices below are components of this same assignment;
they are never independently picked per port. Captured roots are imports
under the local `step` binder. No step here moves their existential scope.

The nested-block addendum supplies the source term and lexical references:

```text
T = lambda(f,
      bind(step,
        result(lambda(x,
          call(result(name f), result(name x)))),
        result(name step)))
```

The following chain is a generation derivation with retained obligations,
not a proof that those obligations have a solution.

1. Typed-core §6 ordinary parameter generation registers
   `Gamma(f)=Value(A_f)` and `Gamma(x)=Value(A_x)` before their bodies.
   Actual outer/local literals have no supplied Handler expected context or
   explicit Function annotation, so the callback introduction policy selects
   ordinary Pure introduction; entry is Value. The internal protected formal
   seed is a separate fact about `f` and does not change either actual literal.
2. Name synthesis uses the resolved outer `f` and inner `x`. Their `Result`
   computations are respectively `Comp(empty,A_f)` and `Comp(empty,A_x)`.
   The latter is the exact returning Name image `J_x`, not every computation
   with that printed interface. Lexical capture retains the same outer root.
3. The reviewed selected registration/Call construction emits one `R_f`,
   one dependent complete Function variable `F_c`, one upper occurrence
   `u:VIncl(A_f,F_c)`, `beta=(d_f,R_f)`, and the mandatory complete-invocation
   output occurrence `p0`. It retains `ElimOrigin(c,...,p0,p_out(c))` and
   `WF_Dec`, whole-argument, complete-invocation and decorated Call obligations.
   Generating those obligations is permitted before solving them.
4. Actual annotation absence supplies the selected formal seed `k`.
   Original registration and the same-root Name/Call exposure supply
   `ProtectedVarAt(k,A_f,sigma,u)`. Applying Dir-Protect yields precisely
   `delta={(k,beta,u,sigma,p0) -> Protected}`. No concrete removal grant is
   introduced and no original lower/provider occurrence acquires this mark.
5. Application synthesizes `I_c=Computation(E_c,A_c)`, with endpoints
   constrained by the complete invocation relation. The local Lambda then
   has the body/result skeleton
   `Value(F_s)`, where `F_s=Fun(Value(A_x),Comp(E_c,A_c))`.
6. Ordinary sequential binding uses the returning local closure, binds
   `step:Value(F_s)`, and the final Name returns that closure. The block
   synthesizes `Computation(E_block,F_s)` with its original Bind relation.
   The outer Lambda's body/result skeleton is
   `Value(Fun(Value(A_f),Comp(E_block,F_s)))`.

Steps 5–6 use the source roles and the exact inert closure construction.
The displayed `Fun(P,Result(I_body))` forms are the reviewed **body/result
skeletons**. They do not supply a complete Function invocation bound over
arbitrary received carriers. In particular, Value entry can expose effects
or divergence of an external carrier even when the body result is pure.
The original `K,D`, complete call constraints and providers remain active.

At this point SV §3 supplies prospective result-path schemas from the known
Value entry, but SV §4 still asks for an independently compatible original
complete profile and independently typed original invocation. It cannot be
used to discharge its own two inputs.

## 4. Smallest returning specialization attempted

Use a closed ordinary provider formed before supplying it to the callback:

```text
g = lambda(z,result(name z))
P_g = Value(Unit)
t_A = result(g)
t_S = result(Unit)
```

This is a candidate surrounding core context for the unchanged selected
source. It avoids the different direct callback-literal path: `g` is already
constructed with actual Pure role and Value entry. It is not reintroduced as
Handler when supplied through `f`.

Try the structural endpoint specialization `A_x=A_c=Unit`, and let `A_f`
describe this existing callable at the same `xi`. The provider body has
`Result(Value(Unit))=Comp(empty,Unit)`. No latent Unit effect position is
introduced by that body/result rule. `E_c=empty` and `E_block=empty` are
candidate bounds for the reached returning computations, conditional on the
complete invocation/Bind typing premises; they are not universal complete
call schemes.

Assuming those typed premises, the original execution equations reduce the
specific carriers without a Request:

```text
outer receipt;
Force(t_A) returns g; rebind f;
construct local lambda with captured f;
bind step; return step;
later step receipt;
Force(t_S) returns Unit; rebind x;
Name f returns g; construct whole Name x argument inertly;
g receipt; Force(result(Unit)); rebind z; Name z returns Unit;
return Unit from g and from step.
```

This conditional reduction explains that no Return/divergence obstacle is
responsible for this attempted witness. It does not derive typed admission
from the fact that the untyped equations return. Later `step` execution also
does not revive the expired outer receiver; no event-protection/liveness
claim is inferred from this request-free trace.

The candidate profile `Gamma_candidate={p0 -> Protected}` with no grant is
compatible with the generated fragment as a **candidate**. The next required
step is to prove it is the *complete original source profile*, including all
applicable signature positions and original contribution/path interpretation.
Neither the absence of requests nor the absence of latent result positions
proves that step. There is no asserted counterexample here: a missing proof
of completeness is not evidence that this candidate is false.

## 5. Earliest failed premise and last-rule inversion

The first unclosed profile judgment on this route is:

```text
C,d_f,c,sigma; R_f,F_c,beta,p0,ElimOrigin; NoAnnotation; seed/refined records
----------------------------------------------------------------------- P
CompleteOriginalProfile(C,beta,F_c,Gamma_original;xi)
```

Its conclusion must determine the complete applicable-position inventory,
its contribution/path interpretation, and its compatible receiving-view
interpretation while retaining lower/provider packets and original scopes.
Only `delta` is produced above. Extending `delta` arbitrarily yields a
candidate completion, not a source derivation of P.

Last-rule inspection of the named route gives:

| Possible supplier | What inversion obtains | Why P is still a premise |
| --- | --- | --- |
| Typed-core Lambda/Name/Bind/Result | Source interfaces and ordered result skeleton | These constructors do not select complete original callback positions |
| Reviewed Gen-Call-0 / Dir-Protect | One complete-call output occurrence and its tagged protection fragment | Initial slots and `delta` are explicitly distinct from `Slots_original(beta)` |
| Semantic `G_call` | Obligations including `WF_Dec`, complete carrier compatibility, `CIncl`, `TypedCallCert_Dec` | The decorated Call certificate retains supplied profile/receipt premises; solving it would not establish their source origin |
| Callback delivery §4 | An original callback slot supplies its original invocation view | It preserves/supplies that slot's profile at invocation, rather than enumerating the complete inferred profile |
| Typed-boundary §6 | Introduce from source profile, then move existing packet by typed image | Its profile and independently typed correspondences are inputs |
| SV §4 Receipt-Upper | Realized prospective and transition-indexed evidence | Its complete compatible profile and independently typed original row are inputs |
| C-realization | Correspondence after local descriptor lemmas and source/admission conformance certificate | Those independent primitives and admission premises must already be justified |

This inversion does not forbid unknown Function constraints or independent
semantic solving. It shows why a satisfying decoration, even for the Unit
identity specialization, has not been proved to be an original source row.
The earliest missing source premise is P, rather than lexical capture,
receiver naming, prospective result lift, or successful Return.

After supplying P, the independent initial-admission premise remains:

```text
original complete profile; same xi; independently typed provider/environment;
punctured caller context; whole t_A; original state/result/path/provider roots
------------------------------------------------------------------------ A0
InitialChallenge_original(beta,context,t_A,state;xi)
```

Source-contract §3.3 lists A0 separately from typed responses, original raw
resumptions and typed future uses. The list requires a source-typed initial
context; it is not a construction of that context typing from this raw source.
The latter constructors extend a supplied initial history and cannot generate
one when A0 has no derivation. No Q success, vacuous event condition, or finite
emission conformance substitutes for A0.

## 6. Independence, coverage, failures and checks

Oracle independence is complete: no Oracle semantics or executable output is
used. The conditional reduction and inversion share the explicitly selected
source equations, independent decorated primitives, and reviewed constructors.
That shared calculus is the stated premise; composing its constructors cannot
prove its remaining source primitive contracts. No checker assuming those
transitions is offered as independent validation.

Coverage is one selected raw source, one forward generation chain and one
request-free returning provider/argument specialization. There are no seeds,
random ranges, mutations, numerical searches or bounded enumeration. The
attempt omits recursive provider formation, generalized interfaces, annotation
overlap, operations, effects/requests/resumptions, opaque imports, State,
mixed uses, arbitrary latent results, all-world closure, principality, complete
source coverage and production membership/conformance. The conditional trace
does not narrow SV's admitted suspended/divergent envelope.

Failure conditions for the attempted specialization are exact: absence of a
P derivation; failure of any original descriptor, complete invocation, provider
or environment typing premise; absence of A0. Even independently checking one
ground decorated inequality would leave source origin and admission open.
No incompatible Authority-consistent semantics or minimum-cardinality
counterexample is claimed. No second equivalent toy probe is proposed.

Checks run: read-only HEAD/branch/status inspection; exact governing-section
reads; source-rule inversion and conditional equation reduction; direct-input
SHA-256 capture; output-path absence check; final note whitespace and input
hash stability check. Initial combined captures were truncated; decisive
supporting sections were reread narrowly. No absence conclusion relies on a
truncated capture. No tests, builds, source/Oracle execution, executable
experiments, child agents, interactive questions or Git mutations occurred.
One lightweight command process at a time except batched independent reads;
zero heavyweight processes. CPU, RSS and wall time were not instrumented.

Recommended next action: have the primary select a source primitive proof
supplier for P at this exact generated Function root, with its complete
applicable-position/contribution premise stated explicitly. Validate it by
source inversion/reflection before attempting A0 for the Unit identity case.
This is a proof-method handoff, not a proposed new language rule or a repeated
semantic vote. If no existing supplier closes P, report that exact unresolved
clause and pursue source-contract construction rather than another self-defined
transition checker.

## 7. Frozen dependency hashes and commit packet

SHA-256 of direct semantic inputs at freeze:

```text
4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1  inferred-function-call-views.md
df4941d4c66e4f3147257024a35e7041a2c51dd528657cc80efaf3d0db62fed5  callback-context-delivery.md
1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186  source-contracts-and-common-allowance.md
0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e  typed-computation-core-elaboration.md
750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0  nested-block-function-source-realization-addendum.md
6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7  directional-inferred-effect-protection-addendum.md
1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb  typed-boundary-realization-draft.md
462d792e518409199f77bb20a41aaa54d64898fe30363f98f0afff7ab3f805e3  directional-source-view-instantiation-construction.md
6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073  source-call-generation-construction.md
fc459dfac03693f426dea575585a0d20d7a075f8c7ac27be9fd2e67a150466c1  directional-joint-source-judgment.md
```

The first seven basenames are under `notes/design/`; the final three are
under `notes/progress/`. Task receipt hash:
`df4c4915c0934fe65df658e3992ad4c26ed2598c5e99ffbe4749372f3c4789a1`.
Policy hashes: research-lab
`ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd`;
design-authority
`9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29`;
git-concurrency
`e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e`.

Commit packet:

- Exact leased/changed path: `notes/progress/2026-10-06-source-profile-admission-derivation-attempt.md`.
- Baseline: `393b77b64cef03e74b3f1e76adb22c2aac5c981d`.
- Dependency changes: none by this producer; frozen hashes above. Primary
  rechecks any branch movement before integration.
- Review status: unreviewed frozen research; author is not an independent
  reviewer. No complete-profile/admission existence or implementation claim.
- Checks already run: narrow source/rule reads, explicit derivation/inversion,
  conditional returning reduction, dependency hash equality, lease/whitespace.
- Proposed checkpoint message: `research: isolate original profile and admission cuts in source derivation`.
- Shared-record deltas intentionally deferred to primary/curator: record that
  the request-free Unit identity attempt does not discharge P or A0; retain
  reviewed SV and every broader gate at their existing conditional status.
  No task, index, authority, theory map, question bundle or production file
  was modified.

## Independent review

A compiler referee reviewed the frozen artifact at SHA-256
`cf9971fcd4f257033272fd9a13921a91fde71c1c5475d0002ca11f98acafd7ae` against
the stated baseline and direct semantic inputs; no blocking, major or minor
finding remained. The review accepts this only as an unclosed conditional
derivation and proof-method handoff. It confirms that complete-profile
construction and independent initial admission remain separate unresolved
premises; it does not establish source acceptance, rejection, principality,
production conformance or implementation authority.
