# CALL_TYPE typed-core producer / successor shadow correspondence

Date: 2026-10-08 (assignment date)
Baseline: `fd6434993f02d85221642ab2c4047eb63798f9ca`
Status: frozen research-only audit; compiler-referee reviewed, no findings
Claim class: bounded source/code correspondence and conditional structural derivation
Exclusive lease: this note only
Authority: no semantic selection, production implementation or gate closure

## Objective and dependencies

Audit the typed-core **producer** of the complete Call, rather than an Oracle
lowering or another endpoint/Use inventory. Determine whether the retained
successor carriers lose a concrete source coordinate needed to construct its
callee prefix, actual receiver invocation and pending suffix.

Governing sections: typed computation core §§3, 6–9; source contracts
§§2.1–2.2, 3.2–3.5; Authoritative inferred Function call views §§2, 5;
Authoritative exact nested-block addendum §§1–3; canonical DAG nodes
`CALL_REL`, `CALL_TYPE`, `ORIGINAL_ASSOC`. Typed core remains Draft. Source
contracts supply conditional results requiring independent local typing
lemmas, rather than adopted exhaustive semantic clauses. Call-view authority
fixes formation direction while leaving the concrete rules open.

Accepted decisions remain premises: source tags select Normalize; the whole
argument is delayed inertly; the actual provider owns role and entry;
receipt precedes entry execution; a consumer executes its designated layer;
raw resumption uses current state and keeps the ordered suffix. The exact
approved block sequentially binds and returns `step`, capturing outer `f`.
Source annotation, inferred public type and internal evidence remain distinct.
Neither Q success, solved shape nor Oracle output creates these facts.

Previously closed structural joins are used as dependencies, not attacked
again: the Apply endpoint crosswalk and local-binding source-identity slice.
The computed-callee/retained-entry attempt supplies the known semantic stop.
This audit adds correspondence of the full producer template to the actual
retained operands; it does not re-prove those joins or repeat its operational
branch probe.

## Hypotheses and exact claim

For the structural derivation below distinguish:

- `H_ret`: one validated, immutable retained ordinary source skeleton and
  its same-artifact raw arena; each referenced source node is present.
- `H_src`: the original lexical/declaration interfaces, source tags and
  designated ports required by typed-core §6, at one fixed original `X`,
  binder tree and `xi=(nu,K,D)`; actual callable producers remain attached
  to their own source definitions. These are supplied semantic premises.
- `H_rel`: the existing §3/§9 Call, Delay, receipt, entry, consumer and Bind
  equations, including original delimiters and current resumed state.
- `H_joint`: independently justified descriptor/carrier/provider/world and
  history interpretation required by `SEM_JOINT`. This audit does not supply it.

**Bounded finding:** in the inspected retained ordinary Apply routes, no
new loss of an already retained source operand, declaration, binding or
capture coordinate is needed to explain the missing complete Call typing.
Given `H_ret`, `H_src` and `H_rel`, the complete static template can reference
the existing callee and argument subgraphs and provider definitions without
recovering erased source structure. This is conditional template construction,
not a claim that current code constructs that template or encodes its semantic
witnesses. `H_joint`, constructor typing and original association do not follow.

The scope is deliberately narrower than full typed-core coverage. Current
raw `Form` supports Lambda, Bind, Use, IntegerLiteral, Group and Apply;
Operation, Reify, Eliminate and Handle are not general raw constructors in
this carrier. Their full source producers have not been implemented or
audited here. Absence of such support is not evidence that an existing
operation delimiter/consumer was discarded during the inspected projection.
No repository-wide absence or complete carrier-sufficiency theorem is claimed.

## Producer partitions and current carriers

Typed-core §§3/6 normalize operands before the §3 Call construction:

```text
n_f = Normalize(I_f,d_f); n_a = Normalize(I_a,d_a)
S_f(actual_f,C) = let t = Delay(X[n_a],original lexical references) in
                   ExecuteCallable(actual_f,t,C;original complete view)
J_whole = X[n_f] >>= S_f
```

This is a semantic template, not an interpretation of the eight bookkeeping
labels as typed ports. `J_call` is the actual receiver's complete invocation,
parameterized by `J_arg`; a closure's `J_body` is its body/result skeleton.
They are separate from `J_whole` and the callee computation.

| Required producer partition | Existing structural locator/carrier | Still required semantic premise |
| --- | --- | --- |
| Callee normalization and prefix | `Form::Apply.callee`, `PendingStructuralForm::PendingApply.callee`, retained child subgraph; solver callee occurrence | Original `Gamma`, `I_f`, designated consumer and independently typed callee computation |
| Whole-argument Delay after callee Return | Separate Apply argument edge and complete retained argument subgraph; lexical binders/capture references | Normalize by `I_a`; inert Delay membership at its original carrier/provider view |
| Actual callable and receiver activation | Call's retained callee source identity and optional declaration/capture joins; provider definition is an input for unknown formal `f` | Actual callable membership, role/entry, current world, source receiver/boundaries and complete view |
| Receipt | Apply, whole argument and original binder references remain distinct | Typed path/Flow, actual receipt relation, owner/profile incidences; a static label is not a receipt |
| Value entry and result rebind | Actual callable's parameter/body references and argument subgraph remain available | One designated Force, result/world preservation, typed rebind before body; latent result introduces no extra Force |
| Retained entry | Same argument subgraph and source parameter/annotation incidence | Bind same carrier at declared computation interface without entry Force; body may consume it later |
| Closure body/result | Lambda body, local Bind ordering and captured references | `Result(I_body)` and typed execution under the received/rebound environment; body result alone does not bound entry behavior |
| Designated result consumer | Conditional §3 producer expansion, using source declaration/port | Operation post-native-return consumer and native delimiter, or the closure's selected body/result computation; not inferred from result shape |
| Invocation return and whole Apply result | Same enclosing Apply and candidate result/whole-result labels | Complete return/world/latent-provider membership; no label asserts equality with `J_body` or the callee result |
| Callee pending suffix | Callee and argument child references plus actual producer template | Request-Bind closure of `kf >>= S_f`; receipt has not yet occurred |
| Receiver pending suffix | Argument, actual parameter/body/consumer references and their ordered template | Original request/response witness and outstanding rebind/body/consumer/return; receipt is not replayed |

Concrete code boundaries at the pinned revision:

- `yu-core/shadow_derivation.rs`: exact-candidate `IncompleteDerivation`
  stores `PendingCall { source, callee, argument, application_premises,
  capture, source_view_premises }`; it asserts no invocation judgment.
  Generic `PendingStructuralProjection` keeps Uses as
  `PendingUseNormalization`, expressly requiring original `Gamma`.
- `RawStructuralArena::from_artifact` retains each source form and child
  references. `RawCall` keeps the source-use/declaration/header/capture joins
  and pending premises. The endpoint skeleton labels are addresses under one
  Apply, not typed computation ports or execution phases.
- `yu-hir/shadow.rs`: `ClosureCorrespondence` remains pending typed capture,
  provider/receiver and semantic discharge. `Premise` explicitly leaves
  callable role, full membership and call-view realization unresolved;
  the source-view inventory includes independently typed original invocation
  and whole-row carrier/prefix/resumption interpretation.
- `yu-solver/lib.rs`: `retain_pending_applications` keeps each Apply and its
  callee/argument occurrence, recursively visiting retained children; state
  is `ApplicationTypingRuleUnresolved`. The exact local initializer is
  visited for pending applications without semantic local-Lambda collection.
  `emit_lambda` emits recipes only for its supported simple body cases;
  Apply/Group/Error bodies return without that recipe. Final solve moves
  both the retained HIR and pending application rows into `SolvedModule`.
- `yu-solver/shadow_f5.rs` exposes direct Name operand references and closed
  scheme observations while disclaiming typed endpoint/profile association.
  Q/R scheme-local binders are not original source slots or shared `xi`.

There is no current execution-phase carrier for Delay, receipt, rebind or
pending continuation in these structural views. That is a missing typed
producer, not a demonstrated lossy projection of a previously supplied
phase witness. Inventing another phase label would not prove any row above.

## Conditional derivation and smallest source cut

For `H_ret`, follow the Apply's two retained edges to their complete child
graphs. Under `H_src`, §6 generates exactly one Normalize skeleton per child
from its source tag. Under `H_rel`, §3 attaches a fixed Call template to those
references; it does not require argument evaluation, role guessing or a new
source occurrence. Actual provider definitions supply the receipt/entry/body/
consumer/return expansion when reached. Finite source recursion uses registered
references rather than unfolding. This gives the conditional construction.

The two relevant Bind partitions remain structurally distinguishable:

```text
callee Request:   Request(qf,C,kf >>= S_f)
receiver Request: Request(qr,C,kr >>= outstanding_receiver_suffix)
```

The first still contains argument construction and receiver entry. The second
contains only the actual outstanding part after the reached receiver phase.
Keeping the source operands enables those templates, but supplies no Request
typing or response/resumption admission law. Neither partition can be replaced
by an effect union. In particular a callee-prefix event gains no designated
receiver upper-output protection merely from membership in the whole Call.

The smallest **source cut for the audit**, not a minimized counterexample,
is the already selected five-node derivation:

```text
call(result(name f),result(name x))
```

It occurs in the approved nested block under ordinary formals. The local
binding/capture slice retains its actual source/HIR/core identities and the
pending inner Apply through solve. Under the selected ordinary-formal source
rules, the argument normalization is `Return(lookup x)`, even if the returned
value is latent. It therefore does not witness every independently admissible
whole carrier at `f`'s interface. A new inventory of this cut cannot close
the all-operand `CALL_TYPE` quantifier.

At the current generic **producer** boundary the first unavailable premise
is the original decorated lexical/interface judgment: for this callee Use,
`Gamma(f)` and Normalize must yield a computation whose returned value meets
the actual Function/provider contract at the original scope. The retained
BinderId, annotation occurrence and candidate endpoint addresses provide
locators for this judgment, not its interpretation or typing derivation.
The exact-candidate structural `Result(Name)` projection does not establish
that membership either.

Within `CALL_TYPE`, **granting** those source interfaces and its stipulated
independently admitted operands, the first Return-side semantic consequence
needed at `S_f` is:

```text
fixed original interpretation and admitted callee/world;
X[n_f](C0) yields Return(actual_f,Cf) with original witness
---------------------------------------------------------------- required
actual_f and Cf satisfy the same independent Function/provider/world
premises for actual receiver invocation at original X,xi and scope.
```

Its pending companion must type `Request(qf,C,kf >>= S_f)` with all admitted
responses and original raw-resumption developments. The inspected structural
interfaces encode neither independent judgment. If a complete supplied
carrier contract already entails the Return consequence, this leaf is
discharged conditionally; its source/semantic construction is still outside
the present code. Later Delay/entry/rebind/consumer/return laws remain needed.
Source-contracts §2.2 specifically forbids substituting the descriptor filter
for constructor typing, and §3.5 assumes the local lemmas. Core §7 checks
with supplied inclusion; §8 weakens an existing certificate on a fixed domain.
Neither produces that first independent descriptor/world fact.

This is consistent with the DAG: `CALL_REL` is conditionally closed;
`CALL_TYPE` requires `SEM_JOINT` and remains open. Even its closure would
leave original source-owned slot/contribution introduction at `ORIGINAL_ASSOC`.
No new DAG edge, source rule or carrier requirement follows from this audit.

## Independence, coverage and failure conditions

No Oracle, executable checker, reference implementation, random search,
mutation execution, build or test was used. Source/code correspondence shares
the stipulated typed-core transition templates; it independently checks only
what the pinned code retains and leaves unresolved. A checker implementing
those templates would test consistency with them, not prove their source
meaning or independent descriptor rules.

Coverage: full displayed §3/§6/§9 Call producer partitions; §7/§8 boundaries;
the four assigned code owners; two prior accepted structural slices; canonical
Call DAG nodes. Analytical partitions include callee Return/Request, actual
Value/retained entry, closure body versus operation consumer, invocation return
and pending suffix. No executable cases, seeds/ranges or performance samples
exist. Broad first reads were truncated; required sections were reread in
bounded extracts. No exhaustive repository search is claimed.

Named falsifiers for the structural finding would be a supported retained Apply
whose callee/argument subtree disappears, a same-scope provider/capture reference
lost by projection/solve, or a supplied typed phase witness erased before the
next consumer. No such witness was found in this bounded audit. Named invalid
shortcuts are treating the argument-effect label as already demanded support,
treating candidate Function return effect as a complete invocation certificate,
replaying receipt on resume, merging callee prefix with receiver upper-output
incidence, or selecting Normalize from solved shape. These are analytical
failure conditions, not executed mutations or newly found code defects.

Unverified: source-tag/interface production beyond retained structure;
independent descriptor/admission clauses and joint realization; actual world/
operand inhabitance; typed Bind/Delay/consumer preservation and every finite
history; Operation/Handle/Eliminate raw producer support; casts/adapters;
general recursive/local polymorphic inference; production-only Option 2
members; original association/licensing and complete source coverage.

Recommended next action: supply and independently justify the original
callee Return/pending-Bind descriptor/world consequence in
`DESC_CLAUSES`/`ADMISSION_CLAUSES`/`SEM_JOINT`, then use its exact witness
requirements to design the first typed shadow producer. Another structural
label inventory or transition-only probe leaves the same premise untouched.

## Checks and resource use

Read-only `git rev-parse HEAD` matched the pinned baseline. Bounded `rg`,
`cat` and `sed` inspected the named inputs. Python compared working bytes to
`git show BASE:path` for all twelve direct dependencies below: all unchanged.
No Git mutation or compiler/test edit occurred. Only this leased note was
written; final whitespace/dependency/hash checks are returned in the handoff.

Budget: at most 15 minutes, serial lightweight text inspection; zero heavy
processes, builds, tests or probes. CPU time and peak RSS were not instrumented.
Exact total wall time is unknown; source/hash commands each returned within
subsecond reported tool durations. No compute or performance claim follows.

| Direct dependency | SHA-256 at baseline |
| --- | --- |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `notes/theory/successor-proof-obligations.json` | `e866faaf68a813b95c80dcf46904a1e1f8dfbc5906b3ca019cd8e565eca9ffae` |
| `crates/yu-core/src/shadow_derivation.rs` | `714fa4f53ee14f7a4d4e1d38ff0820157838de9c4b70a266bee1998eb2851dc2` |
| `crates/yu-hir/src/shadow.rs` | `6ca7457b6f17cb753f328b509d7ac226a0ff523b95608ec1e8d247ee0089136c` |
| `crates/yu-solver/src/lib.rs` | `957f4bc7b5b8becc2e3574f6a9277da410dcfd473aba6327c700e8f930ff26e5` |
| `crates/yu-solver/src/shadow_f5.rs` | `dd4970dea858a01bee0717115d095bb65a532aa2b3f5a95c59ca2dbe0d6e9760` |
| `notes/progress/2026-10-08-call-type-computation-entry-attempt.md` | `0c87d266bdc76b061c5c9e09351723c7c1af4da8f3fca41abc1a4aa184c75dc9` |
| `notes/progress/2026-10-09-shadow-local-binding-source-identity.md` | `20ea9c8761f03fd9a7373b79925c5f51eb9da1b1b225d826bbac248134431797` |
| `notes/progress/2026-10-08-shadow-apply-endpoint-crosswalk.md` | `756c836ea84f1be019a8d898d6203d768353b9a8709b7424284fa20f63513fb8` |

## Commit packet

- Exact leased path: `notes/progress/2026-10-08-call-type-shadow-correspondence-audit.md`.
- Baseline SHA: `fd6434993f02d85221642ab2c4047eb63798f9ca`.
- Dependency hash deltas: none in all twelve direct dependencies.
- Review status: frozen, unreviewed research checkpoint; producer reread is not
  independent review. No closed theorem, gate or implementation authority.
- Checks already run: assigned rule/source/code reads, baseline SHA check,
  twelve baseline byte/hash comparisons, leased-path prewrite status; final
  note whitespace/hash and dependency recheck reported in handoff.
- Proposed commit message: `research: audit typed Call producer shadow correspondence`.
- Shared-record deltas left for primary/curator: optionally link the bounded
  negative structural finding and distinguish missing typed producer from
  carrier loss; retain open `CALL_TYPE`, `SEM_JOINT`, independent clauses and
  `ORIGINAL_ASSOC`. No shared task, theory, index, authority, manifest, lockfile,
  question bundle or other worker path was edited.

The producer stops writing before submitting this artifact for frozen review.

## Independent review

The compiler-referee found no blocking, major or minor issues. The review
confirmed that the audited retained Apply structure supplies source syntax and
provider identities only; its eight structural addresses are not typed ports.
The recorded test coverage preserves pending premises and does not discharge
them. Exhaustive operation/handler/elimination producers, complete history,
source adequacy and production conformance were not audited.
