# Nested binding versus curried Function: bounded falsification

Date: 2026-10-06
Status: frozen, unreviewed research characterization; no theorem closure or implementation authority
Baseline: `503ae9d21fc7b0e4a1062cd101804fb13183273c`
Legacy dependency: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Exclusive lease: this file only
Method: source-grounded counterexample search by minimal distinguishing observations; no execution

## Objective and result

Try to falsify the proposed correspondence between

```text
B: my apply f = { my step x = f x; step }
C: my apply f x = f x
```

`C` denotes the approved curried shape for this comparison, not a claim that
current production HIR accepts its two-formal header. An explicit pair of
curried Function nodes is proof notation; this note does not adopt inline
lambda grammar as an alternative source encoding.

**Bounded characterization:** no source-grounded counterexample was found
among evaluation order, effects, lexical capture/lifetime, administrative
allocation, scope, and final-expression selection. This is a failed falsifier
search over these routes, not a proof of contextual equivalence. The smallest
remaining discriminator is to invoke the returned Function after the outer
invocation and brace scope have ended. The exact candidate's operational
capture/evidence survival and administrative-block realization are not proved
by the retained nearby inference witness.

The prior source/legacy audit supplies the forward conditional derivation;
this note does not repeat that method. It also does not reinterpret the
selected provisional Handler treatment or claim source acceptance.

## Governing sections and fixed decisions

- Authoritative inferred-call-views §§2–3, lines 90–134: annotations, lexical
  scope, captures and argument/call evidence generate one shared contract;
  the original `nu,K,D` stay jointly scoped. Unannotated `f` has a provisional
  fully protected Handler view; ordinary `x` supplies the scoped discharge
  evidence. This is neither an empty-effect assumption nor a generic
  Value-entry-implies-Pure rule. Exact formation judgments remain open.
- Authoritative F5 foundation §§3–4 and 21, lines 65–101 and 483–523:
  one-formal production subset, value-classified Lambda, and monomorphic
  parameter lookup. This bounds current construction; it does not define
  arbitrary nested-local block execution.
- Authoritative source-result choice §4, lines 136–159: known computation
  interfaces are preserved; `Result(Value(A))=Comp(empty,A)`. Ordinary data
  lookup/storage/return is inert. A second implicit result layer is rejected.
- Authoritative scheduling choice §§1 and 4, lines 13–37 and 153–171:
  whole arguments are reified; actual callable entry owns consumption. Result
  completion and receiver-expiry placement remain distinct invariants.
- Brace syntax §1, lines 5–10, and binding syntax Non-goals, lines 190–195:
  grammar does not decide HIR interpretation, block results or recursive scope.
- Draft typed core §§2–3 and 6, lines 70–106, 117–135 and 396–410:
  descriptors retain lexical references and typed evidence; closure creation
  is inert; local binding extends an environment with the RHS result. These
  are candidate construction rules, not independent proof of the raw mapping.
- Redesign charter §§1–2, lines 24–48: preserve final well-typed-program
  capability against frozen Yulang2; intermediate scheme shape and F5
  representation are not compatibility requirements.

Frozen legacy references at `a58eefc3` state ordered final-expression block
results (`control-flow.md:174–189`; `syntax-style.md:186–208`) and left-to-right
currying (`functions.md:23–32`). Frozen local lowering declares `step` before
lowering the tail (`block_local.rs:122–140`), routes its argument to
`LambdaScope::Defined` (`866–896`), generalizes it (`545–594`), and transports
the tail's value (`1284–1306`). Frozen lambda lowering recursively constructs
curried stages and gives Lambda construction a pure value classification
(`lambda.rs:271–282,310–368`). These support the existing meaning without
certifying exact current source execution.

## Claim classes and exact premise

**Established artifact facts:** the cited frozen documentation, lowering
branches, selected decisions, and retained ledger row exist at the pinned
revisions. No new execution fact is established here.

**Candidate assumptions for the correspondence:**

- **L:** the raw brace resolves `f`, `x`, and final `step` to the intended
  outer formal, inner formal and local declaration, constructs the one-formal
  Function without running `f x`, and selects its final value.
- **C:** the returned Function retains the same outer `f` value/cell reference
  and required typed evidence after brace and outer invocation exit. Source
  lifetime/receiver rules attach to the same calls and captures in both forms.
- **O:** administrative `step` binding and lookup add no observable effect,
  force, receiver boundary, or identity/resource distinction on the supported
  envelope. Equality of solved endpoints alone does not establish O.

**Conditional route outcome:** if L/C/O and the fixed parameter/result/call
rules hold for both forms, none of the distinguishing observations below
separates them. This statement is restricted to the displayed observations;
it is not an all-context theorem, type/principality theorem, or completed
source registration result. L/C/O remain the exact unproved premise. The
Draft core calculation would assume them, so another checker built from its
transition table would leave this premise untouched.

## Minimal distinguishing observations and failed routes

The contexts below are observation notation, not certified runnable programs.
Let `h` be a supplied callable whose body emits one observable request `tau`
and returns an ordinary value when invoked. `h` is used only to describe an
operational discriminator; substituting a concrete Pure callable is not a
proof of the unannotated formal's role-resolution rule.

| Route | Smallest useful observation | Falsifier required | Outcome in inspected evidence |
|---|---|---|---|
| Evaluation order/effects | Obtain `g = apply h`, then stop before calling `g`. | `B` emits `tau`, diverges, or consumes an extra computation while `C` only returns its inner Function. | No `f x` lies outside the inner body. Frozen Lambda construction is a pure value and selected data transport is inert. Requires a contrary raw mapping to falsify; none found. |
| Latent result/extra force | Obtain `g = apply h`; invoke `g` once on ordinary value `0`; observe one completed invocation. | One form executes `h` twice, recursively forces its latent return, or returns an extra delay requiring another consumer. | The inner call expression is identical. Selected result A forbids implicit extra-layer synthesis; scheduling and actual callable entry are fixed. No source evidence authorizes the extra consumer. |
| Capture/lifetime | Obtain `g = apply h`, let outer invocation and braces finish, then call `g 0`. | `B` loses `h` or its evidence/visibility while `C` retains them. | This is the smallest unresolved operational discriminator. The returned body has free-name set `{f}`, with `x` bound; `step` is not free in that body. Runtime retention after exit is not proved by static TypeVar sharing. |
| Scope/shadowing | Place an unrelated enclosing binding named `step`, then obtain `apply h` and call the result. | Final `step` resolves to that enclosing binding, or `f` resolves to a fresh unrelated binding. | Sequential legacy local scope supports selecting the newly declared `step`; no forward use or same-spelling `f` binder occurs in this candidate. Changing the source to introduce another `f` would be a different program. Exact current L is still required. |
| Final expression | Observe the value returned by the brace directly. | The local declaration, unit, or a computation carrier is selected instead of final `step`. | Frozen docs and lowering select the final expression. Brace syntax also treats a trailing separator as a separator, not an empty statement (§2, lines 19–25). Arbitrary empty/record/control blocks are outside this result. |
| Allocation/identity/resource | Observe an identity primitive or a deterministic allocation/rejection boundary while obtaining the returned Function. | The extra local binding becomes observably distinguishable from the inner curried Function construction. | Neither form invokes `f` at construction, and both introduce an inner Function. No selected primitive/cap or exact allocation census was found in the narrow read set. We cannot invent pointer equality, assume all allocation invisible, or prove identical resource rejection. This is conditional on O. |

The lifetime observer cannot be reduced to observation before return: that
would never test extrusion. It needs only the two curried invocation stages;
mutation, State, local recursion and additional bindings are unnecessary to
state the missing preservation condition. Calling `g` twice can test reuse,
but adds no independently justified source rule and was not pursued.

The ledger's nearby witness (`2026-09-29-intrusion-oracle-ledger.md:36`) returns
`inner` capturing outer `x`, with captured TypeVar absent from the local
quantifiers. Its Oracle report inspects inference/arena identities, not the
runtime effect trace or surviving receiver evidence of this exact candidate.
The failed forward-local reference at row 37 cannot falsify B: B has no such
forward reference. Expanding that failure to B would misapply the witness.

A separate static risk remains: local `step` is generalized and used through a
local definition, while the direct second curried stage has no corresponding
local-let generalization. The nearby ledger establishes capture avoidance for
its displayed witness only. Different printed quantifiers alone would not be
a compatibility counterexample under charter §2. A real falsifier must show
changed final acceptance or loss of the shared `f`/original `nu,K,D` evidence.
That is the separate H_call/H_registration gate, not settled by this runtime
route analysis.

## Independence, mutations, coverage and stopping boundary

No checker, interpreter, Oracle process, parser, compiler, test, build, probe,
network access or Git mutation ran. Frozen docs, frozen lowering and the
retained Oracle ledger share the Yulang2 lineage; they are corroborating
artifacts, not independent operational oracles. The ledger was not reproduced.
The prior notes are dependencies, not new independent evidence. The producer's
own reread does not count as review.

Conceptual mutations considered, without executing any mutants: hoisting
`f 0` into the outer brace would enable a pre-return request; dropping the
captured `f` reference/evidence would make the post-return observer fail;
selecting the declaration instead of final `step` would change the returned
value. Each attacks one named mapping obligation. None is evidence that the
actual candidate performs that mutation. No seeds, numeric ranges, random
sampling, enumeration or measured performance samples apply.

Read envelope: supplied audits; exact current call-view/F5/result/scheduling/
core/charter sections; brace/binding syntax; pinned legacy function/control/
style references and two lowering files; retained Oracle ledger. One narrow
keyword query for identity/allocation/capture in four legacy reference paths
returned no match; this is not an exhaustive absence claim for the language
or runtime. A prior combined source-read capture was truncated; the decisive
core passages were subsequently read narrowly. Shared task/index reads were
navigation only; pending question bundles and live shared edits were not
consumed as authority. No whole-repository runtime search was performed.

Budget consumed: 8 sequential lightweight top-level `exec_command` invocations,
including lease write and dependency hash/equality checks. All reported command
wall times were at most 0.1 s. Aggregate CPU, peak RSS and complete session wall
time were not instrumented and remain unknown. Read-only Git subprocesses were
sequential; no heavyweight process or child agent ran. Only this lease was
written and unrelated changes were preserved.

Stop/failure conditions: a direct dependency changes, an exact approved raw
brace/capture realization is discovered, a selected observation distinguishes
administrative allocation, or an accepted execution/typing witness supplies
a contrary mapping. Any of these requires a narrow delta analysis. Another
transition-table toy model would share L/C/O and would not resolve the blocker.

Recommended next action: establish the exact two-statement brace's returned
Function capture/evidence survival across outer return, including its
administrative binding observation law, then pass that fixed realization to
the separate registration-preservation gate. No new language meaning is
requested by this report.

## Frozen dependency hashes

Current direct dependencies matched the baseline bytes immediately before the
lease write. Legacy bytes were read at their named revision only.

| Revision | Path | SHA-256 |
|---|---|---|
| `503ae9d2` | `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `503ae9d2` | `notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md` | `781d719ef6ddd458908b61b7b95f49e4c6abec9ffed79595af5fe1e201caac83` |
| `503ae9d2` | `notes/design/2026-10-02-source-result-synthesis-choice.md` | `71326de0897159343797d6aec083860ee0f57a1bc04f9c4ae77e579ea0ba5992` |
| `503ae9d2` | `notes/design/2026-10-02-source-call-scheduling-choice.md` | `181e95a9d87d90c265f28ad87e0176f10dd11c3c84bd308e1b802c571ae8d568` |
| `503ae9d2` | `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `503ae9d2` | `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| `503ae9d2` | `syntax-reference/en/src/expressions/braced-statement-block.md` | `81f637db94d344162c4e2541ee4b955b4469180e755ee800aa39bf9074987b58` |
| `503ae9d2` | `syntax-reference/en/src/statements/binding-use.md` | `18d08a59c211027dc95c9556d71703a8bda7b4c1d3dc72e253e7b7dae93c928f` |
| `503ae9d2` | `notes/progress/2026-09-29-intrusion-oracle-ledger.md` | `b603335b97537931396c56cd2537fa7a83df3ce8f73cc9738de5920c641c8b60` |
| `503ae9d2` | `notes/progress/2026-10-06-source-registration-existing-encoding-audit.md` | `5ea1957b97e18eb3640fb39039f1af44c2fa2730ff2db79db19cd78158f230e1` |
| `503ae9d2` | `notes/progress/2026-10-06-source-registration-block-value-legacy-audit.md` | `bef24bf81b5d561538974db75c950a2df9cc2ed0b49248f2440fb0781941e436` |
| `a58eefc3` | `web/docs/reference/functions.md` | `b2a616ea603dccaa431bfcea0c4c2e6eff54b5e058ff9fb6370cb2eb081fa611` |
| `a58eefc3` | `web/docs/reference/control-flow.md` | `cce270b697f4a8ce3a711a6daec107405dbf93d192187e555138204813d84da1` |
| `a58eefc3` | `web/docs/reference/syntax-style.md` | `d14da22ae583771387f41320126c5d2be0fe20a33df8d78a8113243cd2c3d229` |
| `a58eefc3` | `crates/infer/src/lowering/expr/block_local.rs` | `661386fe559d8e207a9597962cfee3c11f05f21aa2888e22b2c0143825051898` |
| `a58eefc3` | `crates/infer/src/lowering/expr/lambda.rs` | `2e0206bdcfdfbe98d13c12eec7ba8f7964383bc08c92947352ad370754024db9` |

## Commit packet

- Exact leased paths: `notes/progress/2026-10-06-source-registration-block-core-falsification.md` only.
- Baseline SHA: `503ae9d21fc7b0e4a1062cd101804fb13183273c`.
- Legacy dependency SHA: `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none; SHA-256 inventory above.
- Claim/review status: frozen, unreviewed bounded failed-falsifier characterization and conditional route outcome; no independent review, source equivalence, gate closure or implementation authority claimed.
- Checks already run: pinned-source reads, narrow frozen keyword query, byte equality of current direct dependencies to baseline, SHA-256 inventory, exclusive-lease absence guard, and exact artifact write/readback. No executable semantic verification.
- Proposed one-line research-checkpoint commit message: `research: bound block-to-curried-function falsification routes`.
- Shared-record deltas intentionally left for primary/curator: record no source-grounded falsifier among the six inspected routes; retain exact returned-capture/evidence and administrative-observation premises; distinguish that result from H_call/H_registration preservation and final acceptance. No task/index/theory/authority/question-board bundle was edited.
