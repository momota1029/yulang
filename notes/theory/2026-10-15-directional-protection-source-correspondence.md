# Directional protection: native constructor correspondence and first missing edge

Date: 2026-10-15
Status: frozen, unreviewed bounded source correspondence; parent gates remain OPEN
Claim class: static constructor characterization and minimized obstruction
Branch/baseline: `research/simple-sub-intrusion`, `5781fe30e711cb1aac2f7b3a97f4484cd0f278e2`
Production source baseline: `427d1ff5daab866fa7d89cb513a077063cc6454d`
Authority/implementation adoption: none added
Review owner: primary; fresh compiler-referee and spec-auditor review pending

## 1. Frozen statement, binders and exclusions

The assignment fixes the following claim before the derivation. For every
genuinely unannotated formal `f` at its original owning Lambda `L`, original
shared value root `v`, contract identity `beta`, source scope `sigma`, and
source-justified protection seed `k`, and for **each original source upper-use
occurrence** `u` exposing that protected variable as

```text
u : v <: U_u = A_u [Ein_u] -> [Eout_u] B_u,
```

introduce new protection from `(k,u)` at exactly `U_u.ResultEffect`, before
satisfiability. This introduction does not protect `Ein_u`, any position within
`B_u`, or the output of an existing provider/recursive lower Function `L_p <: v`
by backflow. Preserve independently inherited protection and all original
constraints. Identical eventual row values do not identify originating upper
and lower occurrences. Capture/freshening must carry the original scope and
joint occurrence correspondence, rather than select witnesses per port.

Hypotheses of the selected local rule are separately named:

1. `O(L,f,v,beta,sigma)`: actual formal annotation absence and original identity.
2. `P(k,v,sigma,u)`: `k` protects `v` while still inferred at this exposure.
3. `Upper(u,v,U_u,sigma)`: an original source-generated upper demand on that
   same root and scope, with its complete four-port Function meaning.
4. `Out(u,U_u,Eout_u)`: the designated output-effect occurrence of that demand.

The [selected addendum §§1–4](../design/2026-10-06-directional-inferred-effect-protection-addendum.md)
supplies `P and Upper and Out -> NewProtection(k,u,Eout_u)` as the local law.
Its [local source derivation §§1–3](../progress/2026-10-06-directional-protection-source-generation.md)
constructs that rule-relative incidence from certified inputs. The present
question is whether native source constructors actually produce and consume
those inputs/conclusions. The semantic premise `P` is not a certificate already
available in code merely because the selected policy requires it.

The bounded inspection covers the private candidate source schedule and the
named constructor/consumer seams below, conditional on successful admission
and the candidate effect path being enabled. This is an inspection envelope,
not a restriction of the original language obligation. No claim is made that
all supported source paths have been covered. Full nested-result exposure,
late-seed ordering, all-path source coverage, H1/H2/U and production cutover
remain OPEN; H3/P remains disabled. No new full nested-position matrix,
blanket `B` traversal, callback receipt, runtime role, concrete subtraction
grant, complete Call theorem, soundness theorem or principality theorem is
derived. Ordinary inference and source reachability are not narrowed.

Governing reuse: [top-level principles §1.1](../design/2026-10-11-yulang-inference-top-level-principles.md#11-source-constraints-and-intrusion-direct-clarification-2026-10-14)
requires original constraints before solving; [hygiene integration §§1,3–5](../design/2026-10-10-annotation-effect-hygiene-integration.md)
retains existing conditional transport results and their actual constructor
premises. Neither licenses reconstructing protection from endpoint equality.

## 2. Constructor and consumer ledger

Line locators below refer to the production baseline; the seven implementation
files in §6 are unchanged between that baseline, the packet baseline and the
inspected worktree. Each row describes actual code, except an explicit gap.

| Premise/edge | Source witness and constructor | Retained representation and consumer | Original scope/lifecycle and limit |
| --- | --- | --- | --- |
| `O`: annotation absence | `candidate_source.rs:245–303,378–403`: `emit_candidate_source` allocates parameter recipe identity; only `LocalSourceForm::Lambda` with `parameter.annotation.is_none()` inserts an `OmittedFormal`. Parameter Name resolution reuses `CandidateEndpoint::Parameter`, rather than inventing a provider. | `Plan.omitted_formals` stores owner, Lambda, formal, source position and `AnnotationScope`. `lib.rs:11384–11397` reads it at `admit_lambda_fact`. | Scope is local-binding identity when present, otherwise original definition identity. A bare Name of a known external callable does not enter this producer. This witnesses omission, not `P`. |
| Annotated alternative | `candidate_source.rs:395–403,878` schedules `FormalAnnotation` only for an actual annotation. `candidate_effect.rs:1099–1182` constructs paired Function children with composed variance and emits both formal value links. | `formal_domains` retains the negative domain used by Lambda construction. `candidate_formal_effect_port(None)` allocates an ordinary row; singleton symbolic rows remain connected. | `AnnotationScope` keys symbolic variables. This executable annotation route supplies no unannotated-formal protection seed. An omitted row inside an explicit annotation is not evidence of total formal annotation absence. |
| Owning Lambda/domain incidence | `lib.rs:11254–11420`, `admit_lambda_fact`, selects the original parameter row or explicit domain and constructs a positive Function lower bound on the Lambda root. For an omission, its raw domain child must still be the exact negative parameter variable. | `FormalConstruction { source, domain, domain_child, function }` is attached to the owning source `Origin` by `candidate_context_seed_with_formal`, `candidate_context.rs:2740–2753`. | This is authentic source/domain construction. It is not a protection witness, provider contract, activation or receipt. Failure of the raw-child check yields no construction record. |
| Lambda entry flow | The same Lambda owner allocates entry and returned effect rows and admits `entry <: returned` and `body_effect <: returned` at slots 3 and 4. Slot 3 calls `retain_inferred_entry`. | `InferredEntryOrigin` records Lambda, original entry/returned endpoints, occurrence and cause (`candidate_context.rs:157–170,1395–1408`); the slot-3 `Origin` retains its handle. | This proves entry-flow construction, independently of omission. It supplies neither `EntryCertificateId` authorization nor `P(k,v,sigma,u)`. The Function/domain origin and slot-3 entry origin are distinct admissions. |
| `Upper` and raw `Out` | `candidate_source.rs:601–622` retains `CandidateRelation::Apply`, its actual callee/argument endpoints, source checking occurrence and `ApplySourceInput`. `shadow_apply.rs:1428–1510` validates the correspondence, allocates an invocation row and builds `negative_function_term(argument, argument_effect, return_effect, result)`. | `NativeInterface` retains `demand`, invocation row/effect and the other complete ports before `constrain_live_value`. The admitted slot-0 inequality is `(callee,demand)`; `return_effect` is exactly the negative term of that fresh invocation row. | This is the original upper occurrence of the Apply. It is generated before satisfiability. No successful Function comparison is needed to construct it. Original scope authentication for a protection witness has not thereby been constructed. |
| Complete invocation accounting | `shadow_apply.rs:1510–1576` admits the original value constraint, then includes callee evaluation effect and the invocation effect in the application effect. Argument computation effect is the demand's `ArgumentEffect` port. | Original occurrence/cause and all four Function children are retained; no port is independently chosen from a different provider. | This ledger preserves the actual complete demand/accounting. It is not a proof of full Call semantics. |
| Structural `FunctionPort(ResultEffect)` | `lib.rs:12549–12595` decomposes a matching positive/negative Function pair. The result-effect task is `lower.2 <: upper.2`; Argument and ArgumentEffect reverse, ResultEffect and Result preserve. `candidate_step_function_dispatch`, `lib.rs:12701–12725`, admits then enqueues each child. | `candidate_function_port_admit`, `candidate_context.rs:2785–2828`, retains `Dependency::FunctionPort { parent, child, field, operation }`. It preserves the parent's post-check context on ResultEffect and Result and swaps it on the two input ports. | This is structural comparison incidence after the pair is available. It does not create a source-specific protection at the original upper demand. Selecting all `Preserve` fields would also select Result; selecting all ResultEffect dependencies would include non-source comparisons. |
| Captured/per-use identity | `candidate_scheme.rs:515–545,548–595,749–828` captures four ordered Function children, bounds, relation IDs, source-bound orientation, evidence snapshots and existing context payloads. | `prepare_candidate_fresh_use` remaps rows jointly under level/non-generic rules (`1010–1045`), renames existing context payloads (`1099–1135`), and `begin_candidate_fresh_bound` retains `FreshUse` transport with original source bound and one use origin (`1254–1299`). | These are real retained transports, not a new protection producer. They cannot transport an omitted-formal protection witness that was never produced. Retained restoration state is not a proof of every bound's activation or complete replay. |
| Bounded formal/receiving Argument inspection | `candidate_context.rs:302–352` requires actual Argument/Swap incidence, both Replay inputs, FreshUse and the original raw domain child; one source Name handoff may intervene. | `candidate_formal_argument_incidence` returns borrowed structural evidence. Production uses of this helper were not found in the inspected owner files. | This is the receiving call's Argument correspondence to the enclosing formal. It is distinct from a later invocation `f x` and its upper `ResultEffect`. It neither produces nor consumes protection. Earlier extrusion/additional derived routes are excluded by the helper. |
| Actual context consumer | `candidate_context_source`, `candidate_context.rs:2683–2695`, returns identity except for an existing closed annotation allowance. `candidate_context_execute_relation`, `2964–3030`, consumes executable zero-word allowance filters. | Weights retain resolved allowed effects and annotation owner/position. `LocalWeight.left_word` and `right_pops` are empty arrays (`113–139`); `SourceUnitPush` is dormant metadata. `BothFromRight` is rejected by fresh payload discovery (`1572`). | These executable checks implement their annotation context responsibility. No inspected constructor connects an omitted formal plus an original upper demand to a protection-bearing context, and no inspected consumer discharges that protection. A Parent span or row representative supplies no such authority. |

The two calls must remain distinct: passing a callable to an enclosing omitted
formal uses the enclosing Function's Argument comparison; invoking that formal
inside its body generates its own upper Function demand. Neither an inherited
provider effect nor a copied enclosing Lambda ResultEffect may be substituted
for that original invocation's `Out` occurrence.

## 3. Bounded derivation and exact stop

On the inspected source route, actual annotation absence constructively gives
`OmittedFormal(L,f,position,sigma)` and the parameter endpoint. The original
Apply constructively gives its complete symbolic upper demand and a designated
raw invocation `ResultEffect` before the satisfiability call. The owning Lambda
can later retain the exact raw-domain `FormalConstruction`. These are supported
constructor facts, rather than inferred final-type shape.

The **first unsupported transition** in the source-to-law dependency order is:

```text
actual unannotated formal, original shared root and scope
  -/-> source-produced P(k,v,sigma,u): protected while inferred at this exposure.
```

No omitted-formal action produces this witness in `candidate_source`; the
formal path of `candidate_effect` is entered for explicit annotations; the
Lambda construction supplies structural domain and entry-flow facts; and
`candidate_context_seed_with_formal` stores the structural fact without an
executable protection operation. Its generic method name `seed` is not the
semantic seed `k` of the selected directional law.

Even if an external proof supplied `P`, a second native edge remains absent:

```text
P(k,v,sigma,u) + original Apply Upper/Out
  -/-> an executable protection incidence specifically at U_u.ResultEffect.
```

This second edge is recorded to identify the consumer seam, not proved under
an assumed first edge. `FunctionPort(ResultEffect, Preserve)` preserves an
already inherited context and records structural incidence; it is not an
introduction operation. It is also too late to serve as the sole witness of
pre-satisfiability source construction.

There is a further concrete staging warning, not a selected scheduling policy:
`emit_candidate_source` pushes the body visit from Lambda visitation and adds
`Action::Lambda` only at Lambda finish (`378–404,659–674`). Body Apply actions
therefore precede this Lambda's formal-construction admission. The omission
record already exists in the immutable plan; the later `FormalConstruction`
alone cannot establish protection present at each earlier exposure. No
retroactive seed rule or arbitrary order-independence theorem follows.

The semantic local derivation can still be reused conditionally: supplied valid
`P`, original `Upper`, and exact `Out` yield its single output incidence, with
no clause reading a provider lower to create protection. That is precisely the
existing rule-relative result, not a newly established compiler theorem.
Absence of the native producer proves neither a source-level hygiene
counterexample nor the desired no-backflow implementation property: an inert
implementation cannot satisfy the required positive introduction by doing
nothing. Independently inherited protection remains a separate input whose
full lifecycle preservation is unverified here.

## 4. Proof-obligation economy and reuse boundary

The earlier [callback reconstruction note §7](2026-10-15-callback-profile-reconstruction-receipt.md#7-economy-audit-and-one-decisive-next-action)
already identifies source introduction and later typed incidence as separate
owners. The [shallow-Catch bridge §3](2026-10-15-shallow-catch-hygiene-constructor-bridge.md#3-hypothesis-by-hypothesis-bridge)
hits the same missing source introduction. The intervening
[structural-incidence slice](../progress/2026-10-15-omitted-formal-structural-incidence.md)
retains real omission/domain evidence, but adds no effect authority. Its older
wording about an undecided full position matrix does not undo the already
selected local directional rule.

Apply the existing audit before a further equivalent attempt: the required
positive introduction and no-backflow behavior are A/B; reconstructing actual
annotation absence/domain identity from row aliases is D, for which the source
already retains evidence. The remaining `P`/directional introduction cannot be
discharged by another Parent census, another profile-assuming transport lemma,
or reclassifying the gate. Source formation knows original omission and scope;
Apply admission knows the original upper occurrence and exact output port.
Those owners must supply the missing coupled construction/consumer evidence.
No extra language restriction, annotation requirement, full nested-result
profile or reconstruction calculus is justified.

Existing hygiene transport proofs remain usable under their actual typed
correspondence/profile/owner hypotheses. This note supplies some raw source
anchors and identifies the missing introduction; it does not assert those
hypotheses all hold for the native candidate, equate parent/copy equality with
injective renaming, or redo the established conditional theorems.

**One next action:** the primary should assign a narrowly authorized, reversible
constructor/consumer slice joining original omission/root/scope to protection
at the original Apply demand's `ResultEffect`, with a constructive invariant
for its before-satisfiability stage and provider no-backflow. Require real
executable evidence at both owners before a further preservation proof; leave
late-seed semantics and unrelated nested exposure open rather than inventing
them. This recommendation does not grant implementation authority.

## 5. Evidence, coverage and resources

Method: one bounded static pass; no alternative proof-model iteration. Read
the five required rules in full, `rules/orchestration-budget.md`, the
`yulang-proofs` skill, `.codex/config.toml`, `.codex/agents/prover.toml`; the
four governing documents in §6; the narrow source ranges identified in §2;
`tasks/current.md:1–108`, `tasks/research-lab.md:1–95`, and directional/hygiene
navigation entries in `notes/design/INDEX.md`. Also read the economy/obstruction
sections of the two linked theory notes, the structural-incidence checkpoint,
`candidate_context_tests.rs:487–545`, and
`yu-core/src/shadow_directional_protection.rs` in full. Large exploratory reads
were bounded/truncated; decisive claims above use subsequent focused ranges.

The core adapter explicitly requires `AssumedDirectionalInput` for protected
exposure, upper use and covariant output; `derive_conditionally` returns
`ConditionalStatus::Assumed`. It supplies neither native source generation nor
a production consumer. Existing tests/checkpoints provide reported bounded
structural observations only. No test was executed or treated as a protection
witness in this pass.

Commands: read-only `git branch --show-current`, `git rev-parse HEAD`,
`git status --short`, focused `rg`, `sed`, `cat`, `sha256sum`; scoped
`git diff 427d1ff5daab866fa7d89cb513a077063cc6454d HEAD -- <seven implementation paths>`
and `git diff -- <same paths>` both returned empty. Final checks are restricted
to this note's link targets, balanced fences, final newline and whitespace,
plus dependency-hash revalidation. No compiler checks were run.

Budget: one leaf; no descendants; zero Cargo/build/test/probe/measurement
processes, zero samples. Shell reads and note-integrity checks only, sequential
local execution; no resource-heavy process. Allocated wall time at most 20
minutes; CPU/RAM were not measured. No Git mutation or shared-record edit.
Requested route: normal Sol/high leaf; actual effective model/effort metadata
is unavailable to this worker and remains **unknown**. Configuration defaults
are `gpt-6.1-sol`/`high`, and the prover role omits overriding pins; these facts
are not runtime verification. No Astra requested or used by this worker.

Mode: primary-selected M2, two independent reviewers pending. Producer status
is unreviewed; no self-certification. Beyond the explicit exclusions in §1,
error/suspension/replay completeness, all alias/return/capture routes, handler
Receive/Observe, attachment/receipt/residual ownership, and executable hygiene
preservation remain unverified. No gate status is promoted.

## 6. Dependency snapshot and commit packet

SHA-256 of the frozen direct source/authority dependencies:

```text
6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7  notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md
3702eb2ea5108eba1adc8ab7a557542abb9993cee09f70b738e2999a05a2d185  notes/progress/2026-10-06-directional-protection-source-generation.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a  notes/design/2026-10-10-annotation-effect-hygiene-integration.md
3a1ad7155d784c1ff0234dc7815f0d49618bff307a6564c0646cf8e510a248c4  crates/yu-solver/src/candidate_source.rs
f414efa7efdb17644f4dfa6b0bba621c1bb7cccd0f83735c33a0acb875da6b91  crates/yu-solver/src/candidate_effect.rs
6301ca80eec137df3f2c2c44e2edaa7dbdf1ed7a78c69617228888e63654e461  crates/yu-solver/src/candidate_context.rs
c8ef7cc472f0dcb60d793c6f9b4f6ba1aefb76f919ff2a3ce9310f85eb647dcd  crates/yu-solver/src/candidate_scheme.rs
e902da1c9a7f0fb4dcd806c87563d1ae46d35bbb999e69b7fee51c3c0f6e4bf5  crates/yu-solver/src/lib.rs
3db7eb04045391ceb939612226ea87e7bac6c035f3c2d4c210a8d3d4fd641831  crates/yu-solver/src/shadow_apply.rs
9bb4fa098d275874dc0349b115dcc9031648b788fedefd1466af60889e460493  crates/yu-core/src/shadow_directional_protection.rs
```

Exact changed/leased path:
`notes/theory/2026-10-15-directional-protection-source-correspondence.md`.
Baseline: `5781fe30e711cb1aac2f7b3a97f4484cd0f278e2`; source baseline:
`427d1ff5daab866fa7d89cb513a077063cc6454d`. Changed direct dependencies:
none. Review: pending fresh compiler-referee/spec-auditor; research-only
checkpoint, no theorem/cutover closure. Checks already run: source baseline
diffs, direct hashes, and note-only integrity as reported in the handoff.
Proposed checkpoint message:
`research: locate missing directional protection constructor bridge`.

Proposed shared-record delta, left to primary/curator: record authentic
omission/domain retention and pre-solving original Apply/ResultEffect
construction as supplied; identify absent native protected-variable-at-exposure
producer as the first missing edge and absent directed executable introduction
as its immediate consumer seam. Keep H1/H2/U OPEN, H3/P disabled, full nested
exposure/late-seed/all-path/production gates unchanged. Link this artifact only
after primary adjudication; no task/index/design record was edited here.
