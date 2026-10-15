# Declared Unit-arrow inlet: exact formation boundary

Date: 2026-10-16
Status: bounded source/constructor characterization and minimized proof obstruction;
inlet theorem NOT established or refuted. Independent review accepted with
the two minor source-precision corrections recorded below.
Baseline: `66202b0da798a6293561e2fe7241942c9b3217df`, branch
`research/simple-sub-intrusion`. Primary identifies production `35e87f844`
apart from test-only delta `3be1ae365`.
Exclusive lease: this file. No implementation or semantic authority.

Independent review: compiler-referee `ordinary_carrier_semantic` reviewed
producer SHA-256 `d014bb1fbaad667846f0cfd32d4bc8a1bb53b188bc230d923cc8816698d4c001`.
The primary accepted and corrected its two minor findings: dispatch retains
original component rows before replay, and `stamp_input` is conditional on an
authenticated scoped demand. The bounded obstruction is otherwise accepted;
no theorem or parent is closed. Primary diff inspection suffices for these
precision-only corrections under the review-convergence budget.

## 1. Frozen question

The original source is

```yu
my receive (f: () -> 'a) = { my g = f(); g() }
```

Fix every original scoped assignment `xi=(nu,K,D)`, the original annotation
scope and shared variables, independently valid input environment containing
the same actual `f` at its declared target `F_decl`, and independently typed
compatible punctured ambient context at each original first-Call event.
Keep the actual provider/decomposition, captures, carrier origin, current
world, continuation, typed paths and shared incidences fixed. Quantification
includes every independently compatible future event, finite pending prefix
and original complete returning witness `z`; no fresh marginal choice of
provider, context, K, D or result witness is permitted.

Let `t` be the authentic `Delay(Return(Unit))`, with the original formation
and `Comp(empty,Unit)` validity supplied by its literal/Return/Delay
constructors. Suppose the actual generated native Argument and ArgumentEffect
constraints, including their inherited context obligations, are jointly
satisfied at those same indices. Required conclusion:

```text
CheckedCarrier(F_decl; t, current_context, original_incidence, xi).
```

Here `CheckedCarrier` is only an abbreviation for theorem R's existing
whole-argument check at the declared descriptor. It is not a new predicate
in production or a proposed semantic definition. It must be obtained before
checked-challenge assembly and elimination of the input f's membership.
The antecedent must not include this check, actual-provider admission or
the desired complete invocation conclusion under another name.

The stronger possible formation lemma would cover all independently lawful
Unit carriers satisfying the same inlet constraints; this packet needs only
the actual source carrier above. It does not narrow the original parent
domain to that stronger lemma's convenient instances. Arbitrary-alpha Result
soundness, both original tagged packets, pending Bind, complete Call output,
principality and the original reverse FIRST-RESULT theorem remain separate
OPEN parents. No claim here changes their quantifiers or necessity.

## 2. Actual construction and consumer facts

`candidate_effect.rs:1124–1164` supplies an exact structural derivation.
The Unit branch returns the primitive positive/negative Unit leaves. The
Function branch recursively constructs argument and result pairs, reversing
argument variance, and constructs each effect port once. For this annotation
both effects are omitted. Each omitted port allocates one fresh effect row
and returns its positive and negative views. Thus the two polar targets
share one `E_A`, one `E_R` and the original annotation-scoped alpha. Neither
effect row is defined to be empty. The positive target is structurally

```text
Fun(Unit−, E_A−, E_R+, alpha+).
```

`candidate_formal_annotation:1191–1231` builds that pair in the original
shared scope, admits positive-target-to-formal at slot43 and
formal-to-negative-target at slot44, and retains the negative formal domain.
This is a target exposure/check construction, not a new actual provider.
The approved annotation-boundary answer §§2–3 and concrete-effect annotation
design's “Annotation checking and publication owner” select this target
publication and retention of local realization evidence. They do not select
an event-only interpretation of its type operands.

The authenticated Apply demand retains original argument-value and evaluation-
effect component rows u and d. The native Function dispatcher gives input
children `u+ <= Unit−` and `d+ <= E_A−` at the same parent
(`shadow_apply.rs:1531–1641`; `lib.rs:12624–12665`). The complete demand also
has Result and ResultEffect children, whose soundness is not established by
this input specialization. The original literal bounds supply Unit and Bottom
through actual replay; dispatch does not replace u/d with those leaves or erase
the inherited contexts.

`candidate_context::candidate_function_port_admit:3001–3064` obtains the
parent's `post_check_context`, applies Swap to Argument and ArgumentEffect,
and prepends any local source prefix in source order. It retains the original
sources and FunctionPort dependency. Only when the authenticated scoped record
has `scoped.demand = Some(demand)` does AE additionally use
`ScopeTransformer::stamp_input(demand.input)`; the Value argument has no such
transformer. Unscoped execution has no stamp, and this explicitly annotated
formal ordinarily has no omitted-formal introduction supplying such a demand.
The actual applicable context and argument incidence must be preserved rather
than imposing the scoped branch on every instance. Primitive equality alone
is not the full pair interpretation.

The actual context consumer at `:3201–3290` does not contain a Unit-based
context-neutralization rule. Identity contexts and contexts without filters
remain undischargeable there; filtered Effect tasks execute the original
Allowance checks and retain their residual. A Value task with such filters
returns unavailable at this consumer. These branches establish neither a
source whole-carrier check nor an equation erasing the parent context when
Unit has no latent payload. This is a source inspection result, not a claim
that the solver must implement a special Unit rule.

## 3. Attempted direct derivation and the first missing premise

There is a genuine local simplification. Literal Unit carries no callable or
computation payload that requires a later latent elimination. Pure Return
creates no request, receipt or grant and preserves the current world.
Inert Delay does not run that Return at formation. At any lawful designated
demand its represented code returns the same Unit, with the current state
and original origin; compatible future demands repeat this argument without
reviving old authority. Consequently there is no argument-execution request
whose handler routing must be compared. This is the concrete constructor
argument in the predecessor's §3, not an assumption about all pure carriers.

It does **not** derive admission to the declared arrow. To complete that
derivation, one must unfold the declared arrow's independent carrier contract
and verify every introduction premise using the above constructor evidence
and the satisfied native context checks. The governing sources stop before
that unfolding:

1. Typed-core §6, “Source parameter-role generation,” says annotated endpoints
   use the **admitted annotation derivation** and explicitly distinguishes the
   outer role from nested annotation checking. Its source application rule
   retains the whole computation's existing typed path/contract obligations.
   It does not define the admissible carrier set of the written arrow from
   its Unit/AE children.
2. Typed-core §7 defines representation-preserving checking using VIncl/CIncl
   of complete decorated interfaces. Its erasure proof consumes those
   inclusions. The actual receiver obligation is explicit, including boundary
   and protection conditions even for matching roles. Section 9 derives port
   directions but explicitly says those directions do not prove the joint
   challenge inclusion. No Unit specialization of full CIncl is supplied.
3. Authoritative contextual Function membership §2 supplies checked-challenge
   assembly and same-provider membership elimination, but explicitly retains
   **descriptor admission/observation relations as independent inputs**.
   Its selected Return/Delay cases prove carrier validity, not a new arrow
   annotation's carrier contract.
4. Source-contracts §3.3 Initial takes a source-typed punctured context with
   its whole argument; FutureUse takes a source-typed future port. Those rules
   preserve the original domain and prohibit comparison-dependent admission.
   They do not introduce the absent annotation check. C-realization §3.5
   additionally assumes its finite source/emission conformance certificate.
5. Theorem R, semantic-input realization §5, expressly assumes an operand
   assignment whose meaning includes **whole-argument checking at F_c**.
   Its proof uses that check to assemble the challenge, then eliminates the
   same f's membership. Applying R here before proving the check is circular.

The first unsupplied premise is therefore the following original formation
rule/correspondence, at the declared annotation owner:

```text
the independent original elaboration of this () -> alpha target
identifies its carrier-admission premises, and the actual Unit/AE
children with their Swap/stamp_input context imply those premises
for this same source Delay(Unit), with the original K/D and paths.
```

This is precise even without inventing a replacement formal relation: the
missing object is the introduction derivation for the fourth field of
semantic-input §2's checked-challenge assembly, specialized to the original
target published by `candidate_formal_annotation`. The source target's
existence and its correct positive/negative type operands are already
accounted for. Their exposure does not independently specify every premise
of that carrier check.

The approved full-context answer quantifies over all independently typed
compatible contexts; it does not make an unproved filling independently
typed. Conversely, choosing an arbitrary restricted `D_F` would ignore the
actual declaration and cannot refute this claim. No such countermodel is used.
The absence of requests discharges event-indexed obligations only after their
actual formation clause has been identified. It cannot justify silently
declaring all boundary/path/context premises vacuous. In particular the
caller still has a continuation, an actual receiver and original incidence
even when this argument's own evaluation has no requests.

This establishes a **logical gap in the available derivation**, not logical
independence from every possible repository theorem, an accepted source
counterexample, a solver defect, or a need for a new user semantic choice.
The stop condition was the first genuine missing original formation rule;
no third equivalent attempt was made.

## 4. Economy audit and exact application to the parents

The missing implication is class A correctness at the native/source inlet
boundary. Natural admission of this ordinary call also touches class B.
It is not an optional converse or maximality theorem. No evidence inspected
shows that an established source carrier-admission proof was generated and
then discarded; therefore adding a registry, metadata certificate or new
reconstruction layer has no justification here. Target publication already
retains local realization evidence and should remain its sole owner.

The earlier event-only Support attempt concerned a different owner and was
resolved by existing target-exposure authority. The Sol forward attempt and
this declared-target specialization now encounter the same carrier-check
premise. This second method follows the original annotation formation rules
and the actual Unit/context consumers; its result is an exact location of
the missing introduction rule, not proof progress on the implication itself.
Do not dispatch another Unit-purity or empty-row proof as a substitute.

One next action for the primary: obtain the original source annotation
carrier-admission introduction derivation at this exact target, with an
exhaustive premise list, and independently review its application to the
Swap/stamp_input children. If the current source formalization truly lacks
that case, route its legitimate completion through the existing authority
and review process; do not infer a new language restriction or redesign from
this report. A supplied rule must be justified by its original source owner,
not defined to equal native success.

Once that specific rule yields the check, theorem R's assembly and membership
elimination apply to the same input f and t; theorem E then preserves complete
and pending invocation at that provider. The arbitrary-alpha Result/context
translation remains separate. Neither those consequences nor the two tagged
packets are presently claimed by this note. FIRST-RESULT, complete forward
soundness, pending Bind, hygiene/principality and cutover remain OPEN.

## 5. Freeze and verification packet

Only static file inspection and this leased Markdown write were performed.
No builds, tests, probes, compiler edits, Git mutations or children. One
lightweight shell process at a time; no concurrent compute or benchmark
samples. CPU/RAM and elapsed runtime were not instrumented; work remained
within the assigned 25-minute bound and stopped at the stated obstruction.
The primary remains verification owner and independent-review assigner.

Requested routing from the primary packet: bounded `gpt-6-astra` / `low`.
Inspected `.codex/config.toml` registers prover and gives normal Sol/high
defaults; `.codex/agents/prover.toml` omits model/effort pins. This leaf has
no exposed runtime metadata proving the effective model/effort, so observed
settings are **unknown**. No override, hot reload or child launch is claimed.

Static checks: the frozen predecessor SHA matches the assigned
`8593bb9c55ef73f040ea802b83a953182a8c1da80839a191a59c56663051ff62`;
read-only branch/HEAD inspection matches the pinned baseline. Exact dependency
digests follow. No dependent production changes were made by this leaf.
The note is unreviewed and may be checkpointed only as non-authoritative
research; it is not a closure certificate.

Commit packet: sole path
`notes/theory/2026-10-16-declared-unit-arrow-inlet-correspondence.md`;
baseline `66202b0da798a6293561e2fe7241942c9b3217df`;
proposed message `research: locate declared Unit-arrow carrier admission premise`.
Shared-record delta for the primary/curator: retain all parent gates OPEN and
record the annotation carrier-admission introduction owner as the blocker;
no theorem status promotion. No shared record was edited.

Tracked dependency changes against the pinned baseline: none.
The frozen predecessor is an explicit hash-pinned working-tree input absent
from the baseline tree; the initial blanket baseline lookup detected that
absence and was corrected to distinguish it from a changed tracked input.

```text
44ee33d077c61c9dea6359299ca49218afc6ca1b5b6807690838309b25c731c9  crates/yu-solver/src/candidate_effect.rs
72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6  crates/yu-solver/src/candidate_context.rs
199963ac9cd13eebca44c4881b859eeb1f801259cc944bf1d5a57df78dc0c070  crates/yu-solver/src/lib.rs
357b274d0de509931bda3015a99b1a1cf2ac86d75a45d230d62ab456c56740ba  crates/yu-solver/src/shadow_apply.rs
0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e  notes/design/2026-10-02-typed-computation-core-elaboration.md
1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186  notes/design/2026-10-05-source-contracts-and-common-allowance.md
4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1  notes/design/2026-10-05-inferred-function-call-views.md
0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0  notes/design/2026-10-08-contextual-function-membership-definition.md
3a3186723cd93edd2f767a7e4a481cb6dbed701fc749502e640071f65a4d89ae  notes/design/2026-10-10-concrete-effect-annotation-implementation.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a  notes/theory/2026-10-08-call-semantic-input-realization.md
7a660d3b4a5a334d64b1c0d5283c8217eed763404099bc528075d37479f4ee08  notes/theory/2026-10-16-first-call-native-forward-soundness.md
b1ba2a9520903e5ca122ff279dc3cd76fffd44aee889e579c9179288a1606cea  notes/theory/2026-10-16-native-annotation-flow-correspondence.md
e1e2ff77b181fe42edd404ee0d69cfc6d3bb0fbc99ba7e7f092710025d11fb12  questions/2026-10-05-source-annotation-boundaries/approved-answer.md
9b63603890cd522ec80ef81e6208c52acdb1f09ab0a847a9b51368a8f563acf3  questions/2026-10-05-production-function-inlet-context-domain/approved-answer.md
```
