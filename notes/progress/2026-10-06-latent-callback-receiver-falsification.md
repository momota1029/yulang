# Captured callback: two outer valuations of one source formal

Date: 2026-10-06
Status: Frozen, unreviewed research-only conditional discriminator
Baseline: `d8e25902a946edfd907f1c385fa2b18b5cf12370`
Exclusive lease: this file only
Method: minimal context pair and mutation analysis; static work
Implementation authority: none

## Objective and result class

Attack a registration shortcut for the exact candidate

```text
my apply f = { my step x = f x; step }
```

The discriminator varies the outer lexical valuation while retaining the
same source formal and captured use. If two independently admitted outer
contexts bind distinguishable providers to that formal, their returned
closures must retain the corresponding providers. Sharing a static source
contract/root does not imply equality of those concrete provider operands.

This is a **conditional countermodel to provider equality**, and a bounded
characterization of what the approved capture fact entails. It is **not an
accepted-source Yulang counterexample**. Existence of the two admitted
contexts, their completed typed contracts, and their later invocation
certificates remain hypotheses. No runtime activation rule is inferred.

The candidate `PROPOSE`/`REGISTER` route already excludes provider equality
between distinct outer valuations. This result supports that exclusion; it
does not refute the faithful candidate or prove U1–U5. The prior reviewed
zero-invocation prefix and profile-premise inversion are not rerun here.

## Baseline, authority and dependencies

| Exact source | Use and authority |
| --- | --- |
| Callback-context delivery §§2–4 | Authoritative: static slot/profile versus dynamic receiver; known contextual literal B; preserve actual callable role and entry. |
| Nested-block source realization addendum §§2–4 | Authoritative for this exact candidate: sequential binding, non-invoking final result, lexical resolution and retained outer capture. It does not decide registration or general closure lifetime. |
| Inferred Function call views §§1.1–5 | Authoritative direction: shared source contract, stable position/scope, original correlated `nu,K,D`, Q-independent admission; detailed producers remain open. |
| Source contracts §§2.2,3.1–3.5 | Reviewed conditional package, concrete clauses Draft: active provider clauses at original typed incidences/binder environments, supplied decorated source, retained roots, independent future admission and certified use. |
| Integrated nested-block q1/a1 and call-view q1/a2 answers and receipts | Accepted user decisions and integration provenance; archived a1 call-view answer is excluded. |
| Source-registration candidate route §§1–4 | Non-authoritative proposal: `FormalProvider(b_f,p;eta)` means `p=eta(b_f)` subject to U5; one static root is explicitly not one provider across outer valuations. |
| Prior nested-capture and captured-provider falsification notes | Method boundary: their activation-prefix and first-profile-premise attacks are existing results, not new results here. |

All listed dependency bytes matched the primary's pinned baseline before
writing and at freeze. Task/design index reads supplied navigation only.
No uncommitted question bundle or concurrent worker output was used as authority.

## Smallest context pair and explicit hypotheses

Use the candidate's proof labels `b_f` for the resolved outer formal, `u_f`
for its captured body use, and `c` for `f x`. Let `eta_i` denote an outer
lexical valuation and `eta_si` the valuation retained by the returned closure
`s_i`. These are semantic proof operands, not runtime addresses or a proposed
storage layout.

H1. Two possible outer contexts supply providers `p_0` and `p_1`, with
`p_0 != p_1`, and reach the candidate's function-return point with
`eta_0(b_f)=p_0` and `eta_1(b_f)=p_1`. This is a candidate input hypothesis;
the scoped source decision does not prove that both contexts are typeable.

H2. The selected meaning applies to each context: the returned closure retains
that context's outer `f` capture. The approved lexical fact consequently gives

```text
eta_s0(b_f) = eta_0(b_f) = p_0
eta_s1(b_f) = eta_1(b_f) = p_1.
```

H3, needed only for a later-call or observable discriminator. Independently
formed complete contexts admit a call of each returned closure on the same
ordinary value argument `a`. Each context supplies its own complete original
joint assignment `xi_i=(nu_i,K_i,D_i)`, actual role/entry, typed capture/call
route, receipt and current receiver activation. Each tuple remains joint;
no coordinate is borrowed from the other context. If one common assignment
can admit both providers, the pair can specialize to that case, but existence
of such an assignment is not assumed or derived here. Lawful freshening
must retain the original template relationships and scope.

H4, needed only to observe a different result. At that admitted argument,
the supplied actual providers have independently justified distinguishable
observations `r_0` and `r_1`. A pure terminating result pair would suffice,
if independently typed and admitted. This note supplies no surface definitions
of such providers and does not manufacture their observation semantics.

| Coordinate | Context 0 | Context 1 |
| --- | --- | --- |
| Original candidate/formal/use/call | `C,b_f,u_f,c` | same original source coordinates |
| Static contract/root/profile | same source template, if U1/U2 are supplied | lawful instance of that template, if U1/U2 are supplied |
| Outer valuation | `eta_0(b_f)=p_0` | `eta_1(b_f)=p_1` |
| Returned capture, by H2 | `eta_s0(b_f)=p_0` | `eta_s1(b_f)=p_1` |
| Later `f` operand, given H3 | retained `p_0` at the original typed route | retained `p_1` at the original typed route |
| Actual invocation, given H3 | supplied current activation/receipt and actual role/entry | supplied current activation/receipt and actual role/entry |
| Observable distinction, given H4 | `r_0` | `r_1` |

The smallest equality falsifier consists of two outer valuations and the two
retained provider equations; it needs no request, handler, recursion,
annotation, response or resumption. One valuation cannot contradict a global
choice of one concrete provider. Dropping `p_0 != p_1` removes the contradiction.
The later call and H4 are optional extensions that make provider fidelity
observable; they are not needed for the algebraic witness. This is minimal
by differing valuation/provider count, not a minimization of accepted source
bytes or compiler executions.

## Derivation and mutations

Suppose a mutated registration claims that the shared source root/template
determines one concrete provider `p*` for every returned closure, independently
of its retained lexical valuation. For both contexts it asserts

```text
eta_s0(b_f) = p* = eta_s1(b_f).
```

Substituting H2 yields `p_0=p_1`, contradicting H1. Thus under H1–H2 this
extra equality is incompatible with the approved retained-capture meaning.
No transition model is needed. The contradiction is in the provider operands;
it does not depend on printed Function ports or an effect-port witness.

| Mutation / shortcut | Discriminator and limit |
| --- | --- |
| Choose one concrete provider per static formal/profile and reuse it for both returned closures | The H1–H2 equality contradiction above. Sharing a symbolic relation evaluated under each original binder environment is compatible with the pair. |
| Replace every later captured lookup by the provider from the most recent outer return | After the second return, a supplied later use of `s_0` still requires `p_0`, not `p_1`. This requires H3 and the retained-capture meaning; the note does not assert an accepted surrounding multi-call program. |
| Treat an active provider clause at capture/return as a live receiver certificate for later `f x` | Source-contract §2.2's semantic activity at an incidence is not dynamic receiver activity. The table has no later receiver conclusion until H3 supplies the current activation/receipt. Callback-context §3 requires activation. No new activation transition, expired-boundary revival test or receiver identity equation is derived here. |

The first two mutations concern actual captured providers. They do not prohibit
conservative production observations under Option 2, prescribe a closure
representation, or require a source-tight production bound. Nor does the pair
prove that the two contexts have the same completed inferred/public type.

## Exact blocker and stopping point

The faithful candidate clause `p=eta_si(b_f)` passes this conditional
provider-fidelity discriminator. It still needs U3 to certify typed capture
correspondence and U5 to interpret the provider clause at the original typed
incidence. U1/U2/U4 remain separate. No comparison `Q` occurs in the pair;
that absence does not prove the missing admission/certificate producers are
Q-independent.

To promote this to an accepted-source witness, a source producer must admit
the two outer provider contexts and their later calls while preserving the
same original source relationships and each whole `nu,K,D` assignment. The
approved exact-candidate interpretation alone does not provide that producer.
A checker supplied with these valuations and lookup/activation rules would
only reproduce the conditional result, leaving this premise untouched.
The lane stops here rather than enlarging a supplied-transition toy model.

## Independence, coverage, checks and resources

There is no executable oracle. The capture equations use independently
approved source meaning; the provider/admission certificates remain shared,
unproved assumptions of the conditional packages. The equality contradiction
is a consequence of those explicit hypotheses, not independent validation
of the source typing or invocation rules. This producer claims no independent
review of its output.

Coverage: one source candidate, two possible outer valuations, and the three
named mutations above, reasoned about statically. Seeds/ranges and exhaustive
or random search are inapplicable. No tests, builds, probes, formatters,
Git mutations, children, shared-record edits or question-board writes.

Commands/checks: bounded `cat`/`rg`/`sed` governing and prior-method reads;
read-only `git status --short`, `git rev-parse HEAD`; sequential Python
SHA-256 and pinned `git show` byte comparisons; leased `apply_patch`; final
dependency/path/whitespace inspection. Early combined output was truncated;
decisive governing sections and approval clauses were reread in bounded
captures. No repository-wide rule-absence claim is made.

Resource envelope: static work only, at most six lightweight read commands
concurrent; no heavyweight process. No numerical CPU/RAM/wall-time cap was
supplied. CPU time, peak RSS and total wall time were not measured. Only the
leased note was written.

Unverified: actual source acceptance, complete source registration and
two-provider admission, U1–U5, generalization/local polymorphism, runtime
activation/handler behavior, production Option 2 membership, all-view
containment, principality, source adequacy and implementation.

Recommended next action: require the proposed source producer to instantiate
its formal-provider clause under each returned closure's retained valuation,
then separately derive the first later call's current receiver/receipt
certificate; use the two-valuation table as its fidelity obligation.

## Frozen semantic dependency hashes

Whole-file SHA-256; unchanged from the assigned baseline at freeze.

| Path | SHA-256 |
| --- | --- |
| `notes/design/2026-10-03-callback-context-delivery.md` | `df4941d4c66e4f3147257024a35e7041a2c51dd528657cc80efaf3d0db62fed5` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/progress/2026-10-06-source-registration-candidate-route.md` | `fd42d09b04a3454a085439f8564a337e463996e5cc4e86858f994a5fe15ad40f` |
| `questions/2026-10-05-nested-block-function-source-realization/approved-answer.md` | `04ee0dc089dc6ad19a184d31775a146c08b07f2f287099d2e5b54d7d1d5a643e` |
| `questions/2026-10-05-nested-block-function-source-realization/receipt.md` | `e5e59e176eb865a588b2843b18137571fe9c5b6f43bf1ca349bc60c9ad90f0ec` |
| `questions/2026-10-05-function-call-view-formation/approved-answer.md` | `1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536` |
| `questions/2026-10-05-function-call-view-formation/receipt.md` | `6dcf408143c7eb48260d8c4df9ef73834da8d28a7f4ec9744ab381e67414cee0` |

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-latent-callback-receiver-falsification.md`.
- Baseline SHA: `d8e25902a946edfd907f1c385fa2b18b5cf12370`.
- Changed dependency hashes: none consumed; pinned snapshot above.
- Review status: frozen unreviewed research-only conditional discriminator;
  no accepted-source counterexample, runtime activation rule, gate closure
  or implementation authority. Writes stop before submission for frozen review.
- Checks already run: exact governing-section and prior-method reads,
  lease absence, baseline/live dependency equality and hashes, final narrow
  path/whitespace inspection. No executable semantic checks/tests/builds.
- Proposed one-line research-checkpoint commit message:
  `research: distinguish captured providers across outer valuations`.
- Shared-record deltas intentionally left for primary/curator: record this
  two-valuation fidelity obligation and the independent admission/current
  activation blocker; retain U1–U5, registration, principality, adequacy and
  production gates as open. No task/index/theory/authority file was changed.
