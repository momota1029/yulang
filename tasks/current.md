# Current task: replace Yulang type inference with SCC-intrusion inference

Updated: 2026-10-05. Branch: research/simple-sub-intrusion.

## Objective and authority

Prove the SCC-intrusion successor sound, principal, and compatible with
Oracle's final well-typed-program capability on the supported envelope, then
implement the fully reviewed and approved inference machine. This objective
remains active. A test-only finite parent/use transport prototype is authorized
as an experiment; production inference-path replacement remains gated by the
open soundness/principality obligations.

Authority order is current user decisions, in-scope Authoritative designs,
active rules, confirmed code/test invariants, then general practice. The design
index is navigation only; source designs govern. See
[design authority](../rules/design-authority.md) and
[design index](../notes/design/INDEX.md).

Yulang user-decision handoffs now use the approved
[question-board workflow](../rules/question-board.md) for goal-driven work and
explicit board requests. The board is `questions/` in the active worktree;
all unintegrated question/answer bundles stay unstaged/uncommitted and visible,
including explicitly approved local answers. The answerer writes selected answer
files without Git mutations. The questioner discovers and validates the finalized
answer, rechecks bundle stability, then commits the matching question/draft/answer.
Disjoint primary file responsibilities need no worktree-wide ownership handoff.
Consumption requires committed, unchanged, fresh approved content. Authority:
[questioner-integrated handoff](../notes/design/2026-10-04-questioner-integrated-answer-handoff.md).
Delivery: [workflow record](../notes/progress/2026-10-04-questioner-integrated-answer-handoff.md).
Next workflow action: discover/validate finalized local answers at turn start and
before dependent work, or publish the next real unresolved question without a
commit. Posting does not pause a goal; continue independent authorized work.
Publication does not notify or resume a stopped goal.

## Closed decisions

- **Inequality:** one endpoint-dependent `A <: B` solver. Variable-bound
  propagation may use transitivity; successful concrete comparisons may not
  be composed. Casts/adapters are evidence or realizations from concrete
  inequality resolution. Optional-record compatibility is not transitive
  structural subtyping.
- **Function/effects:** source introduction/context selects Pure or Handler
  before Function-port interpretation. Effects are coupled ports, not
  independently-subtyped Types. Covariant rows are canonical flat forms;
  contravariant concrete-bearing descriptors retain only structure needed for
  witnessed partial reverse addition using existing subtraction evidence.
  `never`, `Any`, empty rows, and polarized solver bounds remain distinct.
- **Callback literal:** B is the normative/reference constraint generation:
  expected context selects Handler/boundary before body generation, endpoints
  are independently synthesized, and the completed interface is checked by
  one ordinary `F_lit <: F_cb`. A is permitted only as B-equivalent constraint
  scheduling/partial evaluation; it must preserve acceptance, principal
  solutions, method/adapter choices, and residual/evidence semantics. Stronger
  endpoint assignment/equality is invalid.
- **Existing Pure callback value:** preserve its actual role and §21 entry; a
  callback slot supplies a typed invocation view without rewriting the value.
- **Cross-edit inference lifecycle:** intrusion, variable-level, bound, and SCC
  internal state need not reverse-update across edits; a changed inference
  component may be rebuilt. Downstream inference invalidation may stop only
  when the complete generalized canonical interface is unchanged. Interface
  fields/equality, component boundaries, and non-inference artifact invalidation
  remain open. This adds no implementation authority. See the
  [Authoritative rebuild-boundary addendum](../notes/design/2026-10-04-scc-intrusion-cross-edit-rebuild-addendum.md).
- **Experimental implementation allowance:** the user permits bounded
  experimental implementation before complete soundness/principality proof,
  only with no known source counterexample, explicit invariants, differential
  tests, and rollback; this does not authorize production-path replacement.
  The currently authorized experiment is a `cfg(test)` finite graph
  parent/use transport model with caller-supplied identity partition. It does
  not select production roots, solve constraints, generate source endpoints,
  or alter `InferenceSession` behavior. Its invariants, differential tests,
  failure conditions, and rollback are in the
  [Authoritative experimental transport gate](../notes/design/2026-10-04-intrusion-experimental-transport.md).
  This turn hardens its focused test matrix with incomplete/overlapping/unknown
  partition rejection and explicit failure injection at every helper fault
  point; a two-use late-failure case confirms no partial overlay escapes. The
  initial skip count was corrected from six checks per use to the observed
  three. All 8 focused tests pass; details are in the
  [transport test follow-up](../notes/progress/2026-10-05-intrusion-transport-test-followup.md).
- **Research playground loop:** the user explicitly authorizes executable
  models before proof closure and expects active conjecture/check/break/shrink/
  revise/prove work on structural FMP, callback production bridge, and
  principality. These models may be discarded after an obstruction is
  recorded; passing finite searches is evidence, never theorem or production
  authority. Production inference routing remains gated by soundness and
  principality. See the [research-playground direction](../notes/design/2026-10-04-inference-research-playgrounds.md).
- **Future data existential compatibility:** constructor/package internals may
  hide witness types with existential packaging; they need not all become
  public data parameters. This constrains future representation choices without
  adding existential support to current inference or broadening current proofs.
  No data-existential syntax, elimination, generalization, solver-carrier, or
  runtime rule is selected; existing operation/request existential designs
  remain separate. The user's `ref 'e 'a` example is recorded
  there only as a representation candidate: `run` universally quantifies
  `'b`, while the write path separately existentializes it; their quantifier
  interaction remains unspecified. The read/write examples select no typing
  or runtime rules. See the
  [Authoritative compatibility addendum](../notes/design/2026-10-04-existential-data-witness-compatibility.md).

The governing semantic sources are [concrete compatibility](../notes/design/2026-10-03-concrete-compatibility-boundary.md)
and [callback context delivery](../notes/design/2026-10-03-callback-context-delivery.md).
Oracle behavior around `Never`, `Any`, effects, and references is
characterization only where it conflicts with these decisions.

## Conditional source-generated results

The user's permission to add source-generated hypotheses now has two reviewed
conditional proofs in
[the source-generated theorem package](../notes/design/2026-10-04-source-generated-callback-structural-theorems.md):

- **Callback C:** an explicit positive source relation generator and its
  shared-body lift give full bound containment at one `ν,K,D`, including
  conservative local alternatives. The lift copies old witnesses and adds
  only total-function fresh logical coordinates; independently generated
  source challenge rules prove domain inclusion. This is a theorem for that
  constructed generator, not arbitrary annotations or every production
  endpoint with the same printed ports.
- **Structural S:** after normalization, each free/free component has only
  closed anchors, or exactly one open anchor. With the stated rigid-scope
  condition, a root-only decision kernel plus guarded anchor reconstruction
  proves arbitrary-tree/regular-tree satisfiability equivalence and constructs
  a simultaneous regular witness. Nonempty mandatory Records, Function
  contravariance, and open recursive descriptors are included. The principal
  residual and every original inequality remain unchanged.

These are source-checkable conditional results, not language rejection rules.
Their exact restrictions, reviewed repairs, and verification are recorded in
[the paired progress note](../notes/progress/2026-10-04-source-generated-theorems.md).
The unrestricted obligations below remain active.
The raw/production bridge is now localized: current `yu-hir::ResolvedExpr`
emits only lambda, integer, name, and error nodes, while its simple-chain
lowerer rejects non-leaf `Apply` expressions. It therefore does not yet emit
Theorem C's call/bind/request derivation graph. The exact source-shape audit
and next bridge obligations are in
[HIR/source-core boundary](../notes/progress/2026-10-04-hir-source-core-boundary.md).
The bounded `host (\x -> x)` source is also characterized at the current CST
boundary: the expression parser emits Error tokens for `\`, `-`, and `>` under
an empty operator table, before an inline lambda reaches HIR. With a
constructed `\` prefix entry, the current parser consumes it as an operator
and still rejects the arrow; the bounded parser candidate must reserve only a
complete lambda header before dynamic lookup. This table-level probe does not
establish that source can declare `\`.
An isolated test predicate now exercises that reservation shape for the
complete single-binder opener, matching the lexer’s identifier family and
same-line space/tab trivia. It rejects incomplete headers but does not drive
the parser or check body recovery. A paired CST assertion maps its binder and
arrow ranges to the current error-bearing tree and confirms the body token
remains inside the parenthesized application argument; no lambda node is
produced, so the parser/HIR bridge remains open. A test-only raw-source mapper
now combines those CST ranges into an Apply candidate for exactly
`host (\x -> x)`, preserving the callee and unary-lambda binder/body; it
rejects missing-binder/body cases. It consumes the current error-bearing CST
and emits no production node, resolved name, typed-core derivation or callback
evidence. The bounded source/HIR bridge remains open; see the
[HIR/source-core record](../notes/progress/2026-10-04-hir-source-core-boundary.md).
The HIR-to-core bridge now closes for its monomorphic pure-value fragment:
integer/name leaves and unannotated parameterized bindings map to finite
`literal`/`name`/`lambda(P,result(body))` derivations under a fixed `Gamma`.
This includes `id x = x` with `P=Value(A)`. Applications, callback call sites,
and whole-carrier evidence remain unavailable in this HIR. The pre-HIR
associator preserves one-to-four parenthesized and ML-argument calls as
left-nested one-argument stages; the remaining ordinary-call bridge is from
those structural nodes into `ResolvedExpr` and typed-core `call`/`bind`. See
the call-stage association probe in the HIR/source-core record.
An additional test-only candidate now maps real associated call nodes into a
binary `Apply` tree across bounded mixed source spellings and preserves a
nested call argument (`f(g(a))`). It found that postfix calls can belong to an
ML argument (`f a(b)`) and that parenthesized HIR nodes may have multiple
children; the probe was revised to preserve both facts and now asserts the
exact 14 recovery-free patterns among its 30 generated cases. This characterizes
parser-to-candidate shape only. It does
not add production Apply lowering, endpoint generation, or Theorem C
correspondence; details are appended to the HIR/source-core record.
The candidate now also mirrors typed-core §6's `(I,d,n)` shape under a finite
monomorphic Gamma for five ordinary-call forms, including chained and nested
applications plus a Computation-tagged `pending` name. Tests check each
structural-shadow endpoint triple and retain the nested computation as a whole
argument. This notation model omits actual port profiles, `K,D`, invocation/
subtraction evidence, and full constraints, so it is not executable core or
complete Function comparison. Production Apply lowering and principal
acceptance schemes remain open.

## Latest main-gate results

The reviewed [source factor-cover proof](../notes/design/2026-10-05-source-factor-cover-and-query-preservation.md)
gives a finite sufficient test for exact relation reconstruction: each original
factor's complete operand interface must occur in a retained bag. It is also
necessary for a uniform guarantee over independently arbitrary factors on
nontrivial product domains, without asserting that production fibers are
products. Exact reconstruction preserves every unchanged joint client and
actual direct-query evidence relation. A fixed XOR/returned-provider source-core
example defeats all proper projections of its ternary dependency even after
approved observation erasure. The isolated checker exhausts 148,224 cases.
Complete production membership across generalization/fresh use and the legal
common-component introduction/typed-view rule remain open; original totality,
all-view quantifiers and the actual exported root are unchanged. Full callback/
principal classification remains C, structural FMP A. Review/verification is
tracked in the [new attack record](../notes/progress/2026-10-05-factor-cover-main-gate-attack.md).

The single-inequality endpoint rule also has a small executable check:
[`research_inequality_endpoint_dispatch.py`](../tools/research_inequality_endpoint_dispatch.py)
exhausts 512 variable-edge graphs and the approved optional-record
nontransitivity witness. It verifies that local concrete successes never
enter variable-edge closure, and exhausts all nine lower/upper endpoint pairs
for a retained middle-variable witness. A single nonempty interval is rejected
by a direct-concrete-composition mutant: `{foo?: string} <: X <: {foo?: int}`
with `X = {}`. The table contains all three approved directed optional-record
successes, six successful cells including reflexivity, 64 local-evidence
subsets, and seven inhabited lower/upper pairs. This is finite
characterization only; general lower/upper
replay policy and complete solver behavior remain unspecified. See the
[progress record](../notes/progress/2026-10-05-inequality-endpoint-dispatch-playground.md).

The first HIR-backed Function-realization candidate inspects the current
`id`/`zero` artifacts, reconstructs their identity/constant body relation, and
checks projected typed observations over 26 finite argument-history tuples
per source. The old-tuple-preserving lift is exact in this candidate. Its
remaining bridge is the key one: no production endpoint currently defines
this complete relation, and HIR lacks application/callback invocation forms.
A separate test-only transition probe now executes two explicit two-request
`Force(D) >>= B` suspension/resumption splits, checking suffix order, no
receipt/Force replay, and Pure-role preservation under a Handler slot view.
This characterizes the source rule for those traces; it still does not connect
production Function bounds to complete membership.
Details and limits are in the
[source-indexed realization playground](../notes/progress/2026-10-05-source-indexed-function-realization-playground.md).
The same HIR-backed test now exhausts 96 source modules for
`id : 'a -> 'a`, `wrap ignored = id`, and two aliases of `wrap`: all 24
declaration orders crossed with four pairs of hygienic parameter names. It
checks resolved source-root identity through the returned Function, the three
collected/routed named uses, fresh instantiation count, and the same nested
diagonal principal scheme for both aliases. This reaches production parsing,
HIR, constraint collection, routing, and generalization, but no invocation of
the returned Function is expressible in current production HIR. A separate
test-only composition runs 1,314 bounded outer-Force/future-call histories
against those actual HIR identities, with exact independent trace/state
expectations. Compiler-referee review found a checker weakness (the model's
own final state was reused as expected input) and trace-coverage gaps; the test
now derives exact ordered traces and final state from source responses and HIR
occurrences. Review is clean within that finite scope. The full callback bound
and principal common-allowance bridges remain open.
The same test-only artifact now retains and checks the exact positive
Function-port tuple, `LambdaRecipe`, source body occurrence/binder, original
component handles, and distinct body/construction effect rows across those
variants and three fresh closed uses. Mutations that substitute the
construction row, another Lambda's body row, or a different Function result
coordinate are rejected. F4 projection checks now require source Lambda
occurrences present and internal body occurrences absent before asserting the
source Lambda's `Empty` effect; an independent review caught and closed a
previously vacuous conditional check. Focused verification passes. This
preserves existing test-only source evidence and adds no production carrier;
the application/callback endpoint and full bound-membership gates remain open.
See the [source-indexed realization playground](../notes/progress/2026-10-05-source-indexed-function-realization-playground.md#retained-function-artifact-reconstruction).

**Classification A: normalized pure structural FMP is proved.**
[Finite fence completion](../notes/design/2026-10-04-structural-fmp-fence-completion.md)
constructs a regular solution of the same fixed package from any arbitrary
permitted tree solution, with at most `8^N` states on the finite flat-term
universe. Exact shared recursive descriptors, mandatory Record width,
Function contravariance, invariant coordinates and arbitrary rigid permission
sets are preserved. This proves finite-quotient conflict reflection and the
previous cofinal bounded-rank residual (BR), without an additional source
predicate. Two independent reviews found no defects; the finite distance
algebra and Record case checks pass. See
[the proof/review record](../notes/progress/2026-10-04-structural-fmp-proof.md).
The earlier [finite-feedback result](../notes/design/2026-10-04-structural-finite-feedback-quotients.md)
and its failed non-cofinal quotient families remain valid. Production
Function/effect correspondence, joint predicates and principal projection
remain distinct open gates; no compiler implementation is added here.

The user has authorized an executable research loop before proof closure. The
new [finite-fence playground](../notes/progress/2026-10-05-structural-fence-playground.md)
implements the reviewed §4–10 profile construction outside production in
[`check_structural_fence_completion.py`](../tools/check_structural_fence_completion.py).
Its first counterexamples found and shrank five candidate implementation
mistakes (endpoint reversal vs variance conjugation, negative child direction,
empty Record classification, start-profile budget handling, and rigid-head
namespace collision); these were corrected and retained as regressions. The
checker currently passes 13 focused packages and validates every generated SAT
witness in 1,226 exhaustively generated one-root packages. Its bounded
false-UNSAT oracle checks every root assignment into 127 labeled one/two-node
graphs: 265,856 checks for the one-root family and 45,080 checks for 169
two-root one-inequality packages. The complete two-root/two-inequality family
adds 14,196 packages and 5,700,660 graph/root checks. Targeted distinct
per-root rigid cases add 5,830 screens. Three-node checking covers the focused
structural rejection cases in a signature matched to `Int`, `Bool`, and both
Record fields (810,000 graph/root checks), plus rigid cases (617,310 screens).
No bounded counterexample remains. Review found and corrected an earlier
vacuous three-node signature. Independent reviews closed the generator, count,
permission-filtering, and package-matched scope deltas. These are finite
characterization results, not proof or production solver selection; rigid
permissions are only partially cross-producted with the package family. The
next inference replacement gate is the production-facing
callback/principality bridge. Full Function/effect correspondence and source
adequacy remain open.

[Two-sided constructor-bound regular completion](../notes/design/2026-10-04-preclosed-structural-regular-witness.md)
now has an independently reviewed constructive proof and executable research
checker. If every flattened variable has a constructor-bearing lower and
upper bound in the finite pure structural closure, arbitrary-tree and
regular-tree satisfiability coincide and closure decides existence. Multiple
open recursive anchors, mandatory Record width, Function contravariance and
invariant coordinates are included. The construction creates new witnesses
with at most `(2^n-1)^2` nodes and preserves all original descriptor equations.
It covers a recursive example for which no existing anchor selector works.
The predicate is finite and source-checkable, not proved for all Yulang
sources and not a rejection policy. One-sided/unbounded roots are outside
that conditional construction and are now covered by the full pure FMP
theorem above. Effects, arbitrary guards, joint predicates, principality and
full source adequacy remain open. Proof/review/check details are in
[the structural progress record](../notes/progress/2026-10-04-preclosed-structural-witness-review.md).

[Callback local abstraction](../notes/progress/2026-10-04-callback-local-abstraction-boundary.md)
now proves an explicit endpoint-only erasure obstruction: source-adequate
grounded ports for identity and a constant cannot both be inverted through
the exact identity recipe on a fixed singleton argument relation. This
refutes that factorization shortcut, not callback containment or current
production semantics. A locally saturated integer-body relation, with its
own result coordinate, gives a finite shared-generator lift for projected
first-order observations and independently admitted histories. Full-root
identity, latent values, higher-order inputs and identification with the
actual finite endpoint remain open. Independent review found no blocking or
major defect. The next production-bridge proof must locate each erased
dependency in a source-owned local relation or retain it in the complete
presentation; matching four ports alone does not supply exact source
factorization.

The callback observation-boundary question is answered and consumed in
[its receipt](../questions/2026-10-04-function-bound-value-observation/receipt.md):
use typed observations that forget concrete data-value identity/correlation
while retaining value types, typed events/requests, continuations, origins,
and the existing `nu,K,D` relations. This makes the projected scalar local
abstraction an eligible proof route, not a higher-order adequacy result. The
answer does not approve compiler implementation or update the governing
source design. An independent semantic review found the choice compatible
with Theorem C's stronger exact-observation transport, since a common
projection preserves its inclusion; it did not establish projection adequacy
for higher-order endpoints. The next callback proof must certify the
projection through latent descriptors, requests, resumed histories, and
query-independent challenge admission while retaining joint scopes,
authority-bearing evidence identities, and `nu,K,D`, then prove the domain
sandwich, actual-bound realization for every endpoint-admitted observation,
and checked-bound embedding. Compiler implementation remains unauthorized;
the source theorem package is Reviewed and conditional, while production
generation remains Draft.

## Active unrestricted proof gates

The test-only finite parent/use graph transport prototype is complete under
its narrow gate. It has independent substitution-reference tests and does not
change the production solver. The pure structural FMP gate is now closed by
the reviewed finite-fence theorem in
[`finite fence completion`](../notes/design/2026-10-04-structural-fmp-fence-completion.md):
every satisfiable normalized pure structural package has a permitted regular
model with at most `8^N` states, preserving exact descriptors, Record width,
Function variance, invariant coordinates, and rigid permissions. This closes
the arbitrary-package FMP and finite-quotient conflict-reflection gates; it
does not identify production source generation or coupled effects with that
pure package, and it grants no production cutover authority.

The structural playgrounds remain executable characterization evidence at
`tools/research_structural_feedback.py` and
`tools/research_gamma_quotients.py`. Beyond the fixed rank example, the
generated-package checker exhausts 495 one-Function/one-Int/one-free-root
packages with zero to two separate bounds against 449 labelled two-generated
monoids through size four (222,255 pairs). It independently validates all
27,383 conflict-free graph witnesses and differentially matches the fixed
example's ranks. The generated fragment does not itself establish unrestricted
FMP; that result comes from the separate reviewed theorem. Generalizing this
playground can validate the construction against arbitrary normalized
`Gamma_P^coh`, but it is characterization work rather than a missing theorem
premise. Callback bridge and principality playgrounds remain active lanes.
No production cutover authority follows from any playground or from the pure
FMP theorem.

**Callback direct follow-up: reference realization proved; production conformance open.**

The latest residual attack proves a finite transformation-certificate theorem
for whole membership and independent admission, and its Pure-value callback
corollary at the fixed complete old fiber. It covers every finite
latent/future/resumption history. Checked-admission dependencies remain in
that fiber; an additional hiding lemma proves marginal containment when
checked admission is constant across the forgotten fiber. A two-witness
countermodel shows why binding a hidden name once is insufficient by itself.
These results have independent compiler-referee/spec-auditor review, with
the hidden-admission finding repaired and its delta closed. Deriving the
decorated input and complete finite certificates from the selected production
generator remains open. See
[certified callback and constrained-use theorems](../notes/design/2026-10-04-certified-callback-and-constrained-use.md)
and the [residual attack record](../notes/progress/2026-10-04-callback-principality-residual-attack.md).

The experiment-guided follow-up strengthens the exact linked reference pair:
fresh total definitions can be eliminated with the old scopes and admission;
actual and checked bounds are equal on checked fibers. A legal old-witness
marginal preserves comparison iff every actual complete observation has a
checked-admitted representative (Coverage). A finite source dependency closure
derives a sufficient safe-hiding complement, including request/provider
production premises. The new checker exhausts 4,096 encodings and separates
uniform admission, same-witness admission and Coverage. A source-core
`higher` diagonal defeats independent stage marginals; a supplied scalar
selector defeats local representative substitution. Original joined witnesses
avoid both routes, but legal common descriptors and all-view direct-query
evidence remain open. Proof/review status is in
[the experiment-guided record](../notes/progress/2026-10-05-experiment-guided-main-gate-attack.md)
and [complete argument](../notes/design/2026-10-05-callback-coverage-and-source-joins.md).
The full callback/principal classification remains C; structural FMP remains A.
An additional executable `higher` source-core probe exhausts all 16
challenge/provider relations and shrinks the type-only stage-join error to two
diagonal rows; preserving the original returned-provider incidence restores
the exact projected source relation in every case. It characterizes the
reviewed §6.3 obstruction only and does not construct a production common
descriptor. Details are in the
[callback/principality playground record](../notes/progress/2026-10-04-callback-principal-playgrounds.md#higher-returned-provider-join-probe-2026-10-05).
An executable admission-dependency probe also checks the safe-hiding premise:
all 64 Boolean certificate assignments preserve admission when only the
transitive-closure complement varies. Omitting the exposed-request to
producer-proof edge shrinks to one `call_executed` bit that changes admission.
Production extraction of the dependency graph remains open; see the
[playground record](../notes/progress/2026-10-04-callback-principal-playgrounds.md#callback-admission-dependency-closure-probe-2026-10-05).
An executable B scheduler probe also covers four bounded Apply/literal cases:
expected context reaches Handler selection before body synthesis, independently
synthesized endpoints form the completed Function left operand, and the final
ordinary inequality is emitted once. A post-body role-selection mutant is
rejected, as is a mutant that drops completed effect ports. Parser/HIR
generation and port-evidence validity remain open; see the
[playground record](../notes/progress/2026-10-04-callback-principal-playgrounds.md#callback-b-role-first-scheduler-probe-2026-10-05).

The latest user request reopened direct proof work on callback and
principality after the pure FMP proof. The independently reviewed
[source-indexed reference construction](../notes/design/2026-10-04-source-indexed-callback-realization.md)
now gives finite endpoint membership/admission clauses and proves
`D_C^ref = D_GC ⊆ D_GA = D_A^ref` and
`P_A^ref = Pi[P_GA]`, `P_C^ref = Pi[P_GC]` on checked challenges.
Whole-observation typed projection preserves every finite latent/future-use
and resumption history. This closes the crosswalk for the constructed
reference interpretation, not for an independently chosen/current production
interpretation. Source generation and production membership conformance,
including the B literal's supplied decorations, remain real gates. See the
[proof/review follow-up](../notes/progress/2026-10-04-callback-principality-direct-followup.md).

A finite scope-aware checker now exhausts the old-tuple-preserving total
coordinate lift under `forall kappa. exists z`, including one captured `s`
outside that binder, and minimizes three mutations that move `s`, `z`, or
tuple-dependent `w` across it. This closes only that finite scoping
characterization; joint hiding across production segments and actual-side
membership factorization remain open. See the
[scoped-lift playground](../notes/progress/2026-10-05-callback-scoped-lift-playground.md).

An executable finite check now also covers the admission-uniform existential
hiding lemma from §4.1 of the certified-transport theorem: all 73 fixed-fiber
cases satisfying the uniformity premise project correctly. Without it, the
checker shrinks a valid countermodel to three domain memberships and one
actual observation. This validates the logical boundary only; production
certificate derivation and actual-side factorization remain open. See the
[admission-hiding playground](../notes/progress/2026-10-05-callback-admission-hiding-playground.md).

The reviewed value-only structural-shadow obstruction now also has a finite
executable witness: with identical `(Unit, Unit)` value shadows, Value entry
forces a request-bearing inert argument while an unused retained Computation
entry returns quietly. This supports keeping the complete Function query
separate from its pure structural shadow; it is not source execution or a
production inequality result. See the
[Function shadow playground](../notes/progress/2026-10-05-function-shadow-obstruction-playground.md).

The design and its current proof boundary are recorded in
[production callback endpoint generation](../notes/design/2026-10-04-production-callback-endpoint-generation-draft.md).
It specifies a bounded raw/HIR application node and lowering, B step 6 role-first
finite endpoint-generation rule, and the old-tuple-preserving total-coordinate
checked lift. It reuses source segments, operand tuples, binder scopes,
`nu,K,D`, occurrence/provenance, and existing Flow/Observe/path/subtraction
evidence; it adds no carrier. Theorem C applies only to the prebuilt Pure-value
path; inline literals keep the ordinary `F_lit <: F_cb` check.

An executable callback B trace audit now covers 192 bounded source/evidence
tuples and rejects nine deliberate owner/tuple/role/endpoint/occurrence/
attachment/row/query/path mutants. It assembles and queries the completed
four-port endpoint and validates required Force/CallView path selection.
Endpoint terms and selected occurrences are still inputs, so this validates
the finite trace audit only; it is not a production endpoint interpretation
or complete-bound checker. The full-bound realization factorization and
raw/HIR bridge remain open. Details are in the
[callback/principality playground record](../notes/progress/2026-10-04-callback-principal-playgrounds.md#callback-b-endpoint-trace-audit-2026-10-05).

The A/B scheduling invariant now has a separate executable solution-set probe:
[`research_callback_ab_solution_equivalence.py`](../tools/research_callback_ab_solution_equivalence.py)
exhausts 65,536 relation pairs over three independently synthesized binary
endpoint coordinates, retaining four distinct method/adapter/residual/evidence
witnesses per endpoint. Exact unary projection of the completed B solution set,
while retaining B's final joint query, preserves every tagged solution. A
seeded 2,048-case sample independently varies witness availability; a minimal
evidence-erasure mutant loses one of two same-endpoint alternatives. The
endpoint-copy mutant loses all four B witnesses at `(0,0,0)` against expected
`(0,0,1)`. These are finite relational scheduling characterizations, not a
production propagator or callback semantics proof. Details are in the
[A/B playground record](../notes/progress/2026-10-05-callback-ab-solution-equivalence-playground.md).

A new executable composition probe directly exercises the remaining
result-consumer seam: `Force(D) >>= rebind >>= body >>= consumer`, where each
stage may request, suspend, and resume. It differentially compares monadic
suffix propagation with an independent stage walker over 8,192 graphs and
87,264 observations. The model derives argument `d-`/`d+` and body/consumer
`b+` occurrence projections from one composed source trace, preserves the
outer/latent owners, receipts, binder scope, typed paths, and fixed `nu,K,D`,
and rejects minimized omitted-consumer and consistently projected Force-replay
mutants. An independent spec delta review closed the checker corrections.
This is still a finite source-composition characterization: stages have at
most one request, relation rows are supplied, and no production endpoint
membership or Theorem C inclusion is established. Details and exact scope are
in the [consumer-factorization playground](../notes/progress/2026-10-05-callback-consumer-factorization-playground.md).
The HIR-backed `id`/`zero` realization test enumerates 21 handled Force
histories of length zero to two, each with two possible values and two states.
It runs a designated consumer request from each callback's returned state and
resumes it into either next state, for 42 callback cases and 84 consumer
resumptions. The test checks result values, state flow, and exactly-once
callback receipt/Force/body entry. Consumer programs and request evidence
remain test inputs; it grounds the transition in retained HIR without emitting
a production consumer relation or Function endpoint. Compiler-referee review
found no issue in the bounded test. Exact scope is in the same record.

The production bridge is not proved or authorized for implementation. The
smallest Pure-path blocker is a full-bound realization crosswalk, not
exactness with respect to source execution. Let `D_A,D_C` and `P_A,P_C` be
production actual/checked challenge domains and complete bounds, and let
`D_GA,D_GC` and `P_GA,P_GC` be the corresponding source-generated Theorem C
objects. A sufficient bridge is
`D_C ⊆ D_GC ⊆ D_GA ⊆ D_A`, plus (1) for every `c ∈ D_C`, every
`O ∈ P_A(c)` has a finite `G_A` witness factoring through the existing
`J_arg`, entry/rebind, body,
designated result consumer, and `J_call` composition under the same full
tuple, scopes, `nu,K,D`, and occurrence evidence, and (2) every generated
`G_C` observation at `c ∈ D_C` embeds in `P_C(c)`. Theorem C supplies bound
transport on `D_GC`, which contains `D_C`, and the middle domain inclusion;
the production crosswalk would then establish `D_C ⊆ D_A` and
`P_A ⊆ P_C`, meaning `∀c ∈ D_C, P_A(c) ⊆ P_C(c)`. Its local primitive
relations may conservatively overapproximate their executions. No equality
among production bounds, generated relations,
and `Sem` is required. The still-open point is the actual-side membership
factorization: source execution simulation and `Sem_actual ⊆ P_actual` do not
account for arbitrary extras admitted by `P_actual`. Checked-challenge
admission must be generated independently of comparison success. The merged
scalar saturation proves only a projected first-order case and does not close
higher-order adequacy. The B-literal generation clause must independently
show that all three selected occurrences and witnessed attachments project
from the same source tuple before the ordinary query. The current HIR has no
Apply or inline lambda, and parser recovery plus this source/endpoint
realization remain conformance work. The design remains Draft; implementation
is unauthorized pending closure of this crosswalk premise and explicit
approval. No Yulang source counterexample or additional semantic choice has
been established. Earlier proof attempts and the exact repository evidence
remain in the linked value-entry and direct-main-gate progress records. The
current `id x = x` / scalar-body owner trace confirms that HIR and constraint
facts retain distinct source identities but do not yet define either a
complete bound-factoring relation or the projected `Sat_j` relation; see
[Lambda endpoint owners](../notes/progress/2026-10-04-lambda-endpoint-owner-trace.md).
An independent audit of the smallest Pure root, `id x = x`, narrows this to
the missing exhaustive Function-bound membership/admission clause: enumerate
all admitted finite typed observations under fixed `nu,K,D`, including
conservative endpoint extras, and decode each to scope-preserving retained
source/local-bound evidence. Execution supplies positive witnesses but cannot
exclude extras; ports, provenance, and closed-predicate freshening do not
define complete membership. The exact-source reference image cannot be assumed
as production semantics. No source counterexample or carrier insufficiency
was found. See the
[complete-root membership audit](../notes/progress/2026-10-05-source-indexed-function-realization-playground.md#independent-complete-root-membership-audit).
The remaining interpretation choice is on the local question board as
[`production-function-bound-membership/q1`](../questions/2026-10-05-production-function-bound-membership/question.md).
Only claims dependent on production actual-bound membership wait; the separate
principal-scheme lane and `P_ref`-only proof work remain authorized.

User-directed principal-scheme acceptance examples now cover `id`, `zero`,
`call`, `compose`, repeated calls, branches, and staged higher-order calls.
Frozen Oracle evidence is characterization only; the successor's compositional
principal-solution preservation proof remains open. Exact examples, Oracle
limits, and the remaining premise (a principal, representable common allowance
for every original solution fiber, with all valid views factoring through its
generalization) are in
[principal scheme criteria](../notes/progress/2026-10-04-principal-scheme-acceptance-criteria.md).
This turn's source-output-effect contributor shape is only a reviewed proof
candidate; its sort-specific paths and explicit same-fiber totality obligation
are recorded in
[the contributor-bound attempt](../notes/progress/2026-10-04-principal-contributor-bound-theorem.md).
An earlier formulation as direct inequalities from effect contributors to a
common output row is withdrawn: effect ports must be handled jointly inside
complete Function inequalities. The remaining candidate establishes no
source-to-endpoint rule and no implementation authority.
The annotation-free `compose` source behavior now has a conditional
derivation: when no capture contract is written, default full hygiene keeps
caller-owned observations in the complete `f` call along
`Force(D_g) >>= B_f`; its candidate Function contract places them in outward
`c`. Production endpoint projection and principal representability remain
unproved; details are in the contributor-bound attempt.
An exploratory Draft now records the candidate public spelling `'e?` for an
optional provenance edge from a capture-constrained input component to an
ordinary output component. It keeps row membership separate from provenance,
and treats capture authority as expiring at the source boundary. Existing
`Flow`/`Observe`, occurrence/incidence, `Rel_C`, `K,D`, directed-weight and
subtraction evidence are the candidate projection substrate; no concrete
failure showing a missing carrier is established. The edge quantifier,
principal order, and source-to-public projection theorem remain open, so the
note adds no semantic or implementation authority. Its **(B)** assessment is
exploratory. See [handler hygiene provenance notation](../notes/design/2026-10-05-handler-hygiene-public-provenance-notation.md).
An architect cross-check found no counterexample among the seven accepted
schemes and no demonstrated missing carrier. A direct Astra theorem attack,
independently reviewed by a compiler referee and architect, distinguishes the
ordered source-definition gaps: source rules still need to construct a complete
role-indexed Function view from the literal, annotation/expected boundary,
`P`, and `Result(I_body)`; only then can the abstract effect allowance be
interpreted as a correlated complete port view and fixed-fiber `Qξ(s,a)` be
defined. Thus `∀s∈Sξ. ∃a. Qξ(s,a)` is not proved. Annotation/callback-context
overlap remains unspecified. This is separate from the production callback
endpoint-realization crosswalk. Principal factorization requires
`∀V. ∃m_V`; the audits did not establish stronger uniform quantifier orders as
obstructions or find a counterexample. Full evidence and scope qualifications
are in the
[principal scheme criteria](../notes/progress/2026-10-04-principal-scheme-acceptance-criteria.md).
The latest reviewed
[safe context-preimage result](../notes/design/2026-10-04-common-allowance-context-preimage.md)
proves finite intensional forward amalgams and the exact domain-safe
image/preimage law. Positive forward relation construction does not in general
express the required universal condition; an explicit finite monotonicity
countermodel identifies that proof boundary. Common-allowance closure still
requires a legal descriptor realization for each original solution and an
admissible map for each independently valid public presentation, using the
existing complete Function query and source occurrence maps. The quantifiers
remain `∀s∈Sξ. ∃a. Qξ(s,a)` and `∀V. ∃m_V`. No source-scheme counterexample
or new descriptor semantics is asserted.

The further reviewed constrained-use theorem removes a separate
map-construction-calculus requirement: fresh-copy the whole finite
presentation, apply any supplied uniform descriptor graft, retain the client
constraint, and append one direct complete query at the actual designated
exported root. Its finite graph exists before solving. It preserves exactly
the client's full solution relation iff `C_V(v) => Ext_P(v)` for every public
assignment. Thus the remaining all-view gate is this entailment for every
independently valid `V`, alongside legal common-allowance totality. No general
explicit universal-preimage descriptor is required when the query is retained.
If the common descriptor replaces the exported source root, its witness must
also satisfy the direct root-to-`V` comparison; totality alone is insufficient.
The conditional retained-root corollary does not change any accepted scheme's
root. Source/query completeness and descriptor realization remain unproved;
classification is C. Full proofs, source applicability, and independent
reviews are in the linked certified-callback/constrained-use theorem and
residual attack record.
The direct formation audit narrows the first missing source clause: one legal
abstract effect descriptor must have a complete correlated view at every
original typed Function path, preserving the common `Rel_C` / `nu,K,D` fiber
while permitting path-specific challenge/value carriers. Existing linking,
joins, factor coverage, freshening, hiding, and grafting do not create that
descriptor interpretation. The `choose` unequal-branch witness rejects
endpoint equality only; it does not refute a common allowance. Whether the
formation rule follows from existing source semantics or requires a user
choice remains unverified. See the
[direct descriptor-formation audit](../notes/progress/2026-10-04-principal-contributor-bound-theorem.md#direct-common-descriptor-formation-audit-2026-10-05).

An executable contract-join probe now exhausts 65,536 two-stage cases with
separate Function-valued and Int-valued challenge projections. Typed pullbacks
retain the admitted source tuples and the closed concrete support union is
pointwise least; identifying the local challenge coordinates loses the
minimal admitted tuple `(fn0, 0)`. This checks the semantic contract join in
the finite concrete-support fragment only; it does not establish shared
descriptor realization, complete Function comparison, or `m_V` admissibility.
See [callback/principality playgrounds](../notes/progress/2026-10-04-callback-principal-playgrounds.md).
An additional finite callback probe checks the higher-order boundary of the
approved typed observation projection: an identity callback returning a
callable followed by one future invocation. Two same-interface callable
owners stay distinct with their request origins and continuations. Of four
candidate endpoint owner sets containing the source owner, all and only sets
with an extra owner fail full-observation factorization; erasing authority
labels creates two false greens. This concretely blocks generalizing the
integer `Sat_j` abstraction across callable values without preserving source
ownership. It is not evidence that production admits extra owners and does not
close higher-order endpoint denotation. Reviewed with one minor terminology
repair and focused rerun; see
[callback/principality playgrounds](../notes/progress/2026-10-04-callback-principal-playgrounds.md).
An annotation-free `compose` probe now exhausts 128 finite `Force(D_g)` request
cases under the fixed same-fiber Value-entry bind, covering operation kind,
all two-value/two-state response relations, and inner handler operation sets.
Pending and resumed traces preserve their exact request/fiber/path and
response/live-state pairs; without an explicit capture contract, the `g`
request remains in outward `c` even when `f` handles that operation. A mutant
that subtracts on shared printed component `b` loses the contribution in 64
cases; the minimum is one pending `Read`. This is a source-order/hygiene
characterization, not a full Function comparison or principal-scheme proof.
An independent compiler-referee review found no major issue; after adding its
requested resumed-state assertions, the focused checker and `py_compile` pass.
Details: [callback/principality playgrounds](../notes/progress/2026-10-04-callback-principal-playgrounds.md).
The checker now also enumerates 95 ordered zero-to-two-request prefixes,
including each possible pending boundary and all completed response/state
choices, under four handler sets (380 assignments). Repeated operations keep
distinct source event IDs while projecting to one covariant support point; the
88 explicit resume transitions match independent whole-prefix reconstruction,
preserving the updated state, completed event exactly once, and remaining
Force suffix. Support includes the full finite sequence, including requests
latent in the pending suffix. The component-match subtraction mutant loses
support in 230 assignments. A deliberate replay mutant shrinks to one pending
`Read` and duplicates its event ID; the checker rejects it. This remains a bounded
source-order model and does not close general request semantics,
Function-bound realization, or principality. See the same
[playground record](../notes/progress/2026-10-04-callback-principal-playgrounds.md).
The latest user clarification accepts `Top -> int` for `zero`, with `any` as
the surface notation, superseding the earlier `'a -> int` criterion. The prior
negative-only quantification analysis is retained as history but creates no
successor generalization requirement. The full coupled Function/effect
solution-family proof remains open; see the updated
[principal scheme criteria](../notes/progress/2026-10-04-principal-scheme-acceptance-criteria.md).
The current HIR/F5 collector does not yet admit the application, block, and
branch forms in `call`, `compose`, `twice`, `choose`, or `higher`; the listed
schemes are successor criteria, not current production outputs. The exact
source-generation boundary is recorded in the principal-scheme criteria.
Two isolated characterization models now exercise narrower pieces of the
open callback/principality gates: the callback lift checker preserves old
tuples and distinct `d-`/`d+`/`b+` identities under total-coordinate extension,
exhaustively checks 65,536 bind-shaped relation pairs under two metadata
contexts, with shared intermediate coordinates, and finds minimal bad-join
witnesses both with and without a nonempty exact composition; the
principal-support checker verifies finite common-support factorization while
keeping occurrence endpoints distinct. A separate point-row matcher retains
the conditional disjunctive alternatives through two independent fresh uses
and a correlated receiver restriction; its eager-match mutant loses all four
surviving assignments. A three-use, three-class extension checks 2,187
assignments and finds 108 under a joined client constraint; direct witness
search agrees, while eager-left matching loses all 108. These models still do not represent source constructors,
complete Function comparison, subtraction attachment, or the full
generalization theorem. Exact counts and limits are in
[callback/principal playgrounds](../notes/progress/2026-10-04-callback-principal-playgrounds.md).
The separate Value-entry probe executes the selected finite Return/Request
bind equations for `receipt; Force(D) >>= (v => RebindResultPath; B(v))`; it
checks a same-request continuation resumed under two live states and finds the
one-request ordering difference caused by eager force-before-call. It does not
model endpoint denotation, general owner reactivation, or full Handler dispatch.
The new scalar callback-lift probe combines finite `Sat_j` output abstraction
with the checked total-coordinate extension over 548 Force graphs, including
all one- and two-request response subsets. Exact identity/literal observations
embed; an equality mutant loses 2,116 abstract observations, including the
one-request witness `input 1 -> response 1 at state 0 -> abstract result 0`.
This is bounded scalar characterization only and does not close the production
callback bridge. Details and omitted space are in
[callback/principality playgrounds](../notes/progress/2026-10-04-callback-principal-playgrounds.md).
For the specified `compose f g x = f (g x)` case, `g`'s effect contribution
remains in outward `c` because the annotation-free source gets full hygiene;
reusing its inferred component at `f`'s argument port is not a written capture
contract. Existing witnessed partial subtraction inside `f`'s contravariant
descriptor remains governed by its current attachment evidence.

Historical callback adequacy exploration and its earlier gate descriptions
remain in the linked progress records above and
[callback compositional premise](../notes/progress/2026-10-04-callback-compositional-premise.md).

**Other open gates:**

- **Structural solving / Milestone 3:** regular-witness existence for the
  normalized pure package is now closed by finite fence completion, including
  shifted descriptors and variance/width-directed descent. The finite
  constrained residual presentation, principal/effective projection and
  production source/effect correspondence remain distinct obligations.
  An isolated finite checker now compares direct structural satisfaction with
  open-head residual normalization over 2,025 endpoint pairs (1,800 contain
  variables), then carries 2,048 generated joint packages and supplied finite
  `Phi` relations through exact solution and coordinate-projection checks.
  Its shrunk wrong-variance mutant confirms sensitivity to Function
  contravariance. This is acyclic bounded characterization only; recursive
  residual SCCs, interpreted scope guards and `nu,K,D`, structural projection,
  source-context finiteness, effective principal projection and production
  acceptance remain open. See the
  [residual-factorization playground](../notes/progress/2026-10-05-residual-factorization-playground.md).
  A five-path synthetic guard probe checks 32 path-permission masks and
  distinguishes `GuardFailure` from structural mismatch. It found a concrete
  failure-precedence obstruction: an earlier deferred Function-argument
  residual can fail its guard before a later known result mismatch, so a
  fail-fast normalizer loses the direct comparison outcome. The checker now
  retains ordered obligations and matches direct outcomes in this bounded
  family. Resetting the immutable context at an open Record residual still
  fails its one-Function/one-Record-field mutation witness. These probes test
  context-carry and failure-order sensitivity only; they do not establish
  production guard finiteness or lexical-scope semantics. See the
  [guard-context probe](../notes/progress/2026-10-05-residual-guard-context-playground.md).
  A further recursive-graph checker compares direct greatest-fixed-point
  subtyping against finite residual normalization: it exhausts 32,400 checks
  over a selected shallow endpoint graph and adds 15,360 seeded checks over
  bounds with up to four reachable nodes, including 133 cyclic bounds. Review
  caught and helped repair two checker defects (assignment-edge offsets and
  reflexive-only generated endpoints); the repaired model includes a separate
  recursive-copy rejection assertion and a cyclic bound with both satisfying
  and failing assignments. Its joint extension also checks 192 one-to-three-
  bound packages under supplied finite Phi masks (2,688 admitted assignments,
  including 105 cyclic packages) with exact shared solution and separate
  coordinate-projection equality. A two-bound witness confirms each bound can
  have a Phi-admitted marginal while no shared tuple satisfies both; dropping
  Phi admits a spurious tuple. This Phi is synthetic and does not represent
  source-derived production `K,D`. Scope guards, effect ports, source generation,
  and effective principal projection remain open. See the
  [recursive residual playground](../notes/progress/2026-10-05-regular-residual-factorization-playground.md).
  The direct MSO route is still invalid, and standard ranked exact-shape
  subtyping does not directly encode mandatory Record width. Historical
  bounded results and failed scoped encodings are recorded in
  [open residual design](../notes/design/2026-10-03-open-residual-factorization.md),
  and a source-checkable conditional closure for the closed monomorphic
  pure lambda/integer fragment with empty input Record alphabet is now proved:
  when structurally satisfiable in the regular graph domain, that fragment's
  generated packages have a regular witness of at most `N+1` nodes, by §7.4.1
  erasure and rational quotienting. A separate
  induction proves the candidate generator emits only `Int`/Function
  descriptors for this fragment. This is not a theorem for authoritative
  complete Yulang generation: the candidate source rules' arbitrary preorder
  is not identified with the structural graph carrier, and callbacks,
  annotations, imports, effects, records and guards are outside the fragment.
  The source-fragment result and exact boundaries are in
  [empty-Record source fragment](../notes/progress/2026-10-04-empty_record_source_fragment.md).
  A separate audit now proves the same `Λ = ∅` incidence premise for the
  current error-free production HIR's monomorphic **structural value shadow**:
  resolved integer/name leaves and one-atom unannotated lambdas generate only
  Int/Function equations, with no structural inequalities or rigid names.
  Theorem S then gives a regular witness whenever that shadow is satisfiable.
  This is not an equivalence theorem for current F5's polarized four-port
  Function constraints: even `id x = x` generates a directed Function fact
  with coupled effect components. The theorem therefore applies to the named
  source shadow, not actual production constraints. Bridging those facts
  without losing effect correlation remains open; callbacks, Records, and
  complete successor generation remain outside it. See
  [production HIR empty-Record shadow](../notes/progress/2026-10-04-production-hir-empty-record-shadow.md).
  The smallest concrete source/solver bridge is pinned to `id x = x`:
  typed-core gives `Value(Fun(Value(A),Comp(empty,A)))`, while F5 creates a
  four-port Function fact plus polarized body/lambda effect bounds. Prove the
  intended source-interface adequacy of that endpoint before lifting any
  callback theorem; Oracle materialization is not the proof. The value-port
  projection does match for this identity: one F5 quantifier is shared by its
  negative argument and positive result ports, just as typed-core shares `A`.
  The actual body-effect occurrence and its polarized bounds suffice for
  F4's local `SolvedEffect::Empty` projection. F5c summary nodes omit effect
  ports, but the post-solve `ConstraintStore` still retains the original
  Function term, effect constraints, and provenance, so a parallel carrier
  is not justified. The missing item is the semantic transport from that
  existing linked evidence into the source Function view; effect-port
  denotation, full bound inclusion, and callback domains remain open. A
  separate source-case proof establishes the local projection correspondence
  for the current error-free lambda body fragment (`Result(Value(A))` and F4
  both report empty effect), without equating polarized bottom to an effect
  row. For every complete lambda body currently accepted by HIR,
  `LambdaRecipe` and the retained store preserve the exact row-term link from
  body-effect facts into the Function result-effect child, so no parallel
  carrier is needed for this grammar. The denotation/full-bound proof remains
  open; see the same progress record.
  A source-generation theorem now covers the actual F5 value-skeleton
  projection for the full current error-free binding HIR grammar (integer,
  alias, and one-parameter lambda with integer, own-parameter, or resolved-
  name body), provided every cross-SCC `DefinitionUse` targets an alias chain
  ending in an integer binding. The finite HIR/SCC check establishes the
  grounded or one-open-anchor condition after actual internal and restricted incoming
  routes; Theorem S gives a regular witness whenever the projection is
  satisfiable. Arbitrary structured incoming schemes remain outside this
  source theorem. It still omits Function effect children only as a projection
  and does not prove full-package satisfiability, source-interface adequacy,
  effect denotation, principality, or successor correctness. See
  [full-HIR value-skeleton incidence theorem](../notes/progress/2026-10-04-production-f5-value-skeleton-hir-incidence.md)
  and its narrower predecessor
  [selector theorem](../notes/progress/2026-10-04-production-f5-value-skeleton-selector.md).
  The useful source-checkable premise isolated from failed unrestricted
  searches is one-anchor incidence: after actual projection/routing and
  normalization, each retained inequality stays within one free/free
  component or connects it to its sole descriptor anchor, with constructor-
  guarded child references. This is not a restatement of regular-witness
  existence. Simultaneous redirection proves a finite regular witness; Theorem
  S remains within its original signature. A separate HIR/SCC check now
  establishes this premise for cross-SCC targets that are integer-ending
  alias/ignored-parameter-lambda chains, alias chains ending at an own-
  parameter identity lambda, or alias-only cycles. The identity target's
  generated `forall q. Function(q,q)` scheme contributes one open anchor;
  cycle targets contribute no value inequality in the existing incoming
  route. Existing F5 `Top` is preserved only as an opaque proof token, without
  assigning semantics to polarized `Bottom` or `Top`. This source criterion
  is sufficient, not claimed absolutely weakest.
  Arbitrary schemes, effects, and full Function adequacy remain outside it; see
  [identity-scheme incoming extension](../notes/progress/2026-10-04-identity-incoming-incidence-extension.md).
  Those incidence results close their conditional structural witness theorem;
  full pure structural regularity is now supplied separately by FMP. Source
  adequacy, principal solutions and the overall inference-replacement objective
  remain open. Theorem S above separately proves
  arbitrary-to-regular reflection with nonempty Records and open recursive
  anchors under its finite incidence and rigid-scope predicates. Multiple
  distinct anchors in a component with an open anchor remain outside that
  theorem. See also
  [root-only result](../notes/progress/2026-10-04-root-only-regular-witness.md),
  [queue probes](../notes/progress/2026-10-04-fixed-descriptor-queue-encoding.md),
  and [direct main-gate attacks](../notes/progress/2026-10-04-direct-main-gate-attacks.md).
  A new finite selector-certificate theorem strictly extends the one-open-
  anchor witness construction when an existing anchor satisfies every
  incident directed bound after redirection. It handles multiple compatible
  open anchors; finite selector enumeration plus coinductive simulation gives
  a terminating positive recognizer. A second
  example shows it is still only sufficient, since a satisfiable package can
  require a fresh constructor graph outside the anchor choices. The current
  HIR structural value shadow satisfies the selector premise in the stronger
  no-directed-bound case.
  This does not bridge the actual F5 four-port Function constraints. Details
  are in [multi-anchor selector witness](../notes/progress/2026-10-04-multi-anchor-selector-witness.md).
  A fixed product encoding with global `Top` is proved exact on its recursive
  source image; the attempted NPS decision transfer stops because inverted
  prefix modalities for shifted descriptors do not enforce the ordinary
  suffix-child source-image grammar. This is a failed proof route, not a
  counterexample to regular completion.
- **Pure structural existence is closed:** the reviewed finite-fence theorem
  proves arbitrary-tree satisfiability iff regular satisfiability iff a model
  exists on some finite surjective monoid quotient of the complete `Gamma_P`.
  Therefore a free-conflict-free package has a simultaneous regular extension
  of its domain, head, presence and original activation facts. The fixed-package
  conflict-reflection statement and conditional cofinal rank bound (BR) follow.
  Exact recursive descriptor sharing, mandatory width, Function variance,
  invariant coordinates and arbitrary permission sets are included; arbitrary
  `Guard`, `Phi/K,D`, effects and optional Records remain outside the theorem.
  The old representative, information-meet, local-signature, and empty-side
  constructions still fail as recorded. Those examples remain regularly
  satisfiable and do not refute FMP. The new construction uses seven finite
  fence distances to all original terms, selected-field landmarks, and exact
  successor profiles; it does not exchange `forall k exists mu` with
  `exists mu forall k`. Proof and independent certification are in
  [finite fence completion](../notes/design/2026-10-04-structural-fmp-fence-completion.md)
  and [its progress record](../notes/progress/2026-10-04-structural-fmp-proof.md).
  The historical attempts remain in the direct-main-gate and finite-feedback
  records. No extra source premise, carrier, rejection rule or compiler
  implementation is selected by this theorem.
- The standard guarded-BPA undecidability result does not directly settle
  this gate: it requires transparent parameter-changing recursive type
  constructors, which current type-declaration authority does not establish;
  its constructed unfolding can be non-regular. The exact mismatch is now
  mapped against the finite descriptor graph: the BPA reduction needs a
  recursive definition to act on arbitrary changing type arguments, while
  current descriptor edges retain fixed graph references. This rules out
  only that direct transfer. The separate finite-fence theorem now settles
  regular completion for the current finite descriptor fragment. See
  [BPA transfer audit](../notes/progress/2026-10-04-bpa-recursive-constructor-transfer-audit.md).
- **Source State/reference bridge:** derive dynamic ownership, read/update
  replacement, captured access, and repeated resumption; the `start!` fixture
  fixes only one observation:
  [State bridge record](../notes/progress/2026-10-04-local-state-capture-observation.md).
  A bounded executable probe now checks 512 visible-alias/update configurations
  under a clearly marked candidate live-store/restart model and minimizes
  capture-by-value and static-ID/runtime-cell conflation mutant failures. This
  is characterization only: source equations for update/restart and captured
  re-entry remain absent. See
  [restart playground](../notes/progress/2026-10-05-local-state-restart-playground.md).
- **Global source bridge/lifecycle:** first-class-reference/import realization,
  complete `EnvStore`/`JointWF`, source-wide acceptance/principality, and
  generalization/SCC lifecycle remain open.

The conditional results do not close these unrestricted gates or authorize
compiler implementation.

## Governing designs and preserved history

- [SCC-intrusion redesign charter](../notes/design/2026-09-29-scc-intrusion-redesign-charter.md)
- [Scoped constraint solving](../notes/design/2026-10-03-scoped-constraint-solving.md)
- [Finite bound/replay closure](../notes/design/2026-10-03-finite-bound-replay-closure.md)
- [Source context finite closure](../notes/design/2026-10-03-source-context-finite-closure.md)
- [Ordinary computation semantics](../notes/design/2026-10-02-ordinary-computation-semantics-package.md)

Prior investigations, counterexamples, reviews, and handoffs remain in
[`notes/progress/`](../notes/progress/) and the
[pre-compaction chronological ledger](../notes/progress/2026-10-04-task-ledger-before-compaction.md).
This summary changes no design status, authority, or historical user decision.
