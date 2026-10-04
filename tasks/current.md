# Current task: replace Yulang type inference with SCC-intrusion inference

Updated: 2026-10-04. Branch: research/simple-sub-intrusion.

## Objective and authority

Prove the SCC-intrusion successor sound, principal, and compatible with
Oracle's final well-typed-program capability on the supported envelope, then
implement the fully reviewed and approved inference machine. This objective
remains active; compiler implementation is not authorized yet.

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
The HIR-to-core bridge now closes for its monomorphic pure-value fragment:
integer/name leaves and unannotated parameterized bindings map to finite
`literal`/`name`/`lambda(P,result(body))` derivations under a fixed `Gamma`.
This includes `id x = x` with `P=Value(A)`. Applications, callback call sites,
and whole-carrier evidence remain unavailable in this HIR.

## Latest main-gate results

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
sources and not a rejection policy. One-sided/unbounded roots, effects,
arbitrary guards, joint predicates, principality and full source adequacy
remain open. Proof/review/check details are in
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

**Callback adequacy proof search is complete; active gate is production design.**
The design and its current proof boundary are recorded in
[production callback endpoint generation](../notes/design/2026-10-04-production-callback-endpoint-generation-draft.md).
It specifies a bounded raw/HIR application node and lowering, B step 6 role-first
finite endpoint-generation rule, and the old-tuple-preserving total-coordinate
checked lift. It reuses source segments, operand tuples, binder scopes,
`nu,K,D`, occurrence/provenance, and existing Flow/Observe/path/subtraction
evidence; it adds no carrier. Theorem C applies only to the prebuilt Pure-value
path; inline literals keep the ordinary `F_lit <: F_cb` check.

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
An architect cross-check found no counterexample among the seven accepted
schemes and no demonstrated missing carrier. Their per-example evidence and
remaining proof parts are now listed in the criteria record. The smallest
shared open premise remains a source-generated principal common-allowance
extension over each full `ν,K,D` solution fiber, followed by factorization of
every valid public view through generalization.
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
For the specified `compose f g x = f (g x)` case, `g`'s effect contribution
remains in outward `c` because the annotation-free source gets full hygiene;
reusing its inferred component at `f`'s argument port is not a written capture
contract. Existing witnessed partial subtraction inside `f`'s contravariant
descriptor remains governed by its current attachment evidence.

Historical callback adequacy exploration and its earlier gate descriptions
remain in the linked progress records above and
[callback compositional premise](../notes/progress/2026-10-04-callback-compositional-premise.md).

**Other open gates:**

- **Structural solving / Milestone 3:** the finite constrained residual
  presentation remains distinct from regular-witness decidability and
  principal/effective projection. The exact existence boundary is regular
  completion when descriptor equations prefix-shift addresses while active
  comparisons descend suffixes with variance and Record-width conditions.
  This remains open; it is not an undecidability result. The direct MSO route
  is invalid, and standard ranked exact-shape subtyping does not directly
  encode mandatory Record width. Bounded results and failed scoped encodings
  are not general impossibility:
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
  This closes only the conditional structural witness theorem, not general
  structural regularity, source adequacy, principal solutions, or the overall
  inference-replacement objective. Theorem S above separately proves
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
- For the normalized pure structural fragment with finite rigid permissions,
  the arbitrary-tree closure can be inconsistent only with a finite Horn
  conflict. The remaining exact premise for a regular decision procedure is
  that every conflict-free least closure has a simultaneous regular extension
  for domain, head, and original-bound activation facts. This is unproved and
  excludes arbitrary `Guard` and `Phi/K,D`; see the direct main-gate record.
  A direct finite-fold pumping attempt fails because quotienting addresses
  can combine activation and field-presence premises from different
  occurrences; closure after folding may create conflicts absent before the
  fold. No instance defeating every regular extension is known.
  Equivalently, the remaining theorem asks for a regular activation invariant
  `A` with `A₀ ⊆ A`, `G(F(A)) ⊆ A`, and conflict-free `F(A)`, where `F` is
  forced domain/head saturation and `G` is the existing width/variance
  descent. The circular dependency is now explicit: descent decides heads
  through shifted descriptors, while heads decide descent. Safe regular
  activation invariants are not union-closed: two individually safe choices
  can force incompatible heads when combined. Thus a regular-extension proof
  must select one joint invariant. They are intersection-closed, but infinite
  intersections can be nonregular even for a fixed package, and the package
  may still have a trivial regular witness. Neither closure property supplies
  the required invariant. Equivalently, the unresolved finite-model property
  says every satisfiable complete address package has a model over some
  finite monoid quotient preserving shifted descriptor prefixes, structural
  suffix descent, and all coherence, activation, and permission clauses.
  Regular solutions give such quotients and quotient models lift back to
  regular solutions, but the finite-model property is unproved and has no
  counterexample. Finite quotient enumeration plus finite Horn-conflict
  witnesses decides regular satisfiability only if this property holds; see
  the exact statement in the direct main-gate record. An independent
  meet-closure theorem rules out aperiodic Wang reductions whose same-package
  solutions realize every translate and whose finite-depth decoder commutes
  with a shared-scaffold information meet. A separate marker-provenance
  invariant shows that prefix stripping plus structural suffix descent alone
  cannot renew the unary head/presence marker needed by a direct two-sided
  counting gadget; activation feedback remains unexcluded. Neither result
  proves FMP or refutes it. A concrete `Y=Fun(Y,{f:Int})`, `X <: Y` example
  refutes regularizing one arbitrary solution by a descriptor-monoid meet:
  literal subtree meets break child coherence, while a coherent local
  head/mask fold removes a field required by the original bound. The package
  itself has the regular witness `X=Y`, so FMP remains open. A synchronized
  local-signature representative fold also fails to preserve
  `q=Fun(X,X)`'s shifted shared-root equation, despite that package already
  having a regular witness; this refutes that reconstruction step only. The
  direct record has the exact paths and independent review.
- The standard guarded-BPA undecidability result does not directly settle
  this gate: it requires transparent parameter-changing recursive type
  constructors, which current type-declaration authority does not establish;
  its constructed unfolding can be non-regular. The exact mismatch is now
  mapped against the finite descriptor graph: the BPA reduction needs a
  recursive definition to act on arbitrary changing type arguments, while
  current descriptor edges retain fixed graph references. This rules out
  only that direct transfer, not the open regular-completion theorem or other
  reductions. See
  [BPA transfer audit](../notes/progress/2026-10-04-bpa-recursive-constructor-transfer-audit.md).
- **Source State/reference bridge:** derive dynamic ownership, read/update
  replacement, captured access, and repeated resumption; the `start!` fixture
  fixes only one observation:
  [State bridge record](../notes/progress/2026-10-04-local-state-capture-observation.md).
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
