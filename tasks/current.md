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

## Active unrestricted proof gates

**Next gate — unrestricted Pure-value callback/Function theorem.** Establish whole-carrier
admission/domain inclusion, endpoint/profile and linked-contribution adequacy,
and observation-bound inclusion across legal histories. Reuse existing
`Rel_C`, `K,D`, paths, receipts, occurrence/incidence, `Flow`/`Observe`, and
subtraction evidence. Do not add a carrier/API or independent port-subtyping
rule without identifying a concrete unrepresentable fact and obtaining
authority. Detailed clauses and conditional results:
[value-entry bind/projection](../notes/progress/2026-10-04-value-entry-bind-projection.md).
The direct main-theorem attack confirms one owning gate: source-to-endpoint
adequacy for the original role-indexed Function query. It must construct
checked-challenge admission independently of query success and establish both
`D_checked ⊆ D_actual` and full observation-bound inclusion. Even granting
equal domains and execution correspondence for a stateless terminating Pure
identity, execution coverage does not prove that every observation admitted
by the actual endpoint bound factors through the existing argument/body/result
composition and linked view. The exact missing bound premise and its minimal
logical countermodel are in
[direct main-gate attacks](../notes/progress/2026-10-04-direct-main-gate-attacks.md).
The source reference `Sem` is already the exact collecting relation; endpoint
presentations `P_i` may conservatively cover it. The missing proof concerns
factorization of that presentation's full bound, not choosing a new meaning
for `Sem`. This is not a Yulang program counterexample, State exclusion does
not close the bound gap, and no carrier or semantic choice follows.
The exact owner is compositional inversion of the synthesized Function
endpoint: core §6 yields only the `Fun(P,Result(I_body))` skeleton, while
§§3/9 give invocation execution without a rule deriving the complete-call
endpoint bound from it. The required theorem must recover argument-entry
admission and factor every endpoint-bound observation through argument,
rebind, body/result consumer, and `J_call` into linked `[b,d]` at the same
`ν,K,D`; callback B step 6 leaves this construction open.
The failed callback proof now has a compact source-checkable premise relative
to its compositional induction: independent challenge admission, constructor-
local witness lifting (including conservative local slack), and faithful
composition into the complete endpoint with the existing linked `d⁺`/`b⁺`
components. The bounded first-order Value-entry theorem follows by finite-
history induction. The common argument endpoint is one checkable way to
establish admission in that fragment, not an adaptation equality rule. This
condition is not claimed weakest among all possible proof contracts. Typed-
core §9 separately proves the operational source graph's composition shape
by induction over finite derivations. It does not prove the still-unspecified
finite inference endpoint satisfies admission or local lifting. B step 6
therefore remains the one missing finite-generation bridge; see
[callback compositional premise](../notes/progress/2026-10-04-callback-compositional-premise.md).
An attempted source-checkable constructor condition (compose only existing
entry/body/result segments, with no independent call-bound leaf) is not yet
sufficient: conservative slack on segment bounds still requires a proved
monotonicity transport for latent and resumed witnesses. Shared descriptor
identity also does not prove query-independent challenge admission. That
weaker condition remains rejected in the direct main-gate record. Theorem C
above closes its explicitly constructed generator's conditional claim by a
proved conservative extension and local admission rules; the unrestricted
source-to-endpoint correspondence and arbitrary target annotations remain
open.
The canonical exact semantic embedding in adequacy §4 does not supply this:
§3 permits any conservative `P` covering `Sem`, without defining or
identifying the syntax-generated Function endpoint. Exactness is unnecessary;
the missing premise is its same-fiber compositional factorization. The
non-authoritative coupled-effect draft's candidate Function contract quantifies
over well-typed contextual calls, but the call-domain choice remains open;
program-reached calls are vacuous for unused exports, while arbitrary runtime
states include configurations no typed source context can construct. I asked
which call domain should govern before deriving Function adequacy from that
candidate; its finite principal presentation remains a separate open proof.

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
  A further source-generation theorem applies Theorem S to the actual F5
  value-skeleton projection for integer bindings and one-parameter lambdas
  whose body is an integer or their own parameter. Integer roots have only
  closed `Int` anchors; each lambda root has one open positive Function
  anchor. Existing F5 Function terms and their correlated effect constraints
  remain intact; the result is not a full-package satisfiability or
  source-interface theorem. See
  [F5 value-skeleton selector theorem](../notes/progress/2026-10-04-production-f5-value-skeleton-selector.md).
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
  itself has the regular witness `X=Y`, so FMP remains open; see the direct
  record.
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
