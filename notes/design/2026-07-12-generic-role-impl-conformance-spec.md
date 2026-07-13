# Generic role impl conformance specification

Date: 2026-07-12

Status: feasibility and implementation design for source-level conformance checking of generic
role implementations. No implementation is approved or started by this document. The three open
soundness reports that motivated it are:

- `notes/bugs/2026-07-12-role-impl-explicit-associated-conformance-gap.md`;
- `notes/bugs/2026-07-12-function-result-annotation-conformance-gap.md`;
- `notes/bugs/2026-07-12-struct-field-type-conformance-gap.md`.

The first report is the primary scope. The other two are included to decide which proof machinery
can be shared; they are not folded into the same implementation stage by assumption.

## 1. Purpose

A role implementation is a generic claim, not a request to infer a narrower candidate.

```yu
impl Index (box 'a) int:
    type value = bool
    our c.index i = c.item
```

The source claim is conceptually:

```text
for every 'a:
    box 'a implements Index int
    associated value is exactly bool
    index has the role requirement specialized with value = bool
```

The current lowering represents `'a` as a flexible inference variable. If the explicit associated
type is merely connected to the method requirement, the constraint machine may narrow `'a` to
`bool` rather than reject the universal claim. A concrete experiment produced:

```text
box(int <: int & bool) -> int -> int
```

That is not conformance checking. It mutates the meaning of the impl head to make the body fit.

This document specifies the properties required of a real conformance boundary, compares three
implementation directions, proposes staged work, and lists decisions that remain unconfirmed.

## 2. Current pipeline and the missing proof boundary

### 2.1 Candidate registration

`BodyLowerer::register_role_impl_candidate` currently:

1. parses the impl head and role description into one `AnnTypeBuilder` scope;
2. creates `candidate_associated_anns`, using an explicit source type where present and a role
   associated variable otherwise;
3. separately creates `requirement_associated_anns`, always using role associated variables;
4. lowers the candidate head and candidate associated values into a raw `RoleImplCandidate`;
5. inserts that candidate into the mutable role impl table before method bodies are lowered;
6. stores the separate requirement-associated signatures in `RoleImplLoweringContext`.

The explicit associated assignment and the role method requirement therefore do not meet.

### 2.2 Method checking

For each method, lowering does perform useful checks:

- the receiver is connected to the impl target annotation;
- argument and result shapes are compared with the role method requirement;
- body values and effects are constrained against requirement uppers;
- residual role predicates are collected as impl prerequisites;
- the method is generalized into a scheme.

These checks use the separately inferred associated variable. They prove that the body can satisfy
*some* associated result, not the explicit associated result written on the impl.

### 2.3 Candidate finalization

After analysis settles, `AnalysisSession::finalize_poly_role_impls` clones candidates into the poly
arena. It does not validate method schemes against the candidate declarations. The candidate may
already have participated in role resolution for later definitions in the same source set.

### 2.4 Downstream accidental rejection

When a malformed candidate is selected at a concrete use, specialize may see both the declared
associated type and the implementation result and report a `ConflictingTypeCandidates` error. This
is not an acceptable source type check:

- it occurs only when the impl is used concretely;
- it reports an internal slot rather than the impl declaration;
- an unused malformed impl remains accepted;
- it is not an invariant promised by lowering or artifact construction.

## 3. Terminology and binder model

For one role impl declaration define:

- `U`: universal binders introduced by the impl head and its explicit source type variables;
- `A_exp`: explicit associated assignments, each a type expression closed over `U` plus permitted
  global concrete definitions;
- `A_inf`: omitted associated assignments represented by impl-local inference variables;
- `P_impl`: prerequisites advertised or inferred for the candidate;
- `M_i`: the generalized implementation scheme for method `i`;
- `Req_i[U, A]`: the declared role method requirement after substituting the impl inputs and the
  settled associated assignments;
- `P_i`: residual predicates required by `M_i`.

`U` must not be narrowed while proving conformance. It may be alpha-renamed, but occurrences that
refer to the same source binder must remain the same symbolic binder everywhere in the impl head,
associated assignments, prerequisites, and methods.

`A_inf` has a different lifecycle. It is inferred from all relevant methods and then frozen as one
candidate-level witness. It must not be treated as universal merely because its current
representation is a `TypeVar`.

## 4. Required conformance invariant

For every method implementation, the compiler must prove a relation of the following form without
adding facts that narrow `U`:

```text
U universal
A = A_exp ∪ settled(A_inf)

P_impl entails P_i
M_i is a valid implementation of Req_i[U, A]
```

The intended value-type direction is implementation-to-requirement subtyping:

```text
M_i <: Req_i[U, A]
```

This direction still requires normal function variance: parameters are checked contravariantly,
results covariantly, and invariant constructor arguments in both directions. Effect and stack
components must follow their existing variance and subtraction rules.

Associated assignment itself is definitional rather than merely covariant. `type value = X`
declares the candidate's associated result to be `X`. Method positions using `value` inherit the
variance of those positions, but candidate export may not rewrite `X` to a narrower type to make a
method pass.

Passing conformance must imply all of the following:

1. no member of `U` gains a new lower/upper bound as a consequence of validation;
2. every explicit associated occurrence in a role requirement refers to its source declaration;
3. the same `U` occurrence is compared as the same binder, not as an unconstrained wildcard;
4. method-local quantifiers may be alpha-renamed independently;
5. method-local quantifiers do not escape into candidate head or associated assignments;
6. residual method predicates are entailed by candidate prerequisites or are rejected;
7. recursive bounds and stack quantifiers are compared under their declared binder scopes;
8. a failed impl cannot be exported in a successful compiled unit.

## 5. Why ordinary subtype connection is insufficient

The normal constraint machine is designed to infer a principal solution from flexible variables.
Given:

```text
body result = U('a)
required result = bool
```

the constraint `U('a) <: bool` is a valid inference refinement. For a generic impl declaration it
is the wrong logical operation: the source promises the method for every `'a`, not only the refined
subset.

Changing the direction or adding the reverse constraint does not fix the problem. Bidirectional
constraints can coalesce or intersect the flexible variable with `bool`; they do not establish that
the original universal proposition was valid.

The conformance mechanism therefore needs either:

- a representation in which `U` cannot be solved; or
- an immutable comparison that observes `U` symbolically and never mutates inference state.

## 6. Design directions

### 6.1 Direction A: live skolem/universal binders

Lower impl head variables as rigid skolems while checking method bodies. Constraint application may
refer to a skolem but may not add a bound that narrows it. A requirement such as `'a <: bool` would
fail unless it is already true structurally.

Advantages:

- matches the standard logical reading of generic declarations;
- produces errors close to the original constraint and source expression;
- reuses the existing constraint-generation path for functions, effects, records, and roles;
- can detect a mismatch before the candidate is finalized.

Risks:

- the current `ConstraintMachine`, compact collectors, floor/co-occurrence simplifiers, and
  generalizer assume ordinary flexible `TypeVar`s;
- adding a protected-variable set to simplification would repeat the class of rigid/blocked/through
  mechanisms prohibited in the inference core;
- candidate registration happens before all methods and prerequisites are known;
- skolems must not leak into ordinary schemes, cache interfaces, or runtime surfaces;
- implicit casts and role predicates need a principled rule under skolem scopes.

Assessment: semantically strong but high-risk. It is not acceptable to implement this as a set of
variables that simplification is told not to touch. A real binder kind and proof of lifecycle would
be required.

### 6.2 Direction B: post-generalization alpha-aware structural subsumption

Let ordinary inference finish. Convert both the generalized method scheme and the specialized role
requirement into immutable binder-aware structural views, alpha-normalize their local binders, keep
`U` in a shared namespace, and check subsumption without mutating the solver.

Advantages:

- does not alter the hot inference path or generalization fixed point;
- cannot narrow the candidate as a side effect;
- naturally supports deterministic witnesses and source-independent alpha tests;
- resembles the successful separation between mutable inference and canonical cache-interface
  validation.

Risks:

- a shape-only comparison is known to be unsound; constructor paths, binder identity, recursive
  bounds, variance, effects, rows, stack weights, and predicates all matter;
- reimplementing the type relation separately from `ConstraintMachine` risks semantic drift;
- subtyping over unions/intersections and recursive bounds may require more than a tree walk;
- implicit cast availability must not be guessed from type shapes;
- a generalized method may already contain bounds introduced by the bad requirement connection,
  hiding the original mismatch. Validation inputs must preserve the pre-conformance principal
  method surface or avoid applying the explicit requirement before validation.

Assessment: the most promising proof mechanism if it is based on a clearly specified symbolic
surface and existing structural helpers, not another inference solver.

### 6.3 Direction C: dedicated immutable role-impl conformance pass

Introduce an explicit pass after method schemes and candidate prerequisites have settled but before
the source set is accepted or written as a compiled unit. The pass receives one complete impl
contract and all method schemes, validates atomically, and emits structured diagnostics.

This is an architectural placement, not by itself a proof algorithm. Its kernel could be Direction
B, or an isolated solver replay with real skolems if Direction A is later formalized.

Advantages:

- one entry point owns multi-method and multi-associated consistency;
- validation sees finalized method schemes and complete prerequisites together;
- invalid candidates can be excluded atomically from successful output;
- source provenance for impl, associated declarations, and methods can be retained deliberately;
- inference and validation responsibilities remain distinct.

Risks:

- candidates currently participate in inference before this point; a later failure prevents a
  successful build but may cause secondary diagnostics in the same failed build;
- moving candidate visibility until after validation would require a two-phase role table and could
  break same-module method resolution;
- the pass still needs a sound kernel and binder mapping.

Assessment: preferred orchestration boundary. The leading feasibility candidate is Direction C
using Direction B as its first proof kernel. This is not yet an approved implementation decision.

### 6.4 Isolated scratch replay variant

A fourth implementation technique is to replay `M_i <: Req_i` into an isolated constraint machine
whose `U` binders are encoded as symbolic constants. This could reuse propagation rules while
keeping the production machine immutable.

It remains unconfirmed whether the existing machine can represent such constants without adding
the same rigid-variable machinery as Direction A. Nominal-cast events also currently treat a
missing candidate as a no-op, so scratch replay cannot be considered a proof oracle unchanged.

## 7. Proposed logical inputs

Names are illustrative. A conformance pass needs information equivalent to:

```rust
struct RoleImplConformanceContract {
    impl_def: DefId,
    role: RolePath,
    universal_binders: Vec<ImplUniversalBinder>,
    inputs: Vec<DeclaredType>,
    associated: Vec<AssociatedAssignment>,
    prerequisites: Vec<DeclaredRolePredicate>,
    methods: Vec<RoleImplMethodContract>,
}

enum AssociatedAssignment {
    Explicit {
        name: String,
        ty: DeclaredType,
        source: SourceRange,
    },
    Inferred {
        name: String,
        binder: AssociatedInferenceBinder,
    },
}

struct RoleImplMethodContract {
    requirement: DefId,
    implementation: DefId,
    declared_requirement: DeclaredType,
    implementation_scheme: SchemeRef,
    source: SourceRange,
}
```

The contract must retain binder provenance. Reconstructing `U` from raw final `TypeVar` numbers is
not sufficient after alpha-renaming, cloning, or candidate normalization.

The current `AnnTypeBuilder::type_var_bindings` provides a source-name-to-annotation-binder map.
Stage 1 should characterize whether this map is complete for all impl head spellings, self aliases,
associated expressions, and imported names before selecting a permanent representation.

## 8. Binder-aware comparison requirements

An alpha-aware view must use separate namespaces:

- `U0, U1, ...`: impl-universal binders shared across the complete contract;
- `A0, A1, ...`: inferred associated witnesses shared across methods;
- `Qm0, Qm1, ...`: method-local quantified binders, fresh per method;
- `Rm0, Rm1, ...`: method-local recursive-bound binders;
- closed concrete constructors identified by canonical path, not numeric ID.

Raw `TypeVar` equality is neither necessary nor sufficient. Two alpha-renamed method-local binders
may be equal logically, while two occurrences accidentally reusing the same raw ID across arenas
must remain distinct.

At minimum the comparison must cover:

1. builtin and nominal constructor identity plus invariant arguments;
2. function parameter, argument-effect, return-effect, and return variance;
3. tuple arity and element positions;
4. record required/optional fields and row/spread tails;
5. poly-variant tags and payloads;
6. effect rows and stack-weight identities after existing cleanup;
7. recursive bounds without unbounded unfolding;
8. role predicates and associated constraints;
9. Bottom/Top with their actual lattice meanings;
10. declared implicit casts only when the existing language contract permits them.

No comparison may treat `Any` as unknown or error recovery. `Unknown` is the only unknown type, and
an unresolved unknown at conformance exit is a validation failure unless an inference ownership rule
explicitly permits it.

## 9. Explicit and inferred associated assignments

### 9.1 Explicit assignment

For `type value = T`, the expected role method signature is constructed with `value := T` before
validation. `T` is interpreted under `U`; it is not lowered as a new flexible role-associated
variable.

The pass must reject:

- a body result that only conforms after narrowing `U`;
- a body result referring to the wrong universal binder;
- an extra method-local variable escaping as the associated result;
- incompatible assignments across aliases of the same role method requirement.

### 9.2 Omitted assignment

For an omitted associated type, current behavior infers one shared variable from method bodies. A
replacement design must preserve this useful behavior.

Open questions include:

- whether all methods jointly infer one principal witness before validation;
- what happens when no method constrains the associated type;
- how contradictory constraints from two methods are diagnosed;
- whether an associated witness may depend on every `U` binder or only binders reachable from the
  candidate head;
- whether a role with no method occurrence of an associated type may omit it.

Stage 5 should first enforce explicit assignments without changing omitted inference semantics.
Stage 6 should close the omitted/partial/multi-method rules after characterization.

## 10. Predicates, effects, and casts

### 10.1 Role predicates

If a method implementation requires a residual predicate not entailed by `P_impl`, the candidate is
not valid for every advertised head input. Silently attaching a method-only prerequisite after
candidate export changes candidate meaning.

The first implementation may conservatively require every residual method predicate to be present
in the normalized candidate prerequisites under the same `U/A` substitution. A more complete
logical entailment rule is unconfirmed.

### 10.2 Effects and stack weights

Effect conformance must use the same variance and subtraction semantics as ordinary function
checking. The pass must consume already-cleaned symbolic surfaces; it must not run a second
generalization or stack-cleanup fixed point.

### 10.3 Implicit casts

Yulang permits declared implicit casts at expected-type boundaries. It is unconfirmed whether role
method conformance should:

1. require an already-elaborated cast boundary in the method body;
2. query the visible cast table during validation; or
3. require direct structural subtyping for impl contracts and reject implicit adaptation.

The validator must not treat “no cast candidate” as success. If cast lookup is permitted, its
dependency must follow the existing cache/dependency tracking rules.

## 11. Recommended orchestration boundary

The least invasive candidate location is near `BodyLowerer::finish`:

```text
lower all declarations and method bodies
drain analysis / generalize method schemes
collect impl prerequisites
finalize a read-only role impl view
validate complete impl contracts
only then return a successful BodyLowering / write artifacts
```

`finalize_poly_role_impls` currently runs before accumulated diagnostics are returned. A
conformance pass can run adjacent to it, but the order between validation and copying candidates
must be explicit. An invalid candidate may exist in the transient inference table, but it must not
be observable from a successful output or cache artifact.

Quarantining candidates until validation would be stronger but is a separate lifecycle redesign.
The initial implementation should characterize same-module uses before deciding whether quarantine
is necessary.

## 12. Diagnostics

A conformance failure should identify:

- the impl declaration and role path;
- the associated assignment, when it determines the expected type;
- the method implementation producing the actual type;
- an alpha-normalized actual/expected summary;
- whether failure came from value, effect, prerequisite, or binder escape;
- related source ranges for both the associated declaration and method body/signature.

The expected primary diagnostic for the motivating case is conceptually:

```text
impl method `index` does not satisfy associated type `value = bool`:
the implementation returns impl binder `'a`, which is not `bool` for every `'a`
```

An internal slot number is not an acceptable primary diagnostic.

## 13. Relationship to the other two soundness gaps

### 13.1 Function result annotations

The generic impl kernel may be reusable because both tasks need binder-aware comparison of a
generalized implementation surface against a declared signature. The integration bug is distinct:

- function result annotations already generate constraints;
- the immediate and deferred validators compare only broad shape;
- builtin/nominal identity and generic binder correlation are lost;
- missing cast candidates are not diagnosed.

A later function-annotation slice may reuse the immutable structural view and diagnostic formatter.
It should not be fixed implicitly while landing role impl conformance because its cast semantics and
header-arity handling require separate acceptance tests.

### 13.2 Struct field annotations

Struct fields already generate constructor argument constraints and preserve expected field names.
Their failure is mainly an unresolved-cast policy problem:

- infer and specialize both accept an empty direct-cast candidate set;
- emit produces a bare `Coerce`;
- evidence-vm rejects the runtime boundary.

The type-relation kernel may help classify actual/expected fields, but the correct fix belongs to
constructor expected-edge and cast-resolution integration. It should remain a separate stage and
must preserve legitimate declared casts and anonymous-record subtyping.

### 13.3 Shared infrastructure that may be factored later

Potentially shared pieces are:

- alpha-normalized declared/actual type views;
- source provenance for expected and actual types;
- structured mismatch categories;
- deterministic rendering for tests;
- a direct-cast result that distinguishes `Resolved`, `Ambiguous`, and `Missing`.

Sharing these representations does not imply sharing one enforcement pass.

## 14. Staged implementation proposal

### Stage 0: characterization oracle

Size: S. Risk: low.

Add test-only witnesses without changing production behavior:

- explicit `value = bool`, method returns concrete `int`;
- explicit `value = bool`, method returns universal `'a`;
- explicit `value = 'a`, method returns the same `'a`;
- explicit `value = list 'a`, nested binder preservation;
- omitted associated inferred from one method;
- omitted associated shared across two methods;
- partial explicit assignment with multiple associated types;
- method residual prerequisite absent/present in candidate;
- effectful role method with a shared row binder;
- alpha-renamed equivalent impls;
- malformed impl unused anywhere in the program.

Record current outcomes at lowering, generalized scheme, candidate table, check diagnostic, and
specialize. This stage establishes the oracle before selecting the proof kernel.

Exit: every binder class and known failure mode has a direct fixture and symbolic dump.

Stage 0 completed in the 2026-07-12 session. The test-only oracle is split along the existing crate
dependency direction:

- `infer::lowering::tests::case_07` records lowering/check acceptance, generalized impl-method
  schemes, and both infer-local and finalized-poly candidate tables for all eleven patterns (the
  alpha-renaming pattern uses two source fixtures);
- `specialize::tests::generic_role_impl_conformance_stage0_specialize_oracle` records the current
  downstream boundary without adding an `infer -> specialize` dependency: undemanded impl methods
  produce no role-method diagnostic and are not materialized by specialization, including the
  malformed unused impl.

The oracle confirms the motivating gap rather than fixing it. Both `value = bool` counterexamples
are accepted with zero check diagnostics: their method schemes return `int` or the universal impl
binder while the candidate table independently retains `value = bool`. Valid explicit, nested,
inferred, partial, prerequisite-bearing, effectful, and alpha-renamed cases are recorded in the same
symbolic format. The shared-row fixture currently preserves the row binder but also retains the
existing return intersection; that is characterization evidence, not a new conformance rule.
The binder-link inventory also confirms that an explicit `value = 'a` reuses the candidate-head
binder, while an omitted `value` is represented by a distinct inferred variable even when its
formatted bounds look like the same `'a`. In the partial fixture, `first` shares the head binder and
inferred `second` does not. Stage 1 must therefore preserve provenance and identity rather than
reconstructing either from rendered type equality.

### Stage 1: immutable contract capture

Size: S-M. Risk: medium.

Capture one `RoleImplConformanceContract` per source impl while the source annotation identities and
ranges are available. Do not enforce it yet.

Requirements:

- explicit versus inferred associated provenance is preserved;
- `U` is derived from source binder ownership, not final raw IDs;
- method requirement/implementation correspondence is total and deterministic;
- no public API change unless separately approved;
- no solver or candidate semantics change.

Exit: a test-only dump shows the same `U` binder in head, explicit associated assignment, and method
requirement after substitution.

Stage 1 completed in the 2026-07-13 session in three independently reviewed slices:

1. **Binder/provenance capture.** Each source impl now creates one crate-private immutable
   `RoleImplConformanceContract`. Stable `U` identities come from source annotation binder
   ownership rather than final solver IDs, and explicit versus inferred associated assignments
   retain distinct provenance (`U` versus independent `A`).
2. **Total method correspondence.** Every role method is recorded in declaration order as
   `Explicit(Vec<implementation>)`, `Default`, or `Missing`; duplicate explicit members are not
   collapsed, and members matching no role requirement remain in a separate
   `unmatched_implementations` inventory. Requirement substitution records role input slots as
   `DeclaredInput(n)`, explicit-associated binder dependencies as `U`, and omitted associated
   witnesses as `A`. Local default bodies come from a pass1 side table; imported defaults are
   recovered from the remapped runtime `Def::Let.body`.
3. **Lifecycle handoff.** Successful source contracts move once from `RoleImplLoweringContext` into
   a `BodyLowerer` inventory and then into the final `BodyLowering`. Synthetic error-role impls do
   not invent a source contract. No validation consumes the inventory yet, and no solver,
   candidate, or public API semantics changed.

The Stage 1 exit witness reads the contract back through normal `BodyLowering` output and shows the
same logical `U0` in the impl head, `type value = 'a`, and the substituted role-method requirement.
The same output is invariant under alpha-renaming of `'a`. Construction is one bounded annotation
walk per source impl plus immutable storage; there is no new loop, fixed point, protected-variable
set, or role-resolution hot-path work.

Known constraints carried into Stage 2:

- the current parser/module map accepts a role input and associated type with the same spelling;
  Stage 1 preserves both slots and marks occurrences ambiguous rather than choosing one;
- an unannotated default method has no declared requirement signature, so its provision is known
  but its requirement-reference list is absent;
- compiled artifacts preserve an imported default body but not its original source range, so the
  imported `Default` source remains `None`;
- source contracts intentionally do not flow into `BodyLoweringPrefix`: a prefix represents an
  already-compiled unit, while conformance must consume the source contract before artifact
  construction.

### Stage 2: binder-normalized conformance views

Size: M. Risk: medium-high.

Build deterministic immutable views for method schemes and declared requirements. Reuse existing
compact/finalization traversals where possible. Do not add a fixed point.

Substeps:

1. first-order variables, builtins, nominal constructors, tuples;
2. records, variants, rows;
3. functions with variance and effect positions;
4. recursive bounds, stack quantifiers, and role predicates.

Exit: alpha-renamed equivalent fixtures produce equal views; swapped universal binders do not.

### Stage 3: conformance kernel in shadow mode

Size: M-L. Risk: high.

Implement the proposed relation as a pure validator and run it in tests/telemetry without changing
compilation success. Compare results with existing valid std impls and the Stage 0 invalid fixtures.

No-heavy-fixpoint rule:

- no mutation of the production `ConstraintMachine`;
- no repeated simplify-until-stable loop;
- recursive types use existing binder graph/SCC structure and bounded memoization;
- ambiguous or unsupported cases fail closed in enforcement mode.

Exit: all known malformed explicit impls are rejected in shadow, representative std impls pass, and
no universal binder is rewritten.

### Stage 3 addendum: exact-equivalence collapse (2026-07-13, Claude Sonnet 5 signature — design approval for this addendum's scope only)

Stage 3's first-order relation (3a/3b/3a.5, receiver value+effect comparison) is implemented and lands
the originally-motivating detection (explicit-bool-concrete-int and its effect analogue). However,
Stage 3's own exit condition ("all known malformed explicit impls are rejected in shadow") is not yet
met: 6 Stage 0 generic-associated fixtures (explicit-bool-universal-a, explicit-a-same-a,
explicit-list-a-nested-binder, alpha-renamed-a/b, malformed-unused-impl) resolve to
Unavailable(NonAtomicSurface) rather than a real verdict.

Root cause (established via read-only investigation, cross-checked by execution after an initial
hypothesis -- OrdinarySccBlocker -- was raised and refuted): the captured actual-value compact surface
for these fixtures contains multiple raw TypeVar components (e.g. v27 | v13 for explicit-a-same-a)
that the constraint machine has already proven exactly equivalent (bidirectional, unweighted
subtyping), but which compact merge does not collapse to one id. ActualFirstOrderNormalizer's
single-alternative rule then conservatively refuses to interpret the surface. Naively picking either
raw survivor is unsafe: only one of the two (v13, via the U/A bridge) resolves to the semantically
meaningful U0 identity -- the other (v27, a fresh accessor-instantiation variable) would misclassify
as an unrelated Qm0 method-local quantifier if chosen. This is the same underlying gap previously
flagged as the Qm-identity-collision risk (independent value/effect normalizers assigning colliding
Qm ids).

Design (Codex gpt-5.6-sol investigation and proposal, Claude review and decision):

- Exact-equivalence rule: a -> b iff a has a projected upper bound Neg::Var(b) with empty
  ConstraintWeights (unweighted); the class of a variable is its strongly-connected component in this
  directed, empty-weight, variable-only graph (bounded single-pass computation, no
  simplify-until-stable loop -- consistent with Section 16's no-heavy-fixpoint rule). Collapse to one
  ConformanceTypeView is permitted only when every substantive component is a raw, unweighted
  CompactVar and all remaining variables (after root-anchor exclusion) belong to the same exact class.
  Same-shape, same-origin, one-way subtyping, or "one member has a bridge entry" are explicitly
  insufficient and must not be used as substitutes.
- Bridge preference: zero bridge identities in a class -> allocate one Qm keyed by the class; exactly
  one distinct identity -> use it for the whole class; more than one distinct identity -> fail closed
  (do not silently unify two different declared binders even if the solver proves their variables
  equal) -- surfaced as an Unavailable/Ambiguous reason, not silently resolved.
- Scope includes closing the Qm-identity-collision gap: a per-method binder context shared across a
  method's value and effect actual surfaces (not just within one surface), so two independently
  processed surfaces cannot each land on a colliding Qm0 for genuinely different zero-bridge classes.
- No production `compact`/`constraints`/`generalize`/`poly` module changes are required -- all
  necessary evidence (`bounds().of()`, `projection_uppers/lowers()`, weight emptiness) is already
  exposed read-only from `&ConstraintMachine`.

Decisions (Claude, 2026-07-13):

- The new equivalence-class resolution and collapse logic must stay `#[cfg(test)]`-gated, matching
  every other Stage 3 slice landed today, even though the pre-existing capture functions it extends
  (`ActualFirstOrderNormalizer`, `capture_*_actual_view`) are already production-compiled as part of
  Stage 2 Slice 6's handoff. Zero *new* production-compiled surface for this addendum.
- The shared per-method Qm-identity context is in scope for this addendum, not deferred -- leaving it
  out would not actually close the Qm-collision gap this addendum exists to close.
- Remaining lower-stakes open points (whether `projection_*` evidence-only entries remain admissible
  equality proof under enforcement, the exact Unavailable-reason naming, deterministic
  value-before-effect Qm numbering order) are Stage 5-enforcement-time questions, not blocking for
  this shadow-mode addendum.

Size: S-M to M. Risk: medium to medium-high (identity soundness -- an overly broad equivalence rule
could turn a real mismatch into false Conforms; shadow-only deployment limits exposure while this
settles).

Slices (each independently shadow/std-verified, following this project's established pattern):

- EQ1 (characterization, S/low): expose the exact-equivalence classes for the diagnosed fixtures; add
  one-way/weighted/multi-bridge/cross-surface-Qm witnesses fixing today's (wrong) behavior as a
  baseline.
- EQ2 (structural split, S-M/low, behavior-preserving): separate actual-surface shape projection from
  binder-identity resolution inside the existing normalizer without changing any output.
- EQ3 (shared Qm context, S-M/medium): introduce the per-method binder registry shared across a
  receiver method's value/effect surfaces; verify two genuinely-distinct zero-bridge classes remain
  distinct.
- EQ4 (exact-class collapse activation, S-M/medium-high): activate SCC-based collapse and bridge
  preference; the 6 Stage 0 fixtures move from Unavailable to their correct Conforms/Mismatch
  verdicts.

### Stage 4: prerequisite/effect/cast closure

Size: M-L. Risk: high.

Close the relation over method predicates, effects, stack weights, recursive bounds, and the chosen
cast policy. This stage must settle whether method predicates require exact candidate membership or
a stronger entailment rule.

Exit: effectful and prerequisite-bearing witnesses pass/fail for documented reasons; no missing
cast is accepted as success.

### Stage 5: explicit associated enforcement

Size: M. Risk: high.

Wire validation into the successful `BodyLowering` exit for explicit associated assignments only.
Invalid impls produce structured source diagnostics and cannot enter successful compiled surfaces.

Keep omitted associated inference unchanged in this stage.

Exit:

- the motivating concrete and generic exploits fail at the impl declaration;
- `type value = 'a` and nested valid assignments pass;
- repository std passes;
- downstream specialization no longer provides the first error for these fixtures.

### Stage 6: inferred/partial/multi-method associated semantics

Size: M-L. Risk: high.

Validate one settled inferred associated witness across all methods, partial explicit declarations,
and roles whose associated types appear only in some methods.

Exit: method order does not change the inferred assignment or diagnostic; contradictory methods
fail deterministically.

### Stage 7: diagnostics, artifact, and cache gates

Size: M. Risk: medium.

Add complete source ranges, malformed compiled-unit tests, and ensure invalid candidates cannot be
encoded/imported. Re-run cold/warm and std-prefix surfaces without changing the Stage 7 cache safety
gate from the canonical-cache project.

Exit: source diagnostics are stable, artifact validators reject missing conformance state if such
state becomes serialized, and valid program semantics are unchanged across cache routes.

## 15. Acceptance oracles

### Oracle C1: universal binder preservation

Given a generic impl whose method returns `U0`, changing an explicit associated assignment from
`U0` to `bool` must change the result from pass to fail. Validation must not rewrite `U0`.

### Oracle C2: alpha equivalence

Two impls differing only in source binder names and raw IDs produce the same conformance result and
normalized witness.

### Oracle C3: associated identity

For multiple associated types and methods, every occurrence resolves to the declaration with the
same role-associated name. Swapping assignments changes the result unless the structures are truly
equivalent.

### Oracle C4: no-use rejection

A malformed impl is rejected even when no method selection ever uses it. This distinguishes source
conformance from downstream specialization.

### Oracle C5: no valid-program narrowing

For every valid fixture, candidate head, prerequisites, method schemes, and role-resolution results
are structurally identical before and after enforcement, modulo diagnostic-only metadata and alpha
renaming.

### Oracle C6: cross-feature closure

Representative functions, effects, recursive bounds, records, variants, role predicates, and
declared casts each have positive and negative witnesses.

## 16. Performance and fixed-point policy

Conformance runs once per source impl after ordinary analysis. It is not part of role candidate
search and must not run per method use.

The design forbids:

- a second generalization loop;
- unbounded recursive unfolding;
- cache- or impl-specific rigid/protected sets inside floor/co-occurrence/polarity simplification;
- blocked unification pairs or through flags;
- repeated full-tree alpha comparisons when a memoized structural key suffices;
- using raw IDs as canonical binder identity;
- accepting unsupported proof cases and relying on specialize/runtime to catch them later.

The intended complexity is linear or near-linear in the size of each impl's captured method and
contract surfaces, plus bounded graph memoization for recursive structures.

## 17. Rollback and compatibility

Stage 0-4 are characterization/capture/shadow stages and should be independently removable. Stage 5
is the first source-semantic enforcement point.

If Stage 5 rejects a repository std impl that cannot be classified with the documented relation:

1. do not weaken comparison to wildcard variables or shape-only matching;
2. determine whether the impl is invalid, the contract capture is wrong, or the relation lacks a
   language feature;
3. record the case as an explicit blocker;
4. roll back enforcement while retaining shadow telemetry if necessary.

No valid impl may be silently narrowed as a compatibility fallback.

## 18. Unconfirmed points

The following decisions remain open and must not be guessed during implementation:

1. **Proof kernel.** Direction C + B is the leading feasibility candidate, but live skolems or an
   isolated replay may be preferable after Stage 0/1 evidence.
2. **Subtyping completeness.** It is unproved that a bounded structural walk can match the full
   algebraic subtype relation without becoming a second solver.
3. **Cast policy.** Whether implicit casts are permitted in role method conformance, and how already
   elaborated cast evidence is recognized, is unsettled.
4. **Predicate entailment.** Exact normalized membership versus logical entailment of residual role
   predicates is unsettled.
5. **Inferred associated ownership.** The principal lifecycle of omitted associated variables across
   zero, one, or multiple methods needs characterization.
6. **Candidate visibility.** Whether transient use of an eventually invalid candidate can produce
   unacceptable secondary inference effects before the final error is unsettled.
7. **Default role methods and missing members.** Completeness rules for omitted methods and default
   bodies need to be included before whole-role enforcement.
8. **Recursive generic impls.** Method SCCs that call the same role method recursively may require a
   contract skeleton; the validator must not reject them merely because the body scheme is open.
9. **Source identity through artifacts.** If conformance proof metadata is serialized, its stable
   identity and format version are unspecified.
10. **Shared kernel scope.** Reusing the kernel for function result annotations is plausible but not
    approved; struct field repair remains primarily a cast-resolution task.

## 19. Acceptance gates

Generic role impl conformance is complete only when:

- explicit associated declarations participate in every relevant method requirement;
- universal impl binders cannot be narrowed by validation;
- valid explicit, inferred, partial, and multi-method impls pass deterministic witnesses;
- malformed impls fail even when unused;
- actual/expected diagnostics identify impl, associated declaration, and method source;
- predicates, effects, recursive bounds, and the selected cast policy have positive/negative tests;
- alpha-renamed equivalents agree and binder-swapped non-equivalents disagree;
- repository std and representative user fixtures pass;
- invalid candidates cannot be emitted in a successful typed/runtime/cache surface;
- no new inference/generalization fixed point or simplification protection mechanism was added;
- downstream specialize/runtime is no longer the first detector for the motivating cases.

Function result annotation and struct field conformance remain separately tracked bugs until their
own integration gates pass. Completion of this specification does not declare those issues fixed.

Investigation and specification design: Codex (gpt-5.6-sol), 2026-07-12 session. Whether and when to implement remains a decision for Claude Sonnet 5 and the user; this document is a feasibility and design specification, not an implementation commitment.
