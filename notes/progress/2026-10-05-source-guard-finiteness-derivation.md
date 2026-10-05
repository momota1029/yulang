# Source-derived guard finiteness: established slices and missing rule

Date: 2026-10-05
Status: bounded source derivation; independently reviewed within the stated scopes
Baseline: committed `a674fcf72` on `research/simple-sub-intrusion`
Scope: derive context finiteness from inspected generation and lexical rules;
no production solver, source restriction, or semantic adoption
Claim class: source-derived finiteness for the named candidate monomorphic
generator; lexical-component finiteness for the admitted unsealed equality
construction; exact missing premise for general guarded subtype closure
Review: compiler_referee and spec_auditor found no BLOCKING/major/minor
findings in the assigned mathematical and source-conformance scopes; §6's
production-code locators and broader implementation remain unreviewed.

## 1. Result and authority boundary

There is no source counterexample to finite guard contexts established by
this inspection. There is a direct source-derived result for the closed
monomorphic pure generator: its scope/evidence context is empty, so one
context per original application bound suffices even when regular
assignments contain recursive feedback. The unsealed equality construction
also derives a finite inventory of retained **lexical** contexts, conditional
on its finite admitted derivation. It does not derive a finite inventory of
every subtype rule's complete guard/evidence context.

The remaining obstruction is a missing source rule, rather than an observed
infinite run: no inspected source gives a complete, meaning-preserving
context transition for same-pivot replay, extrusion-created comparisons,
scheme instances, and sealed packet transport. The existing finite-template
theorem supplies that transition as a premise. Reusing its finite product
bound would not discharge the premise.

The governing package is
[open residual factorization §§2–4.1](../design/2026-10-03-open-residual-factorization.md),
with [closed saturation §3](../design/2026-10-03-scoped-constraint-solving.md)
and [operation-instance §8](../design/2026-10-02-operation-instance-binding-package.md). All sources
in this note were read at the committed baseline. Concurrent task, theory,
and progress edits were not inputs. The reviewed factorization and pure
finite-model theorem are not reopened.

## 2. What needs to be finite

For residual normalization the state is `(b,j,u,v)`. The original source
obligation `b` and context `j` must survive endpoint quotienting. The
context contains the lexical assumptions and binder identities, plus any
rule-relevant witness/evidence correspondence and original `Phi/K,D`
references. A fresh path name is not itself a source obligation.

Three distinct properties must not be conflated:

1. **Initial origins:** a specified finite generator emits finitely many
   source sites and lexical opening contexts.
2. **Derived contexts:** every admitted comparison rule has a
   meaning-preserving successor inside a finite carrier.
3. **Current certification:** checks invalidated by endpoint or permission
   changes are rechecked before publication.

Operation-instance §8's common-entry theorem establishes property 3
conditionally on exhaustive coverage. Its unsealed allocation theorem
supports property 1 for a finite admitted derivation. Residual §4.1 needs
property 2 for the rules it traverses. A finite number of lexical blocks
alone does not bound witness maps or recursively composed evidence.

The [supplied-template context theorem §§2–3](../design/2026-10-03-source-context-finite-closure.md) explicitly takes
finite `J_T` and a meaning-preserving finite label canonicalizer as inputs.
Its §4 derives only initial check contexts for a supplied typed derivation.
The earlier [source-wide audit](2026-10-03-source-guard-context-audit.md)
already proves inheritance for one fixed structural query. The contribution
below constructs origins from the specified pure syntax and separates the
lexical result from the missing full-context result.

## 3. Direct derivation for a specified source generator

Use the candidate rules in
[pure source typing, “Semantic fragment”](2026-09-30-intrusion-pure-source-typing-rules.md),
committed lines 17–81:

```text
e ::= x | integer | lambda x.e | e e

Name:     return Xi(x), no bound
Integer:  return Int, no bound
Lambda:   allocate alpha; generate body in Xi[x -> alpha];
          return Function(alpha, body_root)
Apply:    generate f and a; allocate beta;
          emit t_f <= Function(t_a, beta); return beta
```

Take a finite closed expression with empty outer `Xi`. This fragment has
no rigid opening, declaration bounds, annotation/conversion evidence,
operation witness, schemes, SCC definition generation, effects, or sealed
transport. Specialize endpoint interpretation to the pure contractive
regular structural domain used by residual §§2–4.1. The syntactic generation
claim below does not prove that this carrier interprets all Yulang source.

Let `l` be the number of lambdas and `a` the number of applications. Tag
each emitted bound by its application occurrence `b`. Tags preserve the
meaning of the constraint conjunction; two identical clauses can retain
distinct source sites without changing their solution set.

**Generation claim.** The generated package has at most `a` original
bounds, at most `1 + 2l + 2a` endpoint/descriptor nodes before quotienting,
and empty rigid/evidence context at every original bound. In particular,
its context carrier can be constructed as `J = {epsilon}`.

**Proof by syntax induction.** Name lookup returns an already allocated
lambda endpoint, so it adds neither nodes nor contexts. All integer
occurrences may reference one `Int` node. Lambda adds one flexible parameter
node and one Function descriptor, then combines the finite body graph;
its value binding is an endpoint reference, not a rigid scope opening.
Application adds one result variable and one Function descriptor and emits
one bound at its own site. It adds no lexical assumption or evidence
constructor. Thus all bounds have the same empty scope/evidence payload.
The upper bound on nodes allows the `Int` node even when absent.

**Map to residual input.** Let `Eq` be empty, `B` the application-tagged
inequalities, `Guard` true, and `Phi` true; there are no `K,D` or request
coordinates to erase in this fragment. The rigid-name universe is empty.
The successful equality quotient maps each source endpoint through `q`
without introducing a rigid name or evidence field. For a source bound
`t_f <= Function(t_a,beta)`, its root state is

```text
(b, epsilon, q(t_f), q(Function(t_a,beta))).
```

Each descriptor-known Function successor selects existing children and
reverses argument endpoints as required. The rule introduces no scope,
binder, or witness. Induction on finite discovery-path length therefore
preserves `(b,epsilon)` through every reachable child, including a repeated
pair. Flexible-head pairs remain under that same empty context. Their full
regular-assignment interpretation also introduces no scope opening.

If `N` is the fixed quotient node count, there are at most `a N^2`
normalization states. This proves the stable finite-context premise for
this particular generator rather than assuming a supplied `J`. The result
is about context/state finiteness and the existing conditional residual
equivalence; it adds neither an acceptance algorithm nor a principal
projection theorem.

**Source-shaped feedback check.** `lambda x. x x` emits the single bound
`alpha <= Function(alpha,beta)` and returns that Function. The regular
assignment `alpha = mu A.Function(A,Int)`, `beta = Int` satisfies its
pure structural bound. An arbitrarily long unfolding never opens a binder:
`x` continues to denote the same parameter endpoint, and the application
continues to denote the same origin `b`. The normalizer initially retains
the flexible-head residual; evaluating the regular assignment closes via
its graph back-edge. This is a mathematical witness for the named generator,
not a production-source acceptance claim or a recursive-definition rule.

The separate [empty-Record source theorem](2026-10-04-empty_record_source_fragment.md)
already derives its label
alphabet. Context finiteness here uses the absence of scope/evidence
generation, independently of label erasure or existence-witness selection.

## 4. What the unsealed construction actually derives

Operation-instance §8, “Deriving lexical prefixes for the admitted unsealed
equality core,” committed lines 672–721, assumes a finite acyclic typed-core
construction. Its concrete allocation/flow rules are:

- allocate shared SCC/result/join/cell roots in their owning context;
- lookup and capture reuse endpoints;
- fresh local endpoints use the current live opening frontier;
- allocate handler output before each arm opens its distinct child block;
- outward unsealed flow restricts reachable permissions to the destination
  frontier, follows bindings, and checks opened dependencies;
- deferred comparisons retain their generating lexical context, and relevant
  changes invalidate and requeue them through `Compare`.

Let `G` be the lexical contexts actually visited by that finite construction
and `L` its allocated opening blocks. Assign an identity to each block
allocation, retaining the parent relation. `G` and `L` are finite because
there are finitely many allocation/derivation events in the admitted
construction. No global numeric depth identifies sibling blocks.

For every generated equality `b`, record its visited context `g_b`.
Lookup/capture preserves existing ownership; alias restriction intersects
permissions; outward flow selects an already visited destination; deferred
rechecking retains `g_b`. None of those rules allocates a new lexical
opening merely because the equality is decomposed or rechecked. Consequently
the equality fragment has at most `|G|` retained lexical contexts globally
and one generating lexical context for each original equality.

This derives the **lexical component** of `j`, under the admitted finite
construction. It does not prove that its mutable permission state is an
immutable context, or that every typed evidence field is a finite port.
Record permissions as current dependencies of the retained context;
rechecking must evaluate them again. A replay count or ever-increasing cache
version number is not a semantic scope identity.

For the fixed equality inputs the package separately proves finite updates:
bindings eliminate unsolved variables and strict caps can decrease only
finitely often. In the rational equality extension, merges decrease class
count and at most `V H` permission bits can be removed for fixed variables
and rigid names. This supports finite rechecks **only in those fixed
fragments**; it does not cover an inference route that allocates new
representatives, witnesses, or scheme instances during closure.

Operation-instance §7 additionally generates one uniform arm/body template
at fixed family instance and captures, with one checking name per local
declaration binder. Repeated runtime requests specialize that retained
template; they do not independently regenerate its captured environment.
Thus runtime event count alone is not a source of infinitely many lexical
contexts for that one template. Finiteness of the inventory of static family
instances and complete request/result/store transport remains unproved.

## 5. Exact missing source premise and smallest seam

For a nontrivially guarded subtype extension the first missing statement is:

> Given a source-generated original comparison `b` and its complete
> lexical/witness/evidence context, every admitted child or replay comparison
> has a defined context transformation preserving the source judgment under
> the same assignment, and the closure of those transformations is finite
> without identifying distinct binders, witnesses, or assumptions.

For structural children on a fixed quotient, residual §3 and the earlier
audit already support identity transformation. For deferred **equalities**,
operation-instance §8 supports retaining the generating lexical component.
There is no corresponding complete rule for arbitrary subtype replay in
the inspected sources. Replacing “complete context” by “lexical depth”
would erase exactly the witness/evidence part that remains open.

The smallest useful diagnostic seam is two source obligations sharing one
pivot variable:

```text
[b1, j1] A <= X
[b2, j2] X <= B
```

This is an obligation pattern, not a source counterexample. Both contexts
may come from a captured endpoint used in separately opened generic arms.
Their local checking binders remain distinct even at the same depth. If
a permitted internal replay generates `A <= B`, its guard must be checked,
but no inspected rule determines the replay's complete context from
`j1,j2`. Selecting one parent loses the other provenance; granting the union
of private lexical assumptions can expose facts unavailable in either
source check. Keeping a conjunctive hyperedge avoids that erasure only
after a source-preserving replay rule and finite label canonicalizer are
proved. The supplied-template theorem assumes those laws explicitly.

This seam must not be justified by composing successful concrete
comparisons. Variable-bound propagation and the internal replay route have
their own obligations; optional Records already prevent a general concrete
composition law. No new `A <= B` task is authorized by this note.

Three larger exclusions stay explicit: extrusion can create representative
ports and copied bounds; freshening can create distinct instances whose
sharing is source-sensitive; sealed packets can bind dependencies that are
not free unsealed permissions. A finite source spelling or alpha-renaming
argument does not prove their context/instance closure. No unbounded source
witness was found, and the synthetic `t -> Box(t)` recurrence in the
context-closure note is not adopted as a source witness.

## 6. Current-code correspondence and limits

Narrow committed-code inspection confirms the existing implementation does
not itself supply the missing guarded source theorem:

- `crates/yu-hir/src/module.rs::ResolvedExpr`, lines 426–449, contains
  Lambda/Integer/Name/Error, with no call or handler expression.
- `crates/yu-solver/src/lib.rs::ConstraintBatch::collect`, lines 1004–1136,
  records integer/name/lambda facts and source use identities; retained
  `DefinitionUse` records fix `use_level: 1`.
- `InferenceSession::constrain_live`, lines 11059–11222, uses typed endpoint
  pair memoization and Function children; the shown pair key does not carry
  the successor's complete `(b,j)` scope/witness context.

These are ownership/coverage locators, not findings that the old compiler
violates an adopted successor contract. The pure application generator
proved in §3 is a candidate mathematical generator, not that HIR surface.
The production solver also contains effects and older lifecycle behavior;
its finite pair cache cannot certify the proposed guarded successor by
inspection alone. No compiler change follows.

## 7. Verification, omissions, and handoff

Method: committed source/design inspection and explicit generation-rule
induction. No bounded checker was needed; experiments/processes/samples: 0.
No Cargo/build/test, runtime experiment, external search, Git mutation, or
question-board write was performed. Deterministic artifact check:
`git diff --check -- notes/progress/2026-10-05-source-guard-finiteness-derivation.md`
passed.
Because the new note is untracked, a supplemental
`git diff --no-index --check -- /dev/null notes/progress/2026-10-05-source-guard-finiteness-derivation.md`
also checked its contents and emitted no whitespace diagnostics (exit 1
denotes the added-file difference).

Changed path: this note only. Shared task/design/theory records were outside
the lease and remain the primary's responsibility. No independent review is
claimed. Omitted spaces are full guarded subtype generation, replay/extrusion,
sealed transport, generalization/freshening, all-source coverage, and effective
joint residual solving/projection. `GuardFailure` remains distinct from
`StructuralFailure`, and original `Phi/K,D` remains attached to one assignment
in every extension that actually has those coordinates.

Next action: choose one source-preserving subtype replay rule for the fixed
unsealed finite-instance construction, specify its complete parent/conclusion
context and binder/witness incidence, and prove a finite canonical carrier
for that rule. Then integrate it with the already retained structural child
context. Full source instance closure and sealed lifecycle are separate
subsequent obligations. The pure source result and lexical-only result here
do not close them or authorize implementation.
