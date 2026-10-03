# Open residual factorization candidate (2026-10-03)

## Objective and authority

Continued the full SCC-intrusion type-inference replacement objective at
Milestone 3. The immediate gate is the next theorem named by
`notes/design/2026-10-03-scoped-constraint-solving.md` §7: principal residual
factorization for open flexible heads and Record extensions, with scoped
permissions, projection summaries and original joint constraints retained.
The redesign charter and current task explicitly grant no compiler
implementation authority.

## Candidate produced

`notes/design/2026-10-03-open-residual-factorization.md` proposes a finite
normalizer over descriptor-known pairs after the rational equality quotient.
It keeps any comparison with an unresolved flexible head as a residual edge,
so `X <: {}` covers all finite Record extensions without selecting a row
skeleton. Equality aliases share one quotient assignment; permissions,
original `Eq`, invariant coordinates, witness identity and joint `K,D/Phi`
remain correlated. Projection summaries are derived from the whole assignment
and are not independent ports.

The candidate distinguishes scope-guard failure, structural failure after an
admitted guard, and successful normalization. A successful residual graph is
the premise of the proposed factorization equation. This repairs the empty
residual-graph counterexample for a known mismatch such as `Int <: Bool`;
scope failure remains a separate outcome under charter §22.

## Review and evidence

M3 used one architect to derive the bounded theorem shape, then independent
compiler-referee and spec-auditor reviews. The initial reviews found one major
omitted structural-failure outcome and one minor missing matching-atom case.
Both were repaired. A fresh compiler-referee delta review of §§3–4 found no
remaining findings. The source design and theorem authorities were checked
against the affected charters and predecessor packages.

No compiler code changed. No tests, builds, or measurements ran. Review does
not prove the proposed factorization theorem or any open-bound decision
procedure.

## Remaining gate

The conditional two-direction normalization-equivalence proof is in §4.1 of
the candidate and received a clean compiler-referee review. Its finite state
bound still assumes stable finite guard/evidence contexts. Operation-instance
§8 grounds inherited lexical context, identity-distinct sibling openings, and
invalidation/requeue behavior for a finite unsealed equality construction;
this does not establish coverage for every source-generated subtype check or
sealed lifecycle path.

## Follow-up: closed-regular Record field fiber

§7.2 of the candidate now extends the one-class Record fiber theorem from
identity-only atomic fields to fixed contractive regular field endpoints with
no unresolved flexible class. It characterizes all admissible label shapes
and leaves each selected field's joint lower/upper comparisons in an explicit
`F_f` fiber. The proof uses Record width/depth directly against one assembled
`X`; it never compares two endpoint successes through `X`. Recursive regular
field witnesses can be assembled by finite rooted-graph copies, while
permissions, original guards, and `Phi/K,D` remain conjoined on the same
assignment.

Independent bounded compiler-referee and spec-auditor reviews found no
findings in §7.2's fiber characterization or scope. This does not decide
field-fiber nonemptiness effectively, handle flexible endpoints/cross-field
constraints, or establish source-generation applicability. `git diff --check`
passed; no tests, builds, or measurements ran.

## Follow-up: closed structural interval inhabitation

§7.3 now gives an effective finite test for the unguarded structural
nonemptiness of a field interval whose lower and upper endpoints are fixed
closed regular graphs. States are finite pairs of endpoint-node sets. The
greatest-fixed-point transition follows Function variance, declared variance,
invariant two-way obligations, and Record width/depth; surviving states
construct finite regular witnesses. Its proof decomposes each endpoint
comparison directly against one witness and never composes successful
concrete endpoint checks through that witness.

The compiler-referee review found no blocking/major issue and one minor
ambiguity that equal arity might include Record label count. The wording now
limits arity equality to Functions and fixed-arity constructors and leaves
Record width to its own transition. Spec-auditor review found no conformance
issue. This decides only unguarded structural nonemptiness and extracts one
witness; it does not decide full `Perm_Q ∧ Guards ∧ Phi_q`, preserve every
field candidate under those predicates, or establish source applicability.
`git diff --check` passed; no tests/builds/measurements ran.

## Follow-up: recursive open bounds and witness size

§7.4 separates unbounded explicit graphs in the full solution fiber from
existence-witness size after finite-label erasure. For `X <= Record{f:X}`,
the regular assignments `Tₙ` place a `g` field at arbitrarily deep positions,
so the pre-erasure fiber has no uniform finite explicit graph bound. But with
input labels `Λ={f}`, erasure collapses every `Tₙ` to
`μZ.Record{f:Z}`. This family therefore does not refute bounded existence
witnesses after erasure, finite residual constraints, or regular tree
grammars. The finite-label lemma is limited to unguarded pure structural
existence; it proves neither an input-bounded witness theorem nor preservation
of arbitrary guards/`Phi`, nor an exact full-fiber quotient.

An independent compiler-referee delta review found no remaining issue in the
repaired §7.4 claims. The input-bounded regular-witness/termination theorem
and exact symbolic full-fiber representation remain open, as do joint
permission, guard, and `Phi/K,D` solving. No tests, builds, or measurements
ran. Next prove or replace the structural existence theorem, then return to
the full joint fiber; the full goal remains active.

### Bounded empty-Record-alphabet existence subfragment

§7.4.1 now proves a terminating existence test when the finite structural
input contains no nonempty Record descriptor (`Λ=∅`), while assignments may
still contain arbitrary Records. Finite-label erasure reduces any solution
to the grammar where Records are nullary. There, structural subtyping is
regular-tree bisimulation even with Function reversal and invariant declared
variance, so temporary rational equations decide existence. A consistent
quotient plus one shared available atom yields an `N+1`-node regular witness.
These equations are only an existence decision aid; original inequalities
remain in the principal relation, and the full fiber still includes arbitrary
Record extensions.

Independent bounded compiler-referee and spec-auditor reviews found no
findings in the proof and boundary. For nonempty input label alphabets, width
choices and recursive feedback remain unresolved; no full finite-witness
theorem or counterexample is known. Guards, permissions, effects, casts,
adapters, and joint `Phi/K,D` remain outside this result. No implementation,
tests, builds, or measurements followed.

The separate finite supplied-template context-closure candidate has now
received clean compiler-referee and spec-auditor delta reviews after its
finite-label-carrier repair. This proves only conditional finiteness for its
explicit input carriers; source rules still must construct meaning-preserving
finite carriers, close use-site instances/replay, and establish semantic
preservation. The immediate source gate is that rule-by-rule bridge.

For the representation-preserving annotation-check fragment on an already
supplied finite §6 derivation, §4 of the context-closure candidate now records
a bounded root/context corollary. Each source check site and lexical context
stays fixed; typed path transport retains source-tagged evidence and shared
`K,D,ν`, and proof-label erasure adds no execution boundary or demand.
Compiler-referee and spec-auditor delta reviews found no issue. Raw annotation
generation, conversion selection, scheme freshening and derived-query closure
remain outside the corollary.

Next close the rule-by-rule source bridge that constructs the finite context
and instance carriers from raw source while separating immutable lexical
identity from mutable dependency certification. Then prove an effective joint
representation for residual satisfiability plus projection when nonempty
Record alphabets and recursive feedback vary. Uniform scoped typing,
effect/family compatibility, lifecycle, full acceptance, termination/resource
bounds and implementation remain open. The full goal is active.
