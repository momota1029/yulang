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
existence; by itself it proves neither an input-bounded witness theorem nor
preservation of arbitrary guards/`Phi`, nor an exact full-fiber quotient.

An independent compiler-referee delta review found no remaining issue in the
repaired §7.4 claims. General input-bounded existence beyond the one-/two-label
fragments and exact symbolic full-fiber representation remain open, as do joint
permission, guard, and `Phi/K,D` solving. No tests, builds, or measurements
ran. Continue with larger Record alphabets and input clauses retaining
Function/other constructor heads, then return to the full joint fiber; the
full goal remains active.

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

### Bounded one-label Record existence

§7.4.2 now closes an additional existence-only slice: after fixed rational
equality quotienting, the input descriptors use only fixed atoms, `{}`, and
the mandatory unary field `f`, while the finite shared inequalities retain the
full regular assignment grammar. Erasing other labels and squashing matching
non-Record constructor heads reduces existence to `{}`, unary `R`, and a finite
atom set. Every reduced regular assignment is a finite chain ending in `{}` or
an atom, or the shared infinite chain `Omega`. The direct comparison table
reduces each original inequality to category compatibility and integer depth
constraints; shared roots get one category/depth and descriptor cycles map to
`Omega`. A bounded finite difference-constraint witness follows.

Independent M3 compiler-referee and spec-auditor delta reviews found no
blocking, major, or minor findings. The theorem decides only this one-label
unguarded structural existence fragment. It retains original directed
inequalities and does not represent the full fiber. Three-or-more labels,
scope/permission preservation, joint `Phi/K,D`, source acceptance and
implementation remain open. `git diff --check` passed;
no tests, builds, or measurements ran.

### Finite-alphabet Record existence extension (candidate; M3 review clean)

Sol's bounded proof audit found that §7.4.3 uses no property specific to two
labels. The path-domain/head-propagation argument extends to every finite input
Record alphabet `Λ`: field saturation ranges over `Λ`; Record-head seeds use
the regular union of right quotients for all `l ∈ Λ`; and domain guards compile
using finite transition-function annotations for the finite domain automata.
Every propagated head remains on a present path. Shared paths receive equal
heads, including childless Records; lower-only paths still impose no head
condition on the upper endpoint. The existing effective witness bound remains
finite, with alphabet size reflected in the constructed automata and
transition tables.

The draft now states arbitrary finite `Λ`; `{f,g}` is an instance. The
extension is restricted to the existing unguarded structural existence
fragment with fixed atoms and mandatory Record input descriptors. Known
Function/other constructor descriptors, guards, permissions, effects,
`Phi/K,D`, source acceptance and exact full-fiber representation remain
outside it. The independent compiler_referee review found no findings on
domain/head completeness, finite pushdown compilation, witness construction,
or the effective bound. The spec_auditor found one minor task-record wording
inconsistency, repaired above, and no other scope issue. This remains a proof
candidate, not mechanically checked and not implementation authority. No
tests, builds, or measurements ran.

### Exact sorted encoding for finite-Λ Records with known constructors

Sol adjudicated Astra's bounded investigation of extending existence to
Function and other known-constructor input descriptors. The suggested direct
extension of §7.4.3 is not justified: with variance, lower-only paths must not
activate comparisons beyond an absent upper Record field, while fixed
descriptor transport and child descent act on opposite ends of path words.
The least active-fact closure may therefore need more than ordinary PDS
saturation. A generic two-ended Horn closure can be nonregular, but no proof
shows its counterexample is realizable by these structural rules.

Astra supplied an exact finite-`Λ` encoding. Use a sorted signature:

```text
T ::= input atoms | Rec(F₁,…,Fₖ) | Function(T,T) | declared constructors
F ::= Absent | Present(T)
```

`Rec` is covariant in its finite field slots. In field sort `F`, `Present(s)`
is below `Absent`, two present fields compare by `T`-subtyping, and `Absent` is
not below any `Present(t)`. Thus upper absence accepts either lower state,
while upper presence requires a present lower field and compares its payload.
Encoding and decoding preserve structural comparisons, all original
constructor variances, regularity, and fixed Record equations, provided every
slot in each fixed descriptor is encoded—including absent slots. Combined
with finite-label erasure, this is an exact existence reduction for the
finite-`Λ` input fragment; it does not represent the unrestricted assignment
fiber.

The cited Niehren–Priesnitz–Su uniform-poset/PDL result is relevant prior art,
but its signatures require common arity and common variance and its stated
reductions do not directly handle this sorted field order. Padding `Absent`
with an unrestricted global extremum would admit spurious source trees. The
remaining theorem is effective satisfiability for regular well-sorted trees
over this finite ranked signature, including exact descriptor equations,
directed covariance/contravariance/invariance, and the conditional
`Present(t) <: Absent` branch, plus regular-witness extraction. No
undecidability or failure of regular completion was shown. Sol recommends
keeping this as a proof route and the Function-descriptor existence gate open;
no new effect machinery or language semantics follows. No files in the design
package changed, and no tests/builds ran.

Primary prior art: [Niehren, Priesnitz, and Su, *Complexity of Subtype
Satisfiability over Posets*](https://www.cs.ucdavis.edu/~su/publications/poset.pdf),
especially §§2.4, 4.1, and 5.1–5.3. Their result is not being treated as a
direct proof for the sorted Record encoding.

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

### Direct multi-track PDL decision candidate for finite structural packages (2026-10-03)

A Sol proof attempt targets the remaining unguarded structural existence gate
with finite Records and constructor feedback. It checks each supplied inequality
as its own recursive obligation; it does not close comparison roots by
transitivity. This is an existence procedure only, not a complete residual
fiber representation or a source-level acceptance rule.

**Fragment.** After the fixed rational equality quotient, take finitely many
regular type descriptors and direct inequalities over: identity-compared
atoms; mandatory Records over the finite input label alphabet `Λ`; and a finite
ranked constructor signature with fixed arities and declared `+`, `-`, or `=`
coordinates. Record fields compare covariantly with width. Use finite-label
erasure from §7.4 for existence. Exclude optional Records, casts/adapters,
effects, Yulang's coupled Function effect ports, scope guards/permissions, and
`Phi/K,D` constraints. The relation is the greatest structural simulation
obtained by recursively decomposing each root inequality according to these
rules; no comparison is generated by composing two successful concrete roots.

**Padded multi-track encoding.** Fix one finite direction alphabet containing
all `Λ` field slots and constructor coordinates. Represent each free type
class and each descriptor child as a separate full infinite tree track over
its finite sort alphabet. Type labels record an atom or constructor head;
Record nodes have one `Field` child per `ℓ∈Λ`; field labels are `Absent` or
`Present`, with a payload child only for `Present`. Every track pads inactive
children by a distinguished `Pad` label and requires every descendant of
`Pad` to remain `Pad`. Local shape clauses enforce each sort, head arity,
record field slot and descriptor equation. In particular, for a descriptor
`x = C(x₁,…,xₙ)`, the root of track `x` is `C`, its active coordinate `i`
subtree agrees pointwise with track `xᵢ`, and its inactive coordinates are
padded. Recursive descriptor equations therefore become cyclic local
constraints over the tracks rather than an unfolding bound.

For every original inequality occurrence `c : x <: y`, give it its own
positive comparison proposition at the common root. At each world, local
clauses require matching Type heads (and atom identity), then propagate the
same comparison state to Record field slots or to constructor children with
the declared variance: `+` keeps orientation, `-` reverses it, and `=`
requires both orientations. At a mandatory-record Field pair, lower-present /
upper-absent succeeds without a child obligation; upper-present /
lower-absent fails; two present fields recurse covariantly on payloads. Each
relation proposition implies only its own local head/presence checks and its
required child propositions. Distinct source inequalities have distinct
propositions. No clause propagates a success between different comparison
roots.

The encoding has a material expressibility problem. A descriptor equation
requires `track_x(iπ) = track_xᵢ(π)`, a prefix/inverted address relation.
Pad closure and recursive comparison propagation use ordinary descendants
`πi`. The cited PDL paper treats these directions separately: §4.1 uses
inverted modalities for constructor equations and explicitly notes that the
inverted fragment cannot express descendant propagation; §3.4 does not give a
decision theorem for formulas mixing both directions. Therefore the clauses
below have **not** been shown to form a formula in one decidable PDL fragment,
and neither decidability nor regular-witness extraction follows from the
citation. The two desired translations between assignments and models remain
proof obligations, not established directions.

**Boundary.** The paper's direct theorem is not itself the Yulang solver: its
standard structural signatures and uniform-signature reductions do not directly
supply this many-sorted Record encoding or any optional-field/cast rule. No
reduction to its decision/regular-model result has been established, so this
sketch currently provides neither a decision procedure nor a witness for the
stated pure structural package. Any eventual existence procedure must keep the
original inequalities as the exact fiber, with external permissions, guards
and shared symbolic predicates checked on the same assignment. The fragment
does not type-subtype Function's four ports independently, assign meaning to
`never`/`Any`, or establish the pure-to-handler lift.

Next proof check: find a single supported logic with a proven decision and
regular-model property that expresses both address directions, or replace
this with a reduction that avoids shifted subtree agreement. A uniform
embedding of each descriptor track into its own direction tree may be needed;
its cost and cross-track alignment are unproved. Until that gap closes, this
is an encoding sketch only, not a decision candidate or solver algorithm.
No source or compiler code changed; no tests, builds or measurements ran.

Independent review (compiler-referee and spec-auditor, 2026-10-03) found one
blocking reduction gap: the descriptor equations need prefix/inverted
modalities while Pad closure and comparison propagation need suffix/forward
modalities. The cited PDL result does not justify their combination. Review
confirmed the mandatory Record width cases and the stated exclusions. The
affirmative decidability and regular-witness claims above were withdrawn; the
exact unresolved step is one sound, complete encoding into a supported
decision procedure. See [Niehren, Priesnitz, and Su, §§3.4–4.1](https://www.cs.ucdavis.edu/~su/publications/poset.pdf).

### Fixed constructor heads with variance: first extension boundary

A bounded architect audit considered extending the finite-input-alphabet
existence fragment to retain fixed Function and declared-variance heads. The
existing finite-label erasure does preserve successful structural comparisons
when non-input Record labels are erased, even through Function and
declared-variance children. But the later replacement of all non-Record
subtrees by `{}` cannot be used when input descriptors contain fixed
constructors: doing so changes their exact descriptor equations.

The current unsigned present-domain inclusion also fails as soon as variance
is retained. Let `E = Record{}`, `R = Record{f:E}`, `S = Function(E,Int)`, and
`T = Function(R,Int)`. Direct structural checking gives `S <: T`: Function
argument reversal asks for `R <: E`, which holds by Record width, and the
results agree. Yet `T` contains `arg.f` and `S` does not, so the current
global condition `D_T ⊆ D_S` rejects this successful inequality. Reversing
that global direction would reject ordinary covariant Record width cases;
invariant coordinates require both directed obligations.

Therefore adding constructor-slot symbols or one polarity bit to the current
`§7.4.3` path automaton is not a proved extension. A possible next construction
must jointly saturate present paths, required heads, and signed comparison
paths. Constructor heads determine mandatory child slots and the variance of
each child; those child requirements can in turn extend the path domains.
The proof must preserve every fixed descriptor equation, establish that all
solutions contain the saturated requirements, and construct a regular
assignment that satisfies each original inequality directly. Regularity,
termination, completeness, and finite-witness decoding remain unproved. This
is a new mathematical extension of the structural existence fragment, not a
source-semantics or implementation decision. No impossibility result follows.

### Synchronous tree-automaton route audit (2026-10-03)

After Sol localized the joint path/head/variance closure gap, a bounded
read-only Astra audit tested the natural synchronous multi-track tree
automaton route. That route cannot directly enforce the fixed descriptor
equations. The single equation `q = Fun(x,Int,x,Int)` already requires two
child subtrees of `q` to equal the same arbitrary tree assigned to `x`. If an
ordinary synchronized finite-state tree automaton recognized this relation,
existential projection of the `x` track would recognize
`{ Fun(t,Int,t,Int) | t is a finite type tree }`. That tree language is
nonregular: after determinizing a bottom-up finite-state automaton, two
distinct sufficiently numerous trees `u ≠ v` receive the same state. If
`Fun(u,Int,u,Int)` is accepted, the same parent transition accepts
`Fun(u,Int,v,Int)`. Regular tree languages are closed under track projection,
yielding a contradiction. This rules out that direct automaton encoding of
descriptor sharing; it does not rule out a quotient-specific saturation or
another decidability method.

The comparison transition itself can still be stated finitely: carry an
orientation bit for each original bound; require equal heads; for Records,
check each upper-present field and recurse covariantly only there; for known
constructors, recurse over all fixed coordinates, preserving, reversing, or
duplicating orientation according to declared variance. A post-fixed witness
of these rules satisfies each original inequality directly. The missing
construction is a regular assignment jointly satisfying these comparison
obligations and every fixed descriptor equation. Head choice determines
mandatory children and variance, which determines deeper path demands; the
finite alphabets and orientation states alone do not prove this joint closure
regular or effective. Comparison of already supplied regular types does not
decide satisfiability over shared unknown types. No algorithm, bound, or
impossibility result is established.

The audit requested `gpt-6-astra` at low effort after Sol/architect localized
this new theorem bottleneck; live runtime settings were not independently
observable. No Oracle inspection, edits, tests, builds, or measurements were
performed.
