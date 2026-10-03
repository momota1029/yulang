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

### Shared-quotient partial search procedures (2026-10-03)

Sol derived two exact partial procedures for the finite, unguarded ranked
structural fragment. A compiler-referee independently reviewed them and found
no blocking or major issue. These procedures do not settle the regular-witness
gap above.

**Regular-solution positive semidecision.** After finite-label erasure, retain
the input's fixed constructor heads and finitely many atom identities, along
with a representative atom for non-input leaves. Enumerate finite well-sorted
quotient graphs, root maps, exact descriptor edges, and a separate relation of
ordered graph-node pairs for every original inequality occurrence. Require
each relation to be post-fixed by the direct local comparison rules: matching
atoms and heads, Record upper-field inclusion with its required child pairs,
and variance-directed children (same direction, reversed, or both). Every
accepted graph is a direct regular solution; every regular solution has a
finite bisimulation quotient and supplies these certificates. Thus size
enumeration eventually finds every regular solution. No finite bound on graph
size, nor negative termination, is established.

**Arbitrary-tree negative semidecision.** For depth `n`, construct one finite
prefix CSP over all shared descriptor tracks and all per-bound signed
comparison states. Enforce shifted descriptor equations
`L(q,iw)=L(child_i(q),w)` only when both addresses are present. Enforce local
shape and comparison obligations when their inspected coordinates fit; do
not add a terminal/default head at the frontier. `Pad` represents missing
shape only, never an active Type or Field value. Restrictions from depth
`n+1` to `n` preserve feasibility, so coherent prefix assignments form a
finitely branching tree. König's lemma gives a full possibly nonregular
assignment exactly when every depth is feasible; every equation and direct
comparison obligation is checked at some finite depth. Therefore, if no
arbitrary-tree solution exists, increasing-depth search eventually finds a
finite infeasible CSP. This does not decide regular satisfiability if an
arbitrary solution exists but no regular witness is known.

The attempts are complementary but do not combine into a terminating regular
decision procedure: regular graph enumeration can run forever on a regular-
unsatisfiable package, while the depth tower remains feasible for any
arbitrary-tree solution, including a hypothetical nonregular-only one. The
unresolved theorem is either an effective regular-witness bound/construction
for every arbitrary-tree solution in this fragment, or another terminating
regular-satisfiability method.

The sorted uniform-rank attempt remains incomplete. Unrestricted padding of
an absent-field payload by a fresh `Top` is unsound if that value is available
at ordinary Type roots: `Int <: X` and `Bool <: X` admit the spurious `X =
Top`, although direct atom comparison rejects the original package. A marker
strictly confined to inactive absent-field payloads is not refuted by this
example; it would need a proven sorting/containment mechanism. This narrows the
failed padding route and is not an impossibility result.

Review caveats: keep each original inequality's own comparison relation;
preserve exact descriptor sharing and absent Record slots; do not use endpoint
success composition; and state finite head/atom alphabets explicitly. This is
an existence-only theorem result, with no permission/guard/`Phi/K,D`, effects,
casts, source-acceptance, resource-policy, or implementation claim. No code,
tests, builds, Oracle inspections, or measurements changed.

### Astra audit of the regular-model boundary (2026-10-03)

After Sol localized the exact remaining regular-witness question, a bounded
Astra audit tried to prove or refute: if the finite descriptor-and-inequality
fragment has an arbitrary-tree solution, must it have a regular solution?
This attempt established neither implication nor counterexample. It did
identify why a simple whole-path signed-domain replacement for §7.4.3 is not
sound.

With a contravariant unary constructor `C`,
`{f:C(Int)} <: {}` succeeds because the upper Record has no `f` field, so
structural comparison terminates at that Record-width step. A whole-path
sign analysis that descends through `f` and reverses direction at `C` would
continue into a branch the comparison never visits and impose a spurious
requirement. Variance may reverse an active comparison only along descendants
that survive every preceding head/Record-width check.

A sound route may track head agreement and variance only at shared present
comparison paths, treating omitted Record branches as terminal successes. The
audit did not show that this can be combined in an effective finite quotient
with (1) shifted descriptor equations `(q,i·w)=(child(q,i),w)`, (2) tree-child
coherence `(q,w)` to `(q,w·i)`, and (3) the same shared interpretation at all
descriptor occurrences. Thus this is an obstruction to one global signed-path
closure argument, not to regularity or decidability itself. The remaining
theorem is a finite regularization construction for those jointly activated
obligations, or a finite nonregular-only counterexample. No such counterexample
was found. The Astra request was `gpt-6-astra` at low effort; live runtime
settings were not independently observable. No files, tests, builds, Oracle
queries, or measurements changed.

### Active-path finite-profile quotient attempt (2026-10-03)

Sol attempted a finite quotient that preserves local head/presence data,
descriptor-root subtree membership, and per-bound active endpoint/orientation
membership. A compiler-referee confirmed a counterexample to this **specific
set-valued profile equivalence**. Let `R(t)={f:t}`, let `C` be binary with
variance `(+,-)`, and use

```text
q = C(x,x)
r = R(x)
b : q <: q
x = R³(Int)
```

under the full direct structural-comparison closure of `b`. The two interior
subtrees `u=R²(Int)` and `v=R(Int)` have the same profile: both are Records
with `{f}`, both occur below each descriptor root, and both occur as endpoints
of `b` at both orientations. All Record fields are present on both sides, so
the positive and negative comparison obligations descend through them. But
`u.f=v` is a Record and `v.f=Int` is an atom. Thus equal profiles do not
determine a unique `f` successor; this equivalence is not a tree congruence.

The counterexample requires the stated unindexed membership profile. Adding
exact paths, multiplicities, depths, or successor-refined data changes the
profile definition and is not refuted here. Likewise, “both orientations” is
about the full labelled structural obligation closure, not an implementation
that shortcuts reflexive identity. The supplied `x` is regular and `x=Int`
also satisfies the package, so this is not a nonregular-only witness or an
obstruction to regular-model existence. A repair must withdraw this
congruence claim or define a stronger finite equivalence and prove both
successor coherence and shifted descriptor sharing. No such repair emerged;
no source semantics or implementation claim follows.

### Literature boundary check (2026-10-03)

A primary paper check does not supply the missing regular-model theorem.
Su et al., *The First-Order Theory of Subtyping Constraints* (POPL 2002),
prove the automata-theoretic decision result for unary constructor symbols and
explicitly leave the full first-order theory of structural subtyping open.
The result does not directly cover this finite ranked fragment with binary
variance-bearing constructors, mandatory Record width, and shared descriptor
equations; no translation preserving those constraints was established here.
This is a limit on importing that result, not an undecidability claim for the
Yulang fragment. [Primary paper](https://www.cs.ucdavis.edu/~su/publications/popl02.pdf).

### Paired-state representative-selection follow-up (2026-10-03)

Sol tried to replace the failed node-profile quotient with finite paired
comparison states. Finite head/orientation labels give the local comparison
transitions, but no proof was found that their cycle choices can be made
consistent with the descriptor equations. The exact remaining lemma is
**finite simultaneous representative selection**: from an arbitrary-tree
solution, select finitely many jointly interpreted endpoint states and
deterministic child transitions so that every original bound's paired
relation remains post-fixed under Record width and variance; every occurrence
of a shared descriptor root selects one tree; and shifted descriptor transport
`(q,iw)=(child(q,i),w)` holds at every present suffix. The selection must
close these obligations together, not separately. No positive regularization
theorem or new counterexample resulted. This remains within pure structural
existence; no source-semantic or implementation decision follows.

### Commuting-action certificates for regular solutions (2026-10-04)

A bounded Astra attack on the exact regular-model gap did not establish that
every arbitrary-tree solution has a regular solution, and did not produce a
nonregular-only counterexample. It did identify an exact finite-certificate
characterization of **regular** solutions for the existing finite-`Λ`,
unguarded ranked structural package.

A certificate consists of a finite state set `S`, initial state `e`, suffix
actions `R_i : S → S`, and prefix actions `L_i : S → S`, satisfying
`L_i(e)=R_i(e)` and `L_i R_j=R_j L_i`. Per-state labels retain every
descriptor/free-root track's full head and Record-presence data, plus each
original inequality's active orientation. Exact descriptor root labels,
well-shapedness, absent-field padding discipline, and active Type/Field
endpoints are checked. For each descriptor edge `q.i=q'`, require
`h_q(L_i(s))=h_q'(s)` at every state. Each original inequality has its own
root-positive bit and direct local post-fixed comparison relation; variance
acts within that relation, and upper-Record absence terminates that branch.
No successful comparison is composed with another.

Decode address `w` by applying suffix actions from `e`. Commutation gives
`L_i(s_w)=s_{iw}`, so every track unfolds as a regular tree and descriptor
sharing is exact. The local labels and per-bound relations then witness each
original inequality directly. Conversely, a regular solution's finite graph
and active-orientation automata yield a finite certificate through the finite
transition monoid: for graph transitions `δ_i`, take `L_i(f)=f∘δ_i` and
`R_i(f)=δ_i∘f`; these actions commute and agree at the identity. Finite-label
erasure supplies the required finite output-label set. An independent bounded
compiler-referee review found no blocking or major issue and confirmed both
directions, including the need for root-positive flags, full Record masks,
well-shapedness/Pad rules, active endpoints, and the `L_i R_j` orientation.

This is a finite witness format equivalent to regular-solution existence,
and therefore another positive semidecision by certificate-size enumeration.
It is not a decision procedure and does not imply arbitrary-solution to
regular-solution. A proposed local-convolution shortcut was also refuted: with
binary `C`, distinct atoms `I,B`, descriptors `q=C(a,b)`, `a=C(I,I)`,
`b=C(B,B)`, and no inequalities, exact sharing makes `q(12)=I`, while the
shortcut's local substitution requires `q(12)=b(1)=B`. This rejects that
encoding only; the package has a finite regular solution. No source semantics,
solver rule, implementation, or source-envelope conclusion follows. The
arbitrary-tree-to-regular implication remains open.

### Least forced completion for arbitrary solutions (2026-10-04)

A separate bounded Astra attack reframed arbitrary-tree satisfiability as a
least positive closure, rather than trying to quotient an arbitrary supplied
solution. The primary checked the proposed completion argument, and an
independent compiler-referee audit found no blocking or major defect for this
exact fragment. The result below is an existence characterization only.

After finite-label erasure, form active Type addresses `(q,w)` for every
descriptor/free-root track and suffix `w`, quotiented by the exact descriptor
equations `(q,iw) ~ (q_i,w)`. The quotient is right-congruent: appending the
same child coordinate preserves each equation. Use compressed Record payload
edges labelled by field `ℓ`; at a Type address, field `ℓ` is either absent or
present with a Type payload address. Maintain positive facts `Live(u)`,
`Head_C(u)` (including atom identity and Record), `Present_ℓ(u)`, and an
independent ordered comparison relation `A_b(u,v)` for each original
inequality `b`.

Seed all free/input roots as live and each inequality's own ordered root pair.
Seed the exact head and every present field, including its payload equation,
for every exact descriptor Record state; exact absent fields and fields
outside its mask are forbidden. Descriptor constructor heads and child
equations are also seeded at every exact descriptor state. Close under:

1. Each active pair makes both endpoints live and transports a known type
   head across the pair in both directions.
2. A known ranked head makes its exact Type children live. A pair with that
   shared head generates child pairs within that same `A_b`, following the
   declared covariance, contravariance, or both directions for invariance.
3. A forced present field forces a Record head and a live payload.
4. If `A_b(u,v)` and upper `v` has field `ℓ` present, lower `u` must have `ℓ`
   present and `A_b` gains the covariant payload pair. If the upper field is
   absent, that branch terminates successfully without inspecting the lower
   payload.
5. All facts respect exact descriptor-address equality and active Type/Field
   shape; no rule activates an absent/padded child or composes distinct
   inequality roots.

Then an arbitrary-tree solution exists exactly when this least closure is
clash-free. Necessity follows because each seed/rule is required by every
solution, while a solution forbids conflicting forced heads and fields that
violate an exact descriptor mask. For sufficiency, assign each live address
its forced head, or `Record{}` if no head is forced, and include exactly the
forced Record fields. Every active pair either has one shared forced head at
both ends or defaults to `Record{} <: Record{}`. Ranked child comparisons and
all required upper-present Record payload comparisons are in that pair's own
closure relation. These relations are direct post-fixed witnesses for the
original inequalities; exact descriptor equations hold by the address
quotient. The resulting type assignment may be nonregular.

The referee highlighted the crucial positive descriptor seeding: recording
only forbidden fields is insufficient. For example, exact `r={f:Int}` and
`{} <: r` must force presence of `f` at `r` and expose the missing lower
field. With the compressed payload convention, absence is simply omission;
an explicit Field sort would instead need its own equations and descent rules.
The closure characterization supplies no algorithm deciding whether it is
clash-free: its fact set may be infinite. Regularity of the forced head and
presence languages remains the next mathematical question. A regular-model
construction would yield a regular solution, but neither that construction
nor a nonregular-only counterexample was obtained. No source semantics,
solver rule, implementation, or source-envelope conclusion follows.

#### Two regularity-preserving closure operators (bounded follow-up)

A second bounded Astra attack did not prove the missing regularity theorem.
It decomposed it into two conditional operators; an independent
compiler-referee review found these component claims usable only with the
representation qualifications below. It did not close the equivalence
between the operators and the quotient Horn closure.

Let `A_b^σ` be the active comparison traces for original inequality `b` and
orientation `σ`, recorded over the common descendant word from that
inequality's original root tracks. Let `U` be the forced-head and
Record-presence predicates. For fixed **regular** activation languages,
descriptor prefix rewrites `(q,iw) ↔ (q_i,w)` and same-word transfers of
forced heads/presence form a finite pushdown system with regular stack tests;
the stack top must represent the first address symbol. This gives regular
unary consequences under that fixed activation input. Ranked-head child
liveness and present-payload liveness append coordinates at the right end and
are not automatically part of this prefix-oriented pushdown construction;
they need separate `Live` closure accounting and may not be used to infer new
head/presence facts.

Conversely, for fixed **regular** unary head/presence languages, a product word
automaton plus finite per-bound orientation flags recognizes the next active
comparison traces. Covariance preserves direction, contravariance reverses
it, invariance activates both. On a clash-free package, the common forced
head has the declared shape on both endpoints and contributes its child
transitions. An upper-present Record field activates its payload pair; an
upper-absent field does not, and is not an irreversible negative fact. These
conditional constructions imply every finite clash-free alternation stage is
regular. Since the Horn rules have finite premises, the clash-free least
closure is the union of those finite stages; that union need not be regular
merely because every stage is regular (abstractly,
`X ↦ X ∪ aXb` from `{ε}` has `{aⁿbⁿ}` as its least fixed point).

The reviewer required the activation representation to retain each original
bound's root trace and resolve descriptor aliases through unary prefix
transport; an arbitrary alias-expanded binary address relation must not be
assumed synchronously regular. Those requirements are preserved in the
conditional correspondence below, which now closes the finite-stage bridge.

Thus no regularity theorem, effective procedure, or nonregular-only package
result follows. The sharpened target remains an effective regular recognizer
for the joint forced-head/presence closure (or another proof that the
canonical default-`Record{}` completion is regular). Exact trace and clash
preservation are established only for the clash-free conditional lemma; the
omega-union regularity question remains open.

#### Clash-free trace/unary correspondence (reviewed conditional lemma; omega-union regularity open)

**Premises.** Fix the earlier finite unguarded ranked-structural package: a finite
constructor/field signature, finitely many descriptor roots and exact
constructor/Record equations, and finitely many original directed
inequalities. The descriptor quotient is generated by right-congruent child
equations `(q,iw) ≡ (q_i,w)` (with the analogous typed field-payload
coordinate). The comparison closure has only the listed direct structural
rules: no comparison transitivity, no comparison-root composition, and no
activation at an absent or padded child. Consider only a package whose least
forced closure is clash-free.

For each original inequality `b`, let its two endpoint roots be `q_L,q_R`.
Represent a direct comparison descendant by `(b,w,σ)`, where `w` is one
shared coordinate word followed from those two original roots and `σ` is the
endpoint orientation. A positive variance preserves `σ`; a negative variance
flips it; an invariant position supplies both. A record-field child appends
that field coordinate and preserves `σ`.

**Claim.** On this clash-free branch, the least quotient closure is exactly the
least alternation of (i) unary forced-head/presence saturation `F(A)` for a
fixed active-trace family `A`, and (ii) root-seeded, finite-path
active-trace expansion `G(U)` under a fixed unary fact family `U`. Every
finite alternation stage is regular when its input family is regular. This claim is about exact closure correspondence
and finite-stage regularity; it does not say the omega-union is regular.

**Trace correspondence.** Induct on comparison-rule derivations. Each root
seed has trace `ε`. A descriptor-equation rewrite changes an address
representative of an endpoint class, not its trace or original comparison
root. Every comparison-producing rule is a child rule, appending the same
constructor coordinate or field coordinate to both root tracks; only the
orientation bit can change. Conversely, a trace transition is introduced
only by one such rule. Thus every quotient active pair on this branch has a
common root trace, and every generated trace denotes a valid quotient pair.
This does not identify endpoints across different original inequalities or
compose their successful comparisons.

**`F` completeness and regularity.** For each trace `(b,w,σ)`, a known head
on either endpoint transfers to the other endpoint. A present upper Record
field forces that field present on the lower endpoint. Any forced field also
forces the Record head. Descriptor equations transport every unary fact over
all representatives by the finite prefix rewrites `(q,iw) ↔ (q_i,w)`; field
payload equations use the corresponding typed rewrite. These are exactly the
unary closure rules. If `A` is regular, encode each unary fact predicate,
descriptor root, and inequality endpoint in finite control and use `w` as a
stack with its first coordinate at the top. Descriptor rewrites are push/pop
transitions; comparison transfers are same-stack transitions guarded by the
regular trace language for `b`. Regular pushdown reachability from the finite
descriptor seeds yields exactly the unary `F(A)` facts and remains regular.
No head or presence conflict is discarded; under the premise, none occurs.

**`G` completeness and regularity.** For a trace where `G` takes an outgoing
transition, its current `U` guard requires one common compatible forced head
at both endpoints. If only one endpoint had the head before `F`, `F` transfers
it; two distinct forced heads would be a clash and are excluded by the
premise. A newly reached child trace need not yet have any forced head: it is
still an active comparison, but `G` stops expanding that path until a later
`F` round supplies the head facts. For a shared ranked head, `G` appends each
declared child coordinate with its declared variance and orientation update.
Clash-freedom and exact descriptor equations ensure the child is active on
both sides; there is no absent/padded descent. For a Record field transition,
`G` requires the field present at the upper endpoint and the lower endpoint;
`F` forces lower presence once the parent comparison is in its input, possibly
in the next alternation. `G` then appends exactly that payload coordinate.
An upper-absent field contributes no transition and is not treated as a
negative fact. Atoms and Records with no enabled fields have no outgoing
transition. These are exactly the comparison-expansion rules, allowing a
consequence to appear at a later finite stage. For regular `U`, a product
word automaton over the two root tracks tests the finitely many head and
presence predicates, together with a finite orientation state. Its
transitions are precisely the guarded rules above; root-seeded finite paths
are exactly `G(U)`, so these trace languages are regular.

**Alternation and clash handling.** Start `A₀` with the original root pairs and
`U₀` with exact descriptor facts. Alternate `Uₙ₊₁ = F(Aₙ)` and
`Aₙ₊₁ = G(Uₙ₊₁)`. Both operators are monotone and `G` starts from the
original roots, so growing `Uₙ` preserves earlier trace paths. A finite Horn
derivation uses finitely many rounds of newly available unary facts and
comparison steps, so it occurs at some finite alternation stage; the two
completeness arguments show every stage fact is a closure consequence. Thus
the union of the finite stages is exactly the least closure when it remains
clash-free. If a clash occurs at a finite stage, the package is unsatisfiable
and the derivation itself is a finite rejection witness; the proof does not
need to enumerate positive consequences below that clash. Since every clash
has a finite derivation under these finite-premise rules, stopping there loses
no satisfiable package. The separate `Live` closure only materializes output
shape and does not create head, presence, or comparison facts.

An attempted stronger claim—continue every active pair below clashes by
branching over every common forced head—does **not** preserve the current
active-address rules. Exact unary `x=C(I)`, exact binary `y=D(B,B)`, and
`x <: y` force both heads onto both roots; blindly following shared `D` would
activate coordinate 2 below `x`, an absent/padded child forbidden by the
closure. An exact atom compared with `{f:I}` likewise cannot use a newly
forced Record head to invent an inactive payload below the atom. To claim
exact positive closure on inconsistent packages, a different total-address
convention and its relation to exact descriptor equations would first need
authority and proof. The present lemma does not need that stronger claim.

Independent compiler-referee review first rejected an attempted all-head
continuation below clashes because it could activate absent/padded coordinates.
The repaired clash-free lemma then received two focused delta reviews: the
first found a gap for newly reached traces whose unary facts were not yet
saturated; the final repair requires local head/presence guards at every
expanded trace and leaves new pairs active for the next `F` round. The final
delta review found no remaining issue in that repair or the finite-stage
correspondence. This closes only the conditional exact trace/unary bridge and
finite-stage regularity, not regularity of the least closure.

**Residual mathematical gate.** The finite-stage languages are regular, but
their omega-union need not be regular merely because each stage is regular.
No regular-model theorem, effective recognizer, decision procedure, or
nonregular-only counterexample follows. Prove regularity of the least
clash-free forced-head/presence languages (or another regular solution
construction) before using this fragment as a terminating inference gate.

### Dual absorbing-tree encoding audit (2026-10-04)

After the preceding residual gate was localized, a bounded Astra attempt
developed an exact representation of the finite unguarded ranked structural
fragment. A compiler-referee independently reviewed the supplied encoding
and found no blocking, major, or minor issue in its stated claims.

Let the finite label order contain distinct incomparable source heads between
`Bottom` and `Top`, with an order-reversing involution `d` that exchanges the
extrema and fixes source heads. Encode a source type by positive and negative
ranked trees related by `E-(T) = d(E+(T))`. At active covariant children,
preserve polarity; at contravariant children, reverse it; encode invariant
children in two tagged coordinates, one for each polarity. A present Record
field preserves polarity. An absent field is an entire constant-`Top` cone in
positive polarity and constant-`Bottom` cone in negative polarity. Inactive
coordinates under a head receive constant-head padding.

For this source-valid image, direct structural induction gives
`T <: U` iff `E+(T)(w) <= E+(U)(w)` at every ranked address `w`. The absorbing
Record cones preserve width-rule termination: a present lower field beneath
an absent upper field compares below `Top` at every descendant, while an
absent lower field beneath a present upper field fails at the field root.
Variance and invariant comparisons follow from the order-reversing dual and
the paired tagged coordinates. This remains per original inequality; it does
not compose successful concrete comparisons. Exact descriptor-child
equations become shifted whole-subtree equations on the corresponding
polarity tracks.

The encoding preserves and reflects regularity on its valid image using only
finite head, polarity, invariant-tag, and padding state. That fact does not
give regular witnesses from arbitrary solutions. Source validity still
requires the invariant sibling copies to be pointwise dual and descriptors to
retain shifted subtree sharing; combining these requirements with pointwise
inequalities has not yielded a regular-model theorem. Dropping source
validity is unsound: for covariant unary `C` and distinct atoms `I`, `B`,
`C(I) <: x` and `C(B) <: x` have no source solution, while a relaxed encoded
`x` with root `C` and constant-`Top` active child satisfies both pointwise
inequalities.

This is a reviewed polarity-and-padding reformulation that repairs the earlier
whole-path signed-domain failure at Record width termination. It is not a
regularization, decidability, or new source-semantics result. The omega-union
regularity/regular-witness gate above remains open. Astra attempt: high effort;
independent review: one compiler referee. No repository code, tests, builds,
Oracle queries, or measurements changed.

### Bounded strict-width regularization lemma (conditional)

An Astra attempt isolated a sufficient condition for regular witnesses in
this fragment. Suppose a satisfying arbitrary-tree assignment is given, and
there is a finite comparison depth `D` such that every active Record pair in
each original inequality's direct comparison tree at depth at least `D` has
equal field masks. Depth counts structural comparison steps from the original
root; descriptor rewrites preserve the represented subtree and do not reset
that depth. Active comparisons here are those generated by the supplied
assignment, not just the least positive closure.

At every active frontier pair at depth `D`, the compared endpoint trees are
equal. Heads and atoms match by satisfaction. Equal Record masks ensure every
present field is compared; there is no lower-only field hidden by an
upper-absent stopping branch. All ranked-constructor children are compared.
Variance preserves or reverses equality, and invariance compares both ways.
Thus the active frontier pairs and their descendants form an equality
bisimulation.

Build a finite rational equation graph by retaining the full original
descriptor graph, recording the satisfying assignment's heads, masks, and
child equations on the finite comparison prefixes before `D`, and equating
each active pair at depth `D`. Use fresh payload variables for lower-only
Record fields where needed, without activating any absent-field comparison.
The supplied assignment witnesses consistency of these equations jointly,
including recursive and shared descriptor equations. Finite rational
unification therefore yields a finite graph assignment. Unconstrained graph
classes can use `Record{}`. Its unfolding is regular; each original
inequality's finite prefix followed by the frontier equality bisimulation is
a direct post-fixed comparison witness. A compiler-referee review found no
blocking or major issue in this conditional construction. Its minor node
count concern was removed by making no quantitative bound claim.

This narrows the regular-witness gap without closing it. The regular package
`x = {f:x, g:I}`, `y = {f:y}`, `x <: y` has strict width at every `fⁿ` and
already has a regular solution, so bounded strict width is sufficient but not
necessary. Any nonregular-only counterexample would require unbounded strict
width in every satisfying assignment; this is only a necessary condition.
The remaining case is infinitely recurring strict-width comparisons: equality
frontiers are then unsound, while finitely selecting unequal frontier pairs
returns to simultaneous representative selection. No regular-model theorem,
decision procedure, or source inference result follows.

### Aperiodic-tiling reduction audit (bounded negative result)

A further Astra attempt tested whether finite descriptors and direct
comparisons can encode an aperiodic Wang tiling, which would give an
arbitrary-tree solution without a regular one. No reduction was established.
Three scoped facts sharpen that route:

1. Under a fixed, coordinate-independent pointwise decoder from finitely many
   regular track labels at addresses `aⁱbʲ`, the decoded grid is periodic in
   both coordinates beyond finite thresholds. This follows because each
   child transition is a function on the product's finite graph states, so
   its powers eventually repeat uniformly over all starting states. If the
   decoded grid obeys Wang adjacency on that northeast tail, repeating one
   periodic rectangle gives a doubly periodic plane tiling. Thus a tile set
   with no periodic plane tiling rules out this particular decoder, not all
   conceivable encodings.
2. The least-forced-completion argument blocks a standard finite tile-choice
   encoding only when the package requires **every arbitrary-tree solution**
   to choose from a finite palette at a fixed live address. A finite palette
   of atom heads then forces one atom; an antichain of Record masks likewise
   forces one mask. This argument includes finitely many auxiliary variables,
   but does not apply to a restriction on regular solutions alone, nor to
   labels decoded from several positions or predicates.
3. A root descriptor diamond does not supply arbitrary-prefix commutation.
   For binary `C` and distinct atoms `I,B`, let `s=C(I,I)`, `t=C(B,B)`,
   `u=C(s,t)`, `v=C(t,s)`, and `q=C(u,v)`. Then `q.ab=q.ba=t`, hence
   `q(abw)=q(baw)` for every suffix `w`; yet `q.aab=I` and `q.aba=B`.
   Additional package equations may impose broader commutation, but this
   diamond alone does not.

An independent compiler-referee review confirmed the periodicity and diamond
claims and required the arbitrary-tree quantifier for the finite-choice
claim. This audit yields neither a nonregular-only package nor an
impossibility result. A successful reduction still needs finite constraints
that force valid tile labels and both adjacency directions without relying on
unsupported free finite-choice encodings or arbitrary-prefix transport of a
root equation.

### Exact package with nonstabilizing alternation and regular completion

A bounded Astra audit found a concrete package showing that the reviewed
finite alternation may grow at every stage even when its least completion is
regular. Take one covariant unary constructor `C` with child coordinate `a`,
one free root `x`, an exact descriptor `q = C(x)`, and the single original
inequality `b: x <: q`. There are no Record fields or width branches.

Let `A_n` be the comparison-trace family after `n` rounds, starting with the
original root trace, and let `U_{n+1}=F(A_n)`, `A_{n+1}=G(U_{n+1})` be the
reviewed clash-free alternation. Then

```text
A_n = { a^k | 0 ≤ k ≤ n }.
```

For active traces through depth `n`, unary head transfer plus the descriptor
rewrite `(q, aw) ≡ (x, w)` forces `Head_C(x,a^k)` for `k≤n` and
`Head_C(q,a^k)` for `k≤n+1`. Since the compared heads agree, `G` appends the
next covariant child trace `a^(n+1)`, but it cannot append one more before the
next unary saturation forces the head at that new `x` address. Thus every
finite stage strictly grows; iteration until finite-stage equality is not a
terminating saturation algorithm for this fragment.

The least closure is nevertheless clash-free and its canonical completion
is regular: both `x` and `q` unfold to `C^ω`, represented by one graph node
with a `C` self-loop. So this example refutes only plain finite-stage
stabilization as an algorithm. It proves neither nonregularity nor failure of
effective acceleration. The next structural gate is to accelerate this exact
self-shift while preserving joint unary/trace guards and descriptor-prefix
transport, then prove termination for the full finite-label fragment. A
reviewed general accelerator is still required before treating the fragment
as a terminating inference gate.

#### Finite exact closure accelerator when `Λ = ∅` (candidate)

A follow-up Astra construction uses the existing §7.4.1 empty-input-Record
reduction to accelerate the exact head/trace closure for its bounded
subfragment. Retain the finite descriptor quotient and each original
inequality. In a separate finite workspace, add a temporary rational equality
between the two roots of each original inequality and perform finite
constructor unification, preserving contractive cycles and rejecting head
clashes. Do not replace the original directed constraints in the source
problem.

Keep the workspace as a **partial** rational graph: exact descriptor and
unification-forced constructor heads remain labelled; descriptor-free MGU
classes remain unlabelled. Each original root pair has been unified in the
workspace, so for that bound the active comparison trace can be recognized by
a finite product over its graph node and orientation bit. Follow a ranked
child only when the class is labelled; update orientation by that coordinate's
declared variance. Keep bounds separate, seeding each automaton only from its
own original root. This recognizes the `G`-active trace language without
waiting for finite alternation to stabilize. For `q=C(x), x<:q`, unification
creates one labelled `C` node with an `a` self-loop.

The partial labels also recognize the exact least forced-head closure of the
clash-free `F/G` system in this fragment. Any head forced by closure must be
present in the workspace graph because every `Λ=∅` erased solution makes each
original inequality an equality, hence a solution of the temporary equations.
For the converse, form two completions of the least closure: fill every
unforced live address with `{}` in one and `Int` in the other. Every original
comparison remains satisfied: paired endpoints either carry the same forced
head or receive the same nullary default, and the recursive child obligations
are handled by the same closure. Both completions therefore satisfy all
temporary root equations. Any labelled MGU path/head must occur in both
equality solutions. An unforced proper prefix could not support that path
under both nullary defaults, and an unforced endpoint would differ between
`{}` and `Int`; thus each labelled path/head is forced by the closure. Every
queried path has finite length. Induction over its prefixes uses the root
seed, exact descriptor rewrites and the active comparison child rule to give
a finite Horn derivation for each labelled head, even when the MGU graph has
cycles. Conversely, an unlabelled class can be completed with a nullary head
and carries no forced head. This distinguishes “no forced head” from an
output default: only after closure recognition may the canonical completion
fill all unlabelled classes with `Record{}`.

This is an existence/closure accelerator, not a full-fiber or principal
residual representation. The temporary equations are safe here only because
`Λ=∅` reduces structural subtyping to equality; Records with arbitrary
pre-erasure field extensions remain in the original fiber. It does not
accelerate nonempty Record-width choices, permissions, guards, effects,
casts, adapters, or `Phi/K,D`, and it does not validate combining successful
concrete comparisons in the general solver. Exactness and the boundary of
this candidate received a bounded M3 compiler-referee and spec-auditor review.
The compiler referee found no blocking or major issue and one minor gap in
the reverse exactness argument; the candidate now states the two-completion
proof and finite path-depth induction. Primary inspection closed that local
proof-exposition repair. The spec auditor found no scope-conformance issue.
The candidate remains unapproved for use as a terminating inference gate.

### Stratified fixed-head and Record-boundary regularization candidate

A bounded Astra construction proposes an exact regular-witness result for a
mixed fragment, without claiming a result for unknown ranked-head feedback.
Partition the fixed descriptor quotient into `K`, containing exact Function
and other ranked-constructor nodes (cycles allowed), and `P`, containing
atoms, mandatory Records, and descriptor-free roots. Record children remain
in `P`. Require every ranked descent from an original inequality to reach
only `K/K` or `P/P` endpoint pairs; a `K/P` pair is outside the fragment.
Retain the existing finite alphabet, unguarded setting, and primitive-atom
premise of §7.4.3.

For each original bound, explore finite states `(b,kL,kR,σ)` over `K`,
retaining endpoint order, original-bound identity, and orientation. Matching
ranked heads generate mandatory child states; covariance preserves
orientation, contravariance flips it, and invariance generates both
orientations. Reject the package immediately if any reachable `K/K` pair has
incompatible ranked heads or arity, as required by the existing structural
failure rule; only a successful ranked exploration proceeds. Stop at each
`P/P` state and retain its ordered boundary
inequality and the regular language of ranked trace prefixes reaching it.
Solve all boundary inequalities jointly with §7.4.3's Record-domain NFA and
head pushdown saturation, then attach the resulting regular `P` witnesses to
the unchanged finite `K` graph. The finite ranked exploration has at most
`2|B||K|²` states, plus finitely many boundary states; it keeps original
inequalities separate and never composes successful concrete comparisons.

The proposed existence proof is by direct decomposition: every solution of
an original bound satisfies its collected boundary comparisons; conversely,
a joint `P` solution extends through the exact `K` descriptors after the
ranked exploration has passed its local head/arity checks, with the finite
ranked relation and direct boundary simulations witnessing each original
comparison. Thus arbitrary satisfiability would imply a regular witness in
this stratified fragment. A boundary state's descendant trace
language is `L_b,z · D_upper(z)`, where `L_b,z` is its ranked entrance
language and the upper `P` domain is selected by orientation. Finite union
would give regular trace languages. Exact forced-head/presence recognition
is an additional strengthening: its proposed correspondence with finite Horn
derivations over §7.4.3's NFA and head rules remains to be independently
checked.

The construction must not be generalized by simply removing the `K/P`
restriction. The package

```text
e = {}
r = {f:Int}
x = Function(e,y)
q = Function(r,x)
b : x <: q
```

has the regular solution `x=y=Function({},self)`. Its contravariant argument
comparison is `r <: e` and stops at the empty upper Record. Unsigned upper
domain inclusion would incorrectly demand `f` in `e`; rational-equality
unification would merge `e` and `r` and reject their distinct masks. Result
descent then reaches the unsupported `y <: x` `P/K` feedback. This is a
positive counterexample to those shortcuts, not an impossibility result for
stronger acceleration.

This remains a theorem candidate, not an approved inference gate. Bounded
compiler-referee review checked the existence/regular-witness argument,
converse extension, and orientation-sensitive trace formula, subject to the
ranked-head repair recorded below. Spec-auditor review checked the exact
boundary against §7.4.3. No full fragment termination, decidability,
source-semantic change, or implementation authorization follows from this
candidate.

Review record: the first compiler-referee pass found one major omission: the
finite ranked exploration needed to reject reachable `K/K` head/arity clashes
before concluding that boundary satisfiability extends to the original
inequalities. The clause above was repaired; a fresh compiler-referee delta
review closed that finding, including mismatches below matching ancestors.
The reviewer found no new blocking/major issue in the repair. The spec auditor
found no scope-conformance issue and confirmed that §7.4.3 is confined to the
joint `P/P` boundary problem. Exact forced-head/presence recognition remains
outside that review and unchecked. The regular-witness candidate remains
unapproved as an inference gate.

### P/K witness folding counterexample (unreviewed candidate)

A bounded Astra attempt examined one proposed shortcut for accelerating
descriptor-free/ranked (`P/K`) feedback: key a generated comparison witness by
`(free-root, original-bound, opposing-fixed-ranked-node, orientation)`, and
identify its flexible-side nodes whenever this key repeats, even when the
flexible-side address differs. A finite package shows that this particular
identification is not sound as a witness construction. It does not refute
memoizing comparison obligations while retaining distinct witness positions,
nor any richer regular-witness construction.

Use the mandatory empty-Record/nonempty-Record types `e = {}` and
`r = {f:Int}`, exact descriptors `k = Function(r,k)` and `l = Function(e,k)`,
free roots `z,x,y`, and

```text
x = Function(e,y)
q = Function(r,x)
b0: x <: q
b1: z <: k
b2: z <: l
b3: l <: z
```

The original package has a regular solution: let `t = Function(e,t)` and set
`x=y=t`, `z=l`, leaving `q`, `k`, and `l` at their exact descriptors. Direct
decomposition checks each bound. `b0` gives `r <: e` and `t <: t`; `b1`
becomes `l <: k`, giving `r <: e` and `k <: k`; `b2` and `b3` are `l <: l`.
The Record comparison `r <: e` stops at the empty upper Record. No successful
concrete comparisons are composed.

Under the proposed fold, expanding `b1` against `k = Function(r,k)` gives a
Function head at `z`, argument witness `A`, and result descendant `z₂`. The
result child is again compared with `k` under the same original bound and
orientation. Folding that repeated key identifies `z₂` with `z`, imposing
`z = Function(A,z)`. But `b2` then requires `e <: A`. In this fragment the
only compatible shape is a mandatory Record, and the empty lower Record
forces its field set to be empty, so `A=e`. From `b3`, result descent requires
`k <: z`; its contravariant argument obligation is then `A <: r`, which fails
because `r` requires `f`. Thus the fold rejects a package with the explicit
regular solution above. This identifies loss of flexible-side position
constraints from other original bounds as the cause.

The same pattern extends to `l₀=k`, `lₙ₊₁=Function(e,lₙ)` and bounds
`z <: k`, `z <: lₙ`, `lₙ <: z`: `z=lₙ` is a regular solution for each `n`,
while the same fold identifies `z` with its first result descendant and
conflicts for every `n≥1`. This is evidence against only the stated fold key,
not a lower bound on other finite states or a nonregularity/undecidability
result. Assumptions are unguarded mandatory Records, exact descriptor sharing,
ordinary Function variance, exact atom identity, and coinductive direct
structural comparisons; optional fields, guards, permissions, and joint
symbolic predicates are absent.

This candidate has not received an independent compiler-referee review. The
primary checked the displayed finite witness and the two Record obligations;
the general acceleration gate remains open. No solver algorithm or source
semantics follows from this counterexample.

Primary follow-up on this package: the complete active comparison context
distinguishes the root `z` from its result child `z₂`. At `z`, the bound
partners are `k` for `b1`, `l` for `b2`, and `l` on the opposite endpoint for
`b3`. After the chosen Function head, `z₂` has `k` as partner for all three
bounds, with `b3` retaining the reversed endpoint order. One more covariant
result step leaves that context unchanged. In this witness, `z=l` realizes
the first transition with argument `e`, then `z₂=k` closes the repeated
context. This is a diagnostic for a stronger state key carrying the joint
cross-bound partner vector and endpoint order; it is not a general finite
quotient theorem. Any such proposal still has to preserve descriptor aliases,
child coherence, and all jointly imposed local head/Record constraints.

The local transition table is:

| flexible node | direct Function contexts | argument Record constraints | result-child context |
|---|---|---|---|
| `z` | `b1: z <: k`; `b2: z <: l`; `b3: l <: z` | `r <: A`, `e <: A`, `A <: e`, satisfied by `A=e` | `b1: z₂ <: k`; `b2: z₂ <: k`; `b3: k <: z₂` |
| `z₂` | `b1: z₂ <: k`; `b2: z₂ <: k`; `b3: k <: z₂` | `r <: A₂`, `r <: A₂`, `A₂ <: r`, satisfied by `A₂=r` | same three contexts at `z₃` |

Thus this package's joint context automaton has a transient root state and a
stationary result state; realizing the latter as `k` gives the witness
`z=Function(e,k)=l`. This is a finite calculation for the example only. A
general construction still needs to show that finite joint contexts can be
formed without losing shared descriptor anchors or correlations with `P/P`
boundary solutions.

### Finite joint-context state proposal for P/K feedback (unproved)

The package suggests a more precise state than the rejected one-bound fold.
For an original bound set `B` and finite exact ranked descriptor graph `K`,
give each flexible endpoint occurrence a context atom

```text
(bound-id, flexible-endpoint-side, opposing-K-node, orientation)
```

and associate the **set of all simultaneously active atoms** with the
flexible type node. The key includes exact `K` identity and endpoint order;
it must not merge one occurrence merely because a single bound/partner pair
repeats. A selected constructor head and, for a Record, its finite field mask
are local labels in addition to the context set. Original descriptor-root
aliases remain named graph anchors and are preserved as equations, rather
than being identified solely by matching profiles.

For a ranked child, transfer every atom in the context together: retain its
original bound, follow the corresponding exact `K` child, and transform side/
orientation by the declared variance. Invariant coordinates transfer both
directions. At a Record head, create boundary obligations only for present
fields demanded by the upper endpoint in that ordered comparison; omitted
upper-Record branches stop there. Once both children are in `P`, retain their
ordered original-bound boundary and solve all such boundaries jointly with
the existing §7.4.3 machinery. Do not compose successful concrete
comparisons.

There are at most `4|B||K|` context atoms, hence at most
`2^(4|B||K|)` context sets before finite descriptor-anchor and local-label
products. In the displayed package this transfer yields exactly the transient
`z` context and stationary `z₂` context recorded above. This is only a finite
state proposal: it has not shown that quotienting all repeated
`(context,anchor,head,field-mask)` states preserves one shared descriptor
assignment or the same `P/P` fiber. The completeness direction must map an
arbitrary-tree solution to a finite joint graph while proving deterministic
child profiles, anchor equations, and compatible simultaneous `P/P` exits.
The sufficiency direction must exhibit one post-fixed comparison relation per
original bound on that graph. No regular-witness theorem or terminating
procedure follows until both directions are proved and independently
reviewed; this proposal has not received that review.

Primary scope audit exposed another uncovered transition. A ranked descriptor
node in `K` may have a child that is a descriptor-free root in `P`. For
`q=C(x)` and the single bound `x <: q`, with covariant unary `C`, the first
matched-head descent produces a comparison between the selected child of the
flexible value `x` and the free root `x`; both are `P`, but they may have
ranked heads. The regular witness `x=C^ω` satisfies the bound, yet the
resulting `P/P` ranked obligation is outside §7.4.3's Records/atoms procedure.
Thus the profile transfer above is undefined at this edge unless it retains a
joint flexible/flexible comparison state or supplies another reviewed solver
for ranked `P/P` exits. The current candidate must not be read as covering
these cases; this scope gap is manually identified and independently
unreviewed.

Scope precision: the isolated `Λ=∅` package `q=C(x), x<:q` is covered by the
separate finite exact-closure accelerator in §7.4.1's subfragment: temporary
rational equality turns this self-shift into one labelled `C` cycle. The open
transition is its coexistence with nonempty Record descriptors elsewhere in
the same finite package, where that reduction does not apply. Any counterexample
or state construction for this gap must keep such a Record obligation active;
the isolated unary example does not refute the accelerator within its scope.

Minimal mixed-record probe for the remaining P/P transition: use an abstract
binary constructor `C` with declared variance `(+,-)`, exact Records
`e={}` and `r={f:Int}`, descriptor `q=C(x,r)`, and the one bound `x <: q`.
Choosing the head of flexible `x` as `C(x₁,e₁)` generates the covariant child
obligation `x₁ <: x` (P/P) and the contravariant child obligation `r <: e₁`.
The regular assignment `x=C(x,e)` sets `x₁=x` and `e₁=e`, discharging the
first by reflexivity and the second by mandatory-Record width. This places a
ranked P/P obligation and a nontrivial Record comparison in one satisfiable
package. It is a minimal closure probe only; it neither refutes a candidate
nor proves a general regular-witness result, and `C` here is not a proposal to
decompose Yulang Function's coupled effect interface as an arbitrary ranked
product.

**Bounded compiler-referee delta review.** The initial probe had its Record
direction reversed; with `q=C(x,r)` and witness `x=C(x,e)`, the reviewer
confirmed the corrected direct decomposition. It also supplied a falsification
case for dropping the generated P/P child: `x=C(Int,e)` passes the
contravariant Record obligation `r <: e` but leaves the failed required child
`Int <: x`. Thus a solver cannot skip the P/P edge merely because the witness
above chooses identical endpoints. The proposed context atom still requires an
opposing exact `K` partner, while this child is P/P; the review confirms that
the current state proposal is undefined here. It reviewed the mixed witness and
this omission discriminator only, not a general flex/flex construction or
regular-witness theorem.
