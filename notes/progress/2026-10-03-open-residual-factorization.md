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
it, invariance activates both, and an upper-absent Record field simply has no
presence-enabled child transition. It must not be recorded as an irreversible
negative fact. These two conditional constructions imply every finite
alternation stage is regular. Since the Horn rules have finite premises, the
joint least closure is the union of those finite stages; that union need not
be regular merely because every stage is regular (abstractly,
`X ↦ X ∪ aXb` from `{ε}` has `{aⁿbⁿ}` as its least fixed point).

The reviewer required the activation representation to retain each original
bound's root trace and resolve descriptor aliases through unary prefix
transport; an arbitrary alias-expanded binary address relation must not be
assumed synchronously regular. It must retain incompatible activated pairs
so they still expose clashes such as `Int <: Bool`, and it must expose forced
lower presence failure such as `{}` `<:` `{f:Int}`. A rule-by-rule equivalence
between these trace/unary operators and the quotient closure is not yet
proved. This is the precise remaining bridge before even using the operator
alternation to study regularity of the actual least closure.

Thus no regularity theorem, effective procedure, or nonregular-only package
result follows. The sharpened target remains an effective regular recognizer
for the joint forced-head/presence closure (or another proof that the
canonical default-`Record{}` completion is regular), with exact trace and
clash preservation established first.

#### Primary trace/unary correspondence construction (candidate; pending review)

The exact bridge can be stated without constructing a synchronized
automaton for arbitrary pairs of aliased addresses. Keep, for each original
inequality `b`, a trace language `A_b^σ ⊆ Δ*`: word `w` denotes the ordered
pair obtained by following the same child-coordinate word from `b`'s two
original root tracks, with orientation `σ`. Induction on the direct
comparison rules gives every active pair a common root trace; conversely each
enabled local child step extends that trace by one coordinate. Descriptor
equations identify its endpoints as quotient addresses but do not create a
second comparison root or compose two roots.

Keep unary facts over *all* representatives `(q,w)` and close them under the
finite prefix rewrites `(q,iw) ↔ (q_i,w)`. Do not normalize the left and right
endpoint tracks independently and then claim that their arbitrary binary
alias relation is synchronous. For fixed regular `A_b^σ`, unary head/presence
transfer uses only same-word tests on the two original endpoint tracks. A
finite-control pushdown system over `w`, with the first symbol at stack top,
implements the descriptor prefix rewrites and guarded transfers; regular
`A_b^σ` provides regular stack tests. Its regular reachable configurations
are exactly the unary `F(A)` closure if the rules preserve root-trace
provenance and retain clashes.

For fixed regular unary facts `U`, build each `G(U)_b` automaton from the
product of the two endpoint tracks' head/presence automata and a finite
orientation state. A state is an active trace even when it exposes a head or
presence clash. On the clash-free branch, matching ranked heads generate the
declared child directions, upper-present Record fields generate the covariant
field child, and upper-absent fields generate none. Atoms and empty/default Records terminate. The root is always active.
This preserves a failed original comparison as a clash witness rather than
filtering it out of the activation language.

On the clash-free branch, if the trace/unary equivalence is proved,
alternating `F` to saturation and `G` to the next trace stage gives the exact
quotient Horn closure: every finite rule derivation is represented at a finite
alternation stage, and each stage adds only consequences of those rules. On
an inconsistent branch, a finite clash witness is enough to reject the
package; this construction does not claim to enumerate positive Horn
consequences below a clash. Exact descriptor Record
presence is seeded in `U`; a forbidden descriptor field reached by a forced
lower-presence transfer remains a clash. Liveness is a separate shape
closure: descriptor roots, active comparison endpoints, known constructor
children, and present-field payloads are live; liveness alone creates no
head/presence/comparison facts. In the default completion, output shape is
then determined by the forced head/presence languages, so separate `Live`
regularity need not be an input to the tree-output product.

This is a primary proof candidate, not yet a theorem. Independent review
validated the common-root-trace induction and the component constructions
with the qualifications above. Unconditional equality with the positive
Horn closure is not claimed after a clash: for distinct unary constructors
`C,D` and atoms `I,B`, `x=C(I)`, `y=D(B)`, and `x <: y`, head transfer yields
a clash, while the raw positive rules may still derive children under each
shared forced head. For satisfiability, retaining that finite clash witness
is sufficient; for an exact closure theorem, the clash-free branch still
needs rule-by-rule proof that (i) every quotient active pair has a common
trace representative, (ii) every closure rule is realized and no invalid
pair is activated, and (iii) pushdown stack tests include every alias
without losing either clash class. Exact descriptor Record presences must
be seeded, and a presence clash means a forced field forbidden by an exact
descriptor mask; an upper absence alone is not a negative fact. Until the
clash-free audit closes, the finite-stage construction cannot be cited as an
exact regularity-preserving iteration for the least closure.
