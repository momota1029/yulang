# Direct attacks on callback and structural main gates

Date: 2026-10-04
Status: theorem-gate finding; no semantic decision or implementation authority

This record reports direct attempts at the two current main gates. The callback
lane has one exact missing theorem premise. The structural lane has one exact
regular-completion boundary. Neither result authorizes a new carrier, semantic
rule, or support-envelope change.

## Pure-value callback / Function adequacy

**Result: the main theorem remains open at the source-to-endpoint adequacy
theorem; its bound clause has one decisive missing endpoint-bound
factorization premise, even with State excluded.**

Keep the approved B callback generation, actual Pure introduction and §21
entry, callback-slot typed invocation view, distinct receipts, and settled
`d⁻`, `d⁺`, and `b⁺` locations. The direct attempt granted equal challenge
domains and execution correspondence over the largest assembled immutable
source fragment. It still could not derive the required full-bound inclusion.

The relevant statements have different directions and scopes:

```text
source adequacy:      Sem_actual(d) ⊆ P_actual(d)
execution transport:  Sem_actual(d) corresponds to checked execution
required conclusion:  P_actual(d) ⊆ P_checked(d)
```

The source reference remains the exact collecting relation `Sem` defined by
the source-interface adequacy draft. `P_actual` and `P_checked` are endpoint
presentations whose denotations may conservatively cover `Sem`; exactness is
not a separate language-semantic choice here. The unresolved obligation is to
factor the denotation of the actual endpoint presentation, including its
permitted slack, through the linked checked view.

The minimal logical countermodel to the execution-only inference has one
challenge, an execution returning `0`, an actual bound admitting `{0,1}`, and
a checked bound admitting only `{0}`. Both bounds contain the execution, but
the required containment fails. This refutes that proof step; it is not a
Yulang source-program counterexample and does not refute the selected lift.

For the full query, the theorem must construct checked-challenge admission
independently of comparison success and establish both `D_checked ⊆ D_actual`
and the observation-bound inclusion. Even granting equal domains and
execution correspondence on the State-free fragment, the latter still does
not follow. Its single missing premise is:

> Every observation admitted by the actual synthesized endpoint's complete
> bound factors through its existing `J_arg`, `J_body`, designated result
> consumer, and `J_call` composition under the same `ν,K,D` fiber, and that
> factorization is admitted by the linked checked view.

This is a full-bound factorization obligation, not an exactness requirement.
Event routing, `Flow`/`Observe`, and finite history correspondence account for
actual observations; they do not account for additional observations allowed
by an endpoint bound. Excluding State removes store-realization obligations
but does not remove this gap: it already occurs for the stateless terminating
Pure identity. No new user semantic choice or representation deficiency has
been demonstrated.

The missing step is specifically **compositional inversion of the synthesized
complete Function endpoint**. Even for `f = λx.x`, typed-core §6 derives
`P=Value(A)`, `I_body=Value(A)`, `Result(I_body)=Comp(empty,A)`, and only the
skeleton `Fun(P,Result(I_body))`; §§3 and 9 give the invocation schedule but
explicitly do not define a complete-call scheme from that skeleton. The needed
theorem must invert membership in the endpoint's full bound: each checked-
admissible carrier is admitted by the actual entry, and each observation in
the actual bound has a constituent witness through argument, typed rebind,
body/result consumer, and `J_call`, under the same `ν,K,D` and linked `[b,d]`
profile. Callback B step 6 requires forming and checking the completed
interface but does not state this endpoint-denotation clause. Thus the gap is
present before State/import closure; no source counterexample or semantic
choice follows.

An additional direct attempt checked whether existing projection and linking
results already provide this inversion. Parametric-component-linking §3
proves exact existential projection for a supplied complete relation
`F(X,Z)`: membership in `exists Z.F` yields a constituent witness under the
same external assignment. But §3 explicitly leaves source construction and
completeness of that relation open; §§4–6 require the source presentation to
emit it before the linking laws apply. Core §8's fixed-domain certificate
theorem preserves a supplied unchanged challenge set and weakens guarantees;
its next gate explicitly excludes different admissible interaction domains.
Core §9 defines `J_call` as the actual complete execution image and derives
port directions, but says its finite symbolic presentation remains open.
Parametric-component-linking §7 links supplied templates/maps and proves
forward executable simulation; it neither identifies `P_actual` with that
linked image nor rules out abstract extra successors. Therefore these existing
lemmas compose only after the source-to-complete-endpoint adequacy premise is
supplied:

> For the B-generated role-indexed Function endpoint, its complete denotation
> is represented by the same-fiber linked `J_arg` / entry-rebind / body /
> designated-result-consumer / `J_call` relation, with checked-challenge
> admission preserved independently of comparison success.

This is the source-generation completeness / compositional endpoint-inversion
clause, not another constraint-linking lemma. It is absent even in the
stateless terminating Pure identity case, so the maximal ready fragment does
not currently bridge the primary theorem. No user semantic choice is needed
unless this clause is shown false for an explicit Yulang program; none was
found.

### Direct production-constructor inversion attempt (2026-10-04)

A further constructor-induction attempt located the first missing inverse at
Function introduction. In the current source-to-solver path,
`admit_lambda_fact` constructs a four-child positive Function from parameter,
body-value/effect and result endpoints, then admits the resulting inequality
and provenance. It provides no rule that turns complete-bound membership into
the invocation witness required above (`crates/yu-solver/src/lib.rs`,
`admit_lambda_fact`, around line 10537). The lower-level
`Draft::positive_function` constructor checks and stores those four child
indices only (`crates/yu-types/src/lib.rs`, around line 1822). Typed-core's
lambda clause still supplies just the parameter/body/result skeleton, while B
step 6 still leaves the completed port projection as an obligation.

Thus the missing clause can be stated at one production owner: for a
source-generated Function endpoint `L`, every `O` in its complete denotation
at a checked challenge `c` must have a finite witness through `L`'s existing
argument, entry/rebind, body, designated result-consumer, and `J_call`
composition, preserving the same tuple, scopes, `nu,K,D`, incidence and joint
hiding. Shared type variables, stored provenance, and forward execution
soundness do not yield that inverse. Theorem C has such inversion because its
own bound is defined by the generated positive relation graph with joint
existential hiding; no inspected rule identifies production endpoint
membership with that graph.

This attempt found no unconditional Yulang counterexample and no need for a
new carrier. The endpoint-only `id`/`zero` witness remains conditional because
that interpretation is not required. It does not change the active gate: the
production Function-denotation/constructor crosswalk remains the next action.
No compiler code or tests changed or ran.

The adequacy draft confirms why exact source semantics does not fill the gap.
Its §2 defines `Sem` by collecting exact executions and finite future uses;
§3 requires only `Sem ⊆ ⟦P⟧` for **any** assigned complete-interface
presentation and explicitly permits conservative presentations; §4's exact
embedding `Eν,σ(C)` is a potentially infinite semantic interface built from
source configurations. It never identifies a syntax-synthesized Function
endpoint with `Eν,σ(C)` or supplies endpoint constructors. Thus choosing the
exact embedding as `P_actual` would silently add an endpoint-construction
assumption, while the `{0}` / `{0,1}` countermodel still shows that execution
coverage alone cannot compare two permitted presentations. The single missing
premise is the connection from B's generated endpoint to the existing
same-fiber composition; exactness of `P_actual` is not required.

There is a related **non-authoritative route candidate** in the coupled-effect
draft's Function denotation section: quantify over source-typed call
configurations and bound each `Beh` prefix/result by the function interface.
Its variance argument is sufficient when both functions range over the same
call configurations and preserve captured visibility lineage. For the Pure
identity, exact `Beh` is `Force(D)` followed by returning the rebound value;
this makes the source execution inclusion transparent when the target's
`[b,d]` view admits `d` and the result endpoints agree. But the draft labels
this denotation a candidate and leaves the source-typed contextual domain,
endpoint generation, and finite principal presentation open. It therefore
proves a useful conditional semantic inclusion, not the required comparison
of synthesized `P_actual` and `P_checked`. Using it as the main gate would
still require the same endpoint-to-composition adequacy premise and cannot be
silently promoted to authority.

A further source-checkable-generator attempt does not close that premise.
Removing an independent complete-call bound leaf and assembling the actual
endpoint from receipt/entry/rebind/body/result composition still permits
conservative bounds on those segments. The checked generator then needs a
proved denotational monotonicity law for every admitted segment witness,
including conservative extras, latent views, and resumed suffixes. Merely
retaining graph nodes, occurrence IDs, and evidence references does not prove
that law; stating that all such witnesses survive the `[b,d]` replacement
would restate the missing bound factorization. Likewise, a shared challenge
descriptor does not suffice unless its nonempty admission is generated
independently of query success. The exact adequacy contract currently allows
both failures. This rejects that proposed AST condition as not yet a
source-checkable sufficient premise; it is not a counterexample to a specified
Yulang generator. The callback owner remains source-to-complete-Function-
endpoint generation, whose constructor and admission rules are not yet
defined by B step 6.

The subsequent [source-generated theorem package](../design/2026-10-04-source-generated-callback-structural-theorems.md)
§§2.4–4 supplies a stronger, explicit constructed-generator condition. It
defines positive relation constructors, a checked lift adding only total
definitions of fresh logical coordinates, and independent local source
history admission. Its derivation induction proves conservative extension
with the same complete observation and one joint `ν,K,D`, including local
bound slack; a fresh independent callback delta review found no major gap.
This closes that conditional shared-body lift, not the weaker AST condition
rejected above or B's unrestricted source-to-complete-endpoint theorem.

Governing sources: [callback context delivery](../design/2026-10-03-callback-context-delivery.md)
§§2–5, 7–8; [typed computation core](../design/2026-10-02-typed-computation-core-elaboration.md)
§§6, 8–9; [source interface adequacy](../design/2026-10-02-source-interface-adequacy-theorem.md)
§§2–4; [parametric component linking](../design/2026-10-02-parametric-component-linking.md)
§§3–7; [coupled effect-interface draft](../design/2026-10-01-coupled-effect-interface-core-draft.md)
Function-denotation section. The previous theorem-level attempt and evidence remain in
[value-entry bind/projection](2026-10-04-value-entry-bind-projection.md).

## Structural regularity / finite presentation

**Result: finite residual presentation remains available, but regular-witness
decidability for the full shifted-descriptor/variance fragment is open at one
regular-completion theorem.** No undecidability reduction or source counterexample
was found.

After the existing rational equality quotient and finite-alphabet/atom
normalization, describe each quotient root `q` by address languages
`D_q ⊆ I*` for present paths and `H_q^h ⊆ D_q` for heads `h`. Record heads
carry their exact finite label masks. Each original bound `b` has activation
languages `A_b⁺, A_b⁻`; these retain its identity and orientation rather than
composing successful comparisons. Finite `I` contains tagged Record fields
and ranked-constructor coordinates.

The exact constraints include:

- descriptor equations transport domain and head facts by prefix shift,
  `D_q(iw) ↔ D_c(w)` and `H_q^h(iw) ↔ H_c^h(w)`;
- each active original bound checks local heads and Record width at its current
  address, then descends only through fields required by the current upper
  endpoint;
- descent preserves, reverses, or duplicates orientation according to the
  declared variance, with both directions for invariant coordinates;
- finite permissions and rigid-name identities remain attached to their
  original roots; guards and joint `Phi/K,D` predicates remain separate
  constraints.

A regular assignment induces regular domain/head/activation languages. In the
other direction, regular languages satisfying these coherence, descriptor,
and activation constraints give a finite regular graph assignment and a
post-fixed structural simulation for each original bound. Thus the precise
remaining question is whether this simultaneous finite system has a
terminating regular-completion/decision procedure (or a regular-model theorem
paired with a terminating satisfiability procedure). This statement does not
prove decidability or undecidability.

The tempting direct MSO proof over the ordinary full address tree is invalid.
The descriptor relation `v = 0u` is not an MSO-definable relation there: if it
were, restricting marks to `u=10ⁿ` and `v=010ᵐ` would define equality of the
two unbounded suffix lengths across distinct root branches, which no finite
parity tree automaton can enforce. Reversing addresses makes prefix shifts
local but turns ordinary child descent into a nonlocal prefix operation. This
rejects that MSO route only; it is not an undecidability result.

The standard recursive structural subtype theorem does not directly transfer:
its structural relation requires matching tree domains, while its
nonstructural relaxation uses global least/greatest types. Mandatory Record
width instead requires selective per-field omission while live fields remain
proper types. A proposed fixed-arity encoding with global `Top` admits spurious
solutions unless it separately proves recursive source-image preservation.
See [Niehren, Priesnitz, and Su, *Complexity of Subtype Satisfiability over
Posets*, §§2, 4.1, 5](https://www.cs.ucdavis.edu/~su/publications/esop05.pdf).

An exact follow-up attack resolves the encoding question on its source image.
With a fixed Record product scaffold that distinguishes Record roots from
field payloads even for zero or one labels, encoding absent fields as global
`Top` is an order embedding for image-valid trees: present/present slots
compare payloads recursively, an absent upper slot accepts either case, and
an absent lower slot cannot satisfy a present upper slot. Arrow covariance
and contravariance match Function subtyping. The bounded scaffold preserves
shared descriptor variables, shifted equations, and regularity under
encode/decode.

This does **not** give a decision theorem by adding a regular source-image
grammar to the NPS PDL reduction. Descriptor equations use prefix shift
`x(iw) = child_i(x)(w)`, translated with inverted modalities, while recursive
grammar enforcement needs ordinary suffix-child modalities `w → wi`.
Reversing addresses exchanges the two directions and does not make both
available in NPS's fragment. Its §4.1 states this limitation, and §5's
separate subtype reductions do not establish preservation of the added
recursive sort discipline. Track-wide rigid-name bans are expressible and are
not the blocker. Thus the exact remaining condition for this route is a
solution-preserving, decidably checkable translation of the recursive
Value/Field/Record-scaffold source image into the same-address prefix/suffix
constraint system. No counterexample to regular extension follows, and no
second encoding candidate is advanced.

A direct transfer of the known guarded-BPA undecidability reduction also fails
at a precise premise. DeYoung et al. encode a BPA process by transparent,
parameterized recursive constructor families `t_X[α]`, whose recursive calls
transform the continuation argument; their reduction is stated in §2.3.2 and
Theorem 2.1 of [*Parametric Subtyping for Structural Parametric
Polymorphism*](https://ankushdas.github.io/docs/popl24.pdf). Yulang's scoped
regular fragment instead assigns finite regular graphs to finitely many free
classes; a recursive scheme bound is a binder reference with one lower/upper
pair, not a type-level operator that is re-applied to a changed argument.
The inspected type-declaration authority defers alias/nominal semantics and
does not authorize transparent parameter-changing recursion.

This difference is substantive: for the guarded equations `X = a·X·Y + b·ε`
and `Y = c·ε`, the paper's construction gives
`t_X[α] = {a: t_X[t_Y[α]], b: α}` and
`t_Y[α] = {c: α}`. In `t_X[{}]`, the subtree after `a^n` has a `b` child
consisting of exactly an `n`-long `c` chain. These subtrees are pairwise
non-bisimilar, so this constructed unfolding has no finite regular graph
presentation. This validates the missing-premise distinction; it is not a
Yulang counterexample and does not exclude a separate reduction directly into
finite regular constraints.

### Aperiodic tiling and two-sided marker audit

A further direct Astra attack, independently checked by a
`compiler_referee`, closes a broad but explicitly bounded class of proposed
negative reductions. The finite-model property itself remains open.

First, the arbitrary-tree solutions of the normalized pure structural
fragment with finite rigid permissions are closed under a coordinatewise
**information meet**. For a nonempty family of assignments, matching atoms
and ranked heads retain their head and recurse; Record masks intersect and
retained payloads recurse; incompatible heads produce `Record{}`. Every exact
descriptor keeps its prescribed head, mask, and child equations. For each
original direct bound, endpoints have matching heads memberwise; if those
heads disagree across assignments, both results become `Record{}`. Otherwise
the common head remains, Record upper-mask inclusion follows by intersection,
and retained child comparisons follow the same declared variance. A rigid
leaf survives only if it was the same permitted leaf in every assignment.
Child projection is used only along coordinates retained by the meet. This
closure excludes `Guard`, `Phi/K,D`, effects, optional Records, and any
predicate not proved to preserve the operation.

It rules out an aperiodic Wang-tiling reduction satisfying all of these
conditions: every northeast translate of a legal tiling is realized by a
solution of one fixed package; every arbitrary-tree solution decodes legally;
the decoder is coordinate-independent and reads a finite-depth observation
tuple; a common navigation scaffold makes those observations commute with the
information meet, including the countable family below. If `F : N² → O` is
the finite observation array of a tiling, meet the source assignments for all
its translates. At `(i,j)` the observed value is the meet of
`{ F(i+r,j+s) | r,s ≥ 0 }`. These finite nonempty value-sets decrease as
either coordinate increases. Choose a position with minimum cardinality;
every later northeast set is its subset with the same cardinality, hence the
sets and their meets are constant on that tail. The meet assignment is still
a source solution, so its decoded constant tail is legal. Repeating its
constant tile gives a periodic plane tiling, contradicting aperiodicity.
Finite-depth observations over a finite signature provide the required finite
determination, but the common-scaffold/meet-commutation premise must still be
proved for any concrete encoding. This is not a prohibition on reductions
that realize only an anchored tiling, decode only regular solutions, or fail
these translation and observation conditions.

Second, the least forced-completion rules have a **marker provenance
invariant**. For fixed activation traces, each forced head or field-presence
fact descends from an exact descriptor seed via descriptor-prefix rewrites,
same-address head transfers guarded by an original-bound activation, and
`Present_l ⇒ Head_Record`. Structural suffix descent creates a child
comparison and child liveness, but does not itself create a head or field
marker on the child payload. Therefore, when `Reach` denotes a forced unary
head/presence predicate, prefix stripping plus comparison descent alone does
not derive a two-sided counting implication such as
`Reach_s(a·w) ⇒ Reach_t(w·b)`: the target unary marker and its activated
transfer path must also be derived. This is a precise obstacle to that direct
gadget. It does not rule out feedback where newly generated activation later
unlocks a descriptor-seeded marker; no invariant excluding all such feedback
or exact package realizing it has been found.

The FMP gate therefore remains exactly the joint regular-invariant/finite-
model property above. These audits restrict aperiodic reductions with
finite-depth observation and direct marker-renewal attempts; they do not
prove finite-model reflection or provide a counterexample to it.

Finite constrained residual presentation, regular-witness existence, and
principal/effective projection of the full solution fiber remain distinct
claims. The first is covered by existing scoped residual work; neither a
single witness nor that presentation proves the latter two. Existing bounded
Record saturation remains within its stated scope. No queue-machine candidate
is advanced here. The current structural gate is therefore still the
simultaneous regular-completion theorem, not an undecidability result. For the
literature reduction specifically, the exact absent premise is transparent
parameter-changing recursive type constructors; admitting that premise would
expand language authority rather than follow from regular graph recursion.
The exact feature mismatch is mapped in the
[BPA recursive-constructor transfer audit](2026-10-04-bpa-recursive-constructor-transfer-audit.md):
the reduction needs one recursive definition to act uniformly on arbitrary,
changing type arguments, while this package has fixed child references in a
finite regular descriptor graph. This closes only that direct literature
transfer, not regular completion or other reductions.

### Exact regular-completion premise

A direct Astra attack on the remaining regular-completion gate gives a sharper
proof split, but does not close it. For the normalized pure structural
fragment with finite rigid permissions, the existing least forced-completion
argument characterizes arbitrary-tree satisfiability: finite Horn conflicts
exclude every assignment, while a conflict-free closure decodes to a possibly
nonregular assignment by defaulting unforced present heads to Records. This
arbitrary-tree result is already recorded in
[least forced-completion progress record](2026-10-03-open-residual-factorization.md).
An independent compiler-referee audit found no blocking flaw in the clarified
permission, descriptor-shift, width, and variance clauses; it also confirmed
that this does not prove regularity.

The single unproved premise for a dovetailed decision procedure is:

> Every conflict-free least closure of the existing `D_q`, `H_q^h`, and
> `A_b^±` address facts has simultaneous regular supersets satisfying the same
> descriptor, head, width, variance, and permission constraints without a
> conflict.

Finite regular graph enumeration semi-decides regular satisfiability; finite
Horn-conflict derivations semi-decide arbitrary-tree unsatisfiability. The
premise would make these procedures jointly terminating. It is equivalent to
the arbitrary-tree-to-regular-model property for this normalized fragment,
and remains unproved; ordinary Horn compactness does not supply it. This
formulation reuses the existing address/activation constraints and adds no
semantic carrier. It excludes arbitrary `Guard` and `Phi/K,D` predicates,
effects, and optional Records, so no broader structural or source theorem
follows.

A direct finite-folding attempt identifies why a simple pumping proof does not
follow. Horn closure need not commute with quotienting address occurrences. A
fold can identify an activation `A_b(u)` from one occurrence with an
upper-field fact `D_up(vl)` from another. Saturating their combined state
creates a child activation, which can transport a head through a shifted
descriptor equation into a fixed conflict or forbidden rigid name. Finite
local profiles therefore do not alone prove that a conflict-free closure has
a conflict-free regular extension. No normalized instance where every finite
fold fails was constructed; this is a failed pumping step, not a
counterexample to regular extension or an undecidability result. The required
regular-extension premise is unchanged.

The operators already implicit in the clauses isolate this premise more
usefully. Let `F(A)` be forced domain/head/presence saturation from supplied
original-bound activation languages `A`, including descriptor equations and
permission checks; let `G(U)` be activation closure from facts `U` under the
existing Record-width and variance-directed descent clauses; and let `A₀`
contain the original root activations. The regular-extension theorem is
equivalent to existence, whenever the least joint closure is conflict-free,
of a regular activation invariant satisfying

```text
A₀ ⊆ A
G(F(A)) ⊆ A
F(A) is conflict-free.
```

Sufficiency uses the existing fixed-activation regular saturation and
default-Record completion. Necessity follows because any regular satisfying
assignment induces regular activation languages whose forced facts remain
conflict-free and whose required descents are included. This reformulation
adds no carrier: it exposes the remaining circularity, since ranked heads
decide which orientations descend, while those descents can force new heads
through shifted descriptors. Separate regularity of `F` and `G` does not prove
existence of the joint invariant. No saturation bound or counterexample is
known.

A direct finite-quotient proof attempt sharpens the failure point without
changing the premise. A quotient of address words would need finite-index
congruence under both descriptor prefix transport and structural suffix
descent: `u ~ v` must imply `iu ~ iv` and `ui ~ vi`. The quotient facts must
contain the least closure and remain closed under every Horn rule without
mixing facts into a head, width, variance, or permission conflict. Equating
words by their current finite fact profiles is insufficient because those
profiles need not agree after either context is added. The full contextual
equivalence that is guaranteed to respect both contexts may have infinite
index; requiring it to be finite would additionally regularize the least
closure, stronger than regular extension itself. No finite congruence
construction or counterexample to its existence emerged. The original
regular-extension premise remains the exact main gate.

The quotient condition can be stated as an exact model theorem, which avoids
confusing a quotient of the least closure with a regular solution. Let
`Γ_P` be the complete finite address-constraint package for normalized input
`P`, including domain/head/child coherence, exact descriptor masks and shifted
equations, every original bound activation and its variance-directed descent,
and all rigid permissions. Then:

```text
P has a regular solution
iff
there exist a finite monoid M and a surjective monoid homomorphism
μ : I* → M, with μ(ε)=1 and μ(uv)=μ(u)·μ(v),
such that Γ_P interpreted on M has a model.
```

The interpretation sends prefix shift `iw` to `μ(i)·μ(w)` and structural
descent `wi` to `μ(w)·μ(i)`. For necessity, take a common transition monoid
for the finitely many regular domain, head, and comparison-trace languages of
a regular solution. For sufficiency, lift a finite quotient model along `μ`;
the monoid law preserves both address operations, and the listed coherence,
activation, and permission clauses give regular type graphs and simulations
for the original bounds. Omitting child coherence or checking only for head
collisions would not suffice.

This yields the exact remaining finite-model property:

> Every satisfiable complete address package `Γ_P` has a model over some
> finite monoid quotient, that is, a surjective monoid homomorphism from
> `I*` together with a model of the full quotient constraints.

The converse direction of the equivalence is proved by quotient lifting; the
finite-model property itself remains unproved, with no normalized package
refuting it. This also pinpoints the decision issue: finite quotient models
can be enumerated, while arbitrary-tree unsatisfiability has the existing
finite Horn-conflict witness. These semidecision directions decide regular
satisfiability only if the finite-model property holds; if a satisfiable
package has no finite quotient model, neither enumeration settles that case.
This is an exact reformulation of the same regular-completion gate, not a new
carrier or a second encoding route.
An independent spec-auditor review found the equivalence and conditional
semidecision argument sound; its sole precision finding—that `μ` must be an
explicit surjective monoid homomorphism—has been incorporated above.

### Direct FMP attack: conflict reflection is the exact remaining premise

A bounded Astra attack on the complete finite-model property, followed by an
independent `compiler_referee` quantifier audit, establishes neither FMP nor a
counterexample. Given the recorded characterization of free-address
satisfiability by absence of a finite least-closure conflict, the remaining
claim is exactly:

```text
if every finite surjective monoid quotient makes Γ_P inconsistent,
then the free-address least Horn closure of Γ_P has a finite conflict.
```

This is the contrapositive of
`Sat_I*(Γ_P) -> exists finite μ. Sat_μ(Γ_P)`, and is itself equivalent to
that FMP under the established closure characterization. It is the single
unproved conflict-reflection step; ordinary Horn compactness does not prove it.
Quotient inconsistency can combine an activation and a head/field fact from
distinct address words identified by `μ`; the combination need not be a
conflict in the original free-address closure. Residual finiteness separates
any specified finite set of words, but no finite set of separations is known
to prevent every conflict created by quotient saturation.

The quantifier boundary is material. A negative result requires one fixed
normalized package `P` satisfying `Γ_P` over `I*` while every finite surjective
quotient fails. A failed fold, a selected quotient conflict, or different
failing packages for different quotients is insufficient. Existing results
give finite conflict witnesses for arbitrary-tree unsatisfiability and
enumerable finite quotient models, but do not show those searches cover the
same satisfiability boundary. Independent review confirmed this is an exact
missing-premise localization, not a theorem or counterexample. The next
structural proof action is confined to proving this reflection or constructing
the one fixed counterexample; no new carrier or encoding candidate is added.

### Reviewed finite-feedback quotient theorem and exact rank residual (2026-10-04)

The subsequent [finite-feedback theorem](../design/2026-10-04-structural-finite-feedback-quotients.md)
proves a stronger finite-horizon result without closing FMP. For each fixed
free-satisfiable normalized package and every finite `k`, there is a finite
surjective monoid quotient whose complete closure has no conflict through
`k` head/activation feedback rounds. Regular free-stage domain scaffolds and
one common transition monoid preserve all stage predicates, including
descriptor sharing and full domain/head/child coherence.

The complete finite-quotient saturation makes explicit the Horn implications
already entailed by tagged child coherence. The old free-stage liveness-only
description cannot itself justify default completion on an arbitrary finite
quotient. The repaired fixed-quotient completion lemma and finite-stage
transfer passed independent review; the exact accepted finding and repair
are in [the accompanying progress record](2026-10-04-structural-fmp-feedback-rank.md).

Let `r_P(n)` be the first complete feedback round with a conflict on the
cofinal quotient `eta_n`, formed from all finite quotients of size at most
`n`; let it be infinity for a consistent quotient. Free finite conflict is
equivalent to uniform finite boundedness of these ranks, and a regular
solution is equivalent to eventual infinity. The single unproved premise is

```text
forall fixed normalized P.
  (forall n, r_P(n) < infinity)
    implies (exists B < infinity. forall n, r_P(n) <= B).
```

**Classification C.** A genuine negative package has every rank finite but
tending to infinity. The fixed regular package `q=Function(x,Int), x<:q`
does fail on all length-cutoff quotients with unbounded conflict ranks, but
has another satisfying finite quotient. It therefore refutes only an
unconditional bound over failing quotients. No all-horizons quotient follows
from finite-horizon safety, and no hypothesis is added to the source fragment.

### Direct one-sided-state completion attempt (2026-10-04)

An attempt to extend the reviewed two-sided constructor-bound witness by
defaulting a child state with no constructor-bound anchors to empty Record
fails on the source-generated pure structural package

```text
q = Function(X,R)
X <: q.
```

This package is the `lambda x. x x` structural shadow in the source generator
([source-generated theorem package](../design/2026-10-04-source-generated-callback-structural-theorems.md),
§§2 and 8.1). In the pair-state construction, the root has
`L({X}) = ∅`, `U({X}) = {q}`. Function contravariance creates the child state
`gamma({X},∅)`. Treating that state as unconstrained and choosing empty Record
produces `X = Function(E,E)` and `q = Function(X,E)`, but the original bound
then requires `X <: E`, a Function-to-Record head conflict. Exact shifted
descriptor equations are preserved by this bad assignment; variance-driven
activation is what exposes the conflict.

The package itself has the regular satisfying witness `X=q=μZ.Function(Z,E)`
and `R=E`. Thus this refutes only the premise that an empty side of the
two-sided state permits an independent default. It is not a counterexample to
regular completion or finite-model property. The next theorem still requires
conflict reflection for one fixed address package; any valid construction
must retain the shared endpoint relation through one-sided variance children.
No new encoding, carrier, or semantic rule is introduced by this failed
attempt.

A direct attempt to use the information meet to construct that quotient fails
on a small exact package. Let `F` be Function, `E={}`, `i=Int`,
`R={f:i}`, and impose

```text
Y = F(Y,R)           X <: Y
X0 = F(X1,R)         X1 = F(X0,E)
```

The displayed regular assignment satisfies the bound: the direct simulation
contains `(X0,Y)` and `(Y,X1)`; Function obligations return to those pairs,
and the extra Record obligation `R <: E` is valid by width.

Take the transition monoid of the exact descriptor automaton with states
`F,R,i,absent` and coordinates `arg,ret,f`:

| state | `arg` | `ret` | `f` |
|---|---|---|---|
| `F` | `F` | `R` | absent |
| `R` | absent | absent | `i` |
| `i` | absent | absent | absent |
| absent | absent | absent | absent |

Write `A=μ(arg)`, `B=μ(ret)`, `L=μ(f)`, `T=B·L`, and `0` for the
constant-absent map. The six transformations `1,A,B,L,T,0` have fibers
`{ε}`, `arg+`, `arg* ret`, `{f}`, `arg* ret f`, and all remaining words,
respectively. Thus `μ(argⁿ ret)=B` for every `n≥0`. The exact descriptor
tracks have observations:

| `·` | `1` | `A` | `B` | `L` | `T` | `0` |
|---|---|---|---|---|---|---|
| `1` | `1` | `A` | `B` | `L` | `T` | `0` |
| `A` | `A` | `A` | `B` | `0` | `T` | `0` |
| `B` | `B` | `0` | `0` | `T` | `0` | `0` |
| `L` | `L` | `0` | `0` | `0` | `0` | `0` |
| `T` | `T` | `0` | `0` | `0` | `0` | `0` |
| `0` | `0` | `0` | `0` | `0` | `0` | `0` |

| track | `1` | `A` | `B` | `L` | `T` | `0` |
|---|---|---|---|---|---|---|
| `Y` | `F` | `F` | `R` | absent | `i` | absent |
| `R` | `R` | absent | absent | `i` | absent | absent |
| `i` | `i` | absent | absent | absent | absent | absent |

Define the attempted fold locally: a track is present at class `m` only if
it is present at every address in `μ⁻¹(m)`; its head and Record mask are the
information meet over that fiber; children use right multiplication by their
coordinate. This quotient is coherent and preserves the exact equations
`Y(A·m)=Y(m)`, `Y(B·m)=R(m)`, and `R(L·m)=i(m)` for every `m`. The folded
`X` observations at `1,A,B,L,T,0` are `F,F,E,absent,absent,absent`: across
the `B` fiber, the original returns alternate between `R` and `E={}`; across
the `T` fiber, payload presence does not survive all addresses. All child
domain and descriptor equations still hold.

Nevertheless, the original bound fails at the root's covariant result:
folded `X` has `E` at class `B`, while `Y` has `R`, and `E </: R`. The
source assignments use different comparison orientations at alternating
`argⁿ ret` positions, which the descriptor monoid merges. This refutes this
coherent context-class meet fold, not the finite-model property: the package
already has the regular witness `X=Y`. Whole-solution meet closure applies at
corresponding roots; it does not justify merging different occurrences of
one solution. Any FMP construction must preserve jointly activated,
variance-directed comparisons as well as descriptors and child coherence.
An independent compiler-referee review verified the six-element monoid, all
descriptor/child equations, and the root-result counterexample.

One tempting construction is now ruled out by a finite operator example:
safe regular activation invariants are not closed under union. Take fixed
descriptors `r = {f:Int}`, `t = {f:Bool}` and bounds
`r <: y`, `t <: z`, `x <: y`, `x <: z`. The regular solutions
`x = y = r, z = {}` and `x = z = t, y = {}` induce individually safe
activation families: the first activates `f` only for `r <: y` and `x <: y`;
the second only for `t <: z` and `x <: z`. Their union forces both `Int` and
`Bool` at `x.f`, so its forced closure conflicts. This does not refute regular
extension: `x = y = z = {}` is another regular witness. It shows that
independently safe automata cannot be combined by a union construction; one
joint safe invariant must be selected.

Intersection has the opposite algebraic behavior: monotonicity of
`T(A)=A₀∪G(F(A))` makes post-fixed safe invariants closed under arbitrary
intersection. This still supplies no regular invariant: it presupposes a
nonempty family of regular invariants, and an infinite intersection can be
nonregular even for one fixed package. For `r={a:Int,b:Int}`, `r<:r`,
`X<:X`, every assignment

```text
Dₙ = { aⁱbʲ | i,j≥0 and (i<n ⇒ j≤i) }
```

for `X` is a regular all-Record solution, while `⋂ₙ Dₙ =
{aⁱbʲ | j≤i}` is nonregular (the prefixes `aⁱ` have pairwise distinct
residuals). The package also has `X={}`, so this is not a counterexample to
regular extension. It rules out deriving a finite-state bound by arbitrary
intersection or descending refinement alone; the fixed-activation saturation
construction's state count still depends on the supplied automata.

### Synchronized-signature representative selection fails

A direct attempt to repair representative folding by synchronizing each
address's head/mask signature across all descriptor tracks also fails unless
the fold preserves shifted descriptor sharing globally. Let `R(t)={f:t}` and
use the package `q=Fun(X,X)` with free `X`, no inequalities, and the regular
assignment `X=R^3(Int)`. Under root-first paths, descriptor transport prepends
`arg`/`ret`, while tree descent appends `f`; hence
`q(arg·w)=X(w)=q(ret·w)`. The local signatures
`s=(X:R{f},q:absent)` occur at `f,ff`,
`t=(X:absent,q:R{f})` at `arg,arg f,arg ff`, and
`u=(X:absent,q:Int)` at `arg fff`. Choosing `f` for `s` and `arg ff` for `t`
gives locally coherent transitions `δ_f(s)=s`, `δ_f(t)=u` and root
transitions `δ_arg=δ_ret=t`. The independently folded tracks become
`X'=μZ.{f:Z}` and `q'=Fun({f:Int},{f:Int})`, so
`q'(arg f)=Int` but `X'(f)=μZ.{f:Z}`. This violates the exact shared-root
equation even though each folded track is individually regular and locally
coherent. The original package itself has the regular witness
`X=R^3(Int)`; this rejects the stated representative-selection proof step,
not the finite-model property. Explicit identity labels can repair this bad
choice, but a general construction must prove simultaneous prefix/suffix
compatibility for every shared root. Merely assuming such finite compatible
choices restates the open theorem. An independent architect construction and
compiler-referee delta review checked the path convention, signatures,
transition failure, and regular witness; no theorem status changed.

## Work boundary

These are findings about the unrestricted gates. Callback closure depends on
the one full-bound factorization premise above. Structural closure depends on
the regular-extension premise above; no regularity proof or nonregular-only
counterexample was found. No tests, builds, Oracle runs, measurements, compiler
edits, or design-status changes were made.

The later source-generated theorem package proves two conditional cases,
including a structural construction with closed-anchor components and one
open anchor per remaining component. Its separate
[progress record](2026-10-04-source-generated-theorems.md) records its own
reviews and focused mathematical checks. Neither conditional result closes
the unrestricted gates or invalidates the failed proof routes retained here.
