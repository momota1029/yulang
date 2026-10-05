# Bounded residual admission retraction model

Date: 2026-10-05
Status: Independently reviewed bounded conditional characterization; no implementation authority
Baseline: `4b093702f`
Exclusive outputs: this note and `tools/research_residual_admission_retraction.py`

## Question and claim boundary

Inputs are [open residual factorization §§2–7](../design/2026-10-03-open-residual-factorization.md), [scoped structural projection §§2–6](../design/2026-10-03-scoped-structural-projection.md), and the [reviewed multi-atomic structural image proof](2026-10-05-multi-atomic-record-projection-proof.md). The latter supplies the closed-copy/fresh-root graft, whose pure structural image does not establish joint admission.

The checker tests the conditional premise

```text
A(T, omega) => A(G_H(A+(T)), omega)
```

on an explicitly finite domain. `A` includes propagated permissions, supplied original bound guards and a supplied `Phi`. Every candidate uses the same fixed `omega`; request and owner identities are never resampled. An invariant predicate compares the candidate against a fixed original anchor graph, which also remains unchanged. The reference existential quantifies over the original admitted assignments in the finite domain; the candidate existential admits only one canonical graft for each projected image. Both retain the original joint coordinates. Visible upper queries are evaluated on those same assignments.

Result: whenever the premise holds across this finite domain for a fixed `omega`, the admitted images and all enumerated visible upper query answers coincide. The model also finds minimal omitted-premise failures. This is finite conditional consistency evidence, not a proof that source permissions/guards/Phi satisfy the premise, an effective inference procedure, or a proof of the unbounded theorem.

## Exact finite envelope

Atoms: identity-only visible `Int`, hidden `kappa_a`, hidden `kappa_b`. Labels: `a,b,c`. Two mandatory-hidden packages:

- `H={a:kappa_a}`; root `c` absent; root `b` optional.
- `H={a:kappa_a,b:kappa_b}`; root `c` optional.

Each package exhaustively generates reachable graphs with one or two constructor nodes. The root has its listed required fields and its single optional extra. An extra child ranges over absence, all three atoms and every constructor index. A second constructor ranges over every Record on `a,b,c` with those child choices, or every Function with the non-absent choices in both argument/result. Atom leaves do not count as constructor nodes. All edges are constructor edges, so cycles are contractive. Disconnected two-node graphs are omitted. Each package contains 246 original presentations.

The finite comparison domain additionally contains the canonical closed-copy graft of each of the 70 projected bisimulation classes. This gives 316 presentations per package. The checker chooses one graft per class using the last encountered visible representative in its source enumeration. These supplemental graphs can have more than two constructor nodes: projection creates at most four signed constructor nodes from a two-node source, and the graft adds one fresh root. They close the candidate witness set; this is not exhaustive enumeration of all graphs up to five nodes. Alternate presentations of one image use a common representative only because every supplied predicate is invariant under rooted bisimulation.

Visible upper queries exhaustively contain every one-constructor visible Record graph on `a,b,c`, with each child absent, `Int`, or the root itself: 27 queries, including the empty Record. Functions and larger visible query graphs are not exhaustively queried; one recursive Function graph is a separate targeted case.

For each predicate, `Omega` has exactly 64 tuples:

```text
(permission_mask, original_bound_guard_atom_mask, request_id, owner_id)
in {0,1,2,3} x {0,1,2,3} x {0,1} x {0,1}.
```

Bit 0 denotes `kappa_a`, bit 1 denotes `kappa_b`. `permission_mask` represents the already propagated intersection for this class; the program does not simulate equality quotient propagation. All four possible propagated outcomes are covered. Permission admission requires every reachable hidden name of the candidate to lie in that mask. Bound guards check the unchanged bound context and its required hidden atomic child comparisons. Visible upper comparisons reach only visible atomic comparisons; `Int` is universally admitted in these supplied contexts. This supplied guard law is a model assumption, not a source bridge or an assertion about arbitrary source guards.

Six supplied `Phi` families are enumerated:

1. `true`.
2. `extra_hidden`: the root extra is `kappa_a`.
3. `invariant_fixed`: mutual structural equality with the fixed original Record carrying the required fields and `extra:kappa_a`.
4. `request_owner`: request identity equals owner identity, with both fixed in `omega` and distinct from graph/root identity.
5. `request_sensitive_extra`: request equals owner, and request 0 requires the hidden extra while request 1 requires its absence.
6. `visible_query`: the fixed visible query `{c:Int}` succeeds.

All families also conjoin permissions and bound guards. Across two packages, this means 768 predicate/Omega configurations. A separate three-point finite image domain enumerates all eight Boolean admission predicates; six satisfy the one-way premise and all six preserve the image.

## Minimal omission counterexample and attacked shortcuts

Take nonempty `H={a:kappa_a}`, with permissions and guards admitting `kappa_a`:

```text
T = {a:kappa_a, b:kappa_a}
A+(T) = {}
G_H({}) ~ {a:kappa_a}
Phi(T) = root has b:kappa_a.
```

The original witness satisfies `Phi` and `T <= {}`. Its canonical graft fails `Phi`, so canonical checking rejects an inhabited original admitted fiber. This uses one constructor node, one hidden atom identity and two root labels. Within nonempty-H packages, requiring one distinct extra root field needs at least those two labels; no recursion or extra node is needed. The same pair also refutes replacing invariant mutual comparison against original `T` by a predicate of the positive projection: the projections coincide, but only the larger Record equals the original anchor mutually.

Request/owner coordinates can be unrelated to representation identity and still matter. In the request-sensitive family, `(request,owner)=(0,0)` admits the larger witness and rejects its graft. Resampling them to `(1,1)` would admit the smaller graft, but evaluates a different original joint package. Pure request/owner equality itself is preserved by grafting; this distinguishes fixed correlation from a prohibition on request identities.

A graph-root-identity predicate is a separate inadmissible shortcut under the bisimulation-invariant contract. The checker exhibits two distinct presentations `mu z.{c:z}` and a two-node `{c:{c:...}}` cycle with the same bisimulation image. Representation identity can distinguish them; it is outside the conditional predicate contract, rather than an established source constraint.

Contravariant feedback attacks naive root mutation:

```text
V = mu z.{c:Function(z,Int)}
naive = mu z.{a:kappa_a,c:Function(z,Int)}
A+(naive) = {}
A+(G_H(V)) ~ V.
```

Adding the hidden field to the existing recursive root makes its negative state unavailable and drops the positive Function field. The proper graft keeps the Function argument inside the closed visible copy. This is a targeted three-constructor graft, not an exhaustively enumerated three-node source family.

## Differential reference, results and omissions

Projection uses descending greatest signed availability and shared signed-node construction. The structural query reference independently traverses all required endpoint-pair obligations and rejects exactly upon a reachable local mismatch. Bisimulation uses partition refinement. Reference and candidate share the stated structural rules, visibility classification and admission predicates. They do not share the projection algorithm, but neither oracle validates source generation or source guard behavior.

The final run performed 51,192 explicit structural reference comparisons to check each domain graph, its projection and its canonical graft against the 27 visible queries. Permission monotonicity was checked by comparing reachable hidden-name sets: graft names are a subset of the original witness names. Under these supplied identity comparison guards, mandatory hidden child obligations remain identical.

For `true`, `request_owner` and `visible_query`, all 64 Omega values satisfy retraction for each package and none differ in admitted images. Extra-hidden and invariant-anchor predicates each fail the premise and image equality at 16 Omega values for one required hidden atom and four Omega values for two. Request-sensitive extra predicates fail at four and one values respectively. Other failures are vacuously prevented by rejected permissions/guards/request correlation. All configurations satisfying the premise preserve admitted images and enumerated visible upper answers.

No random seeds, partial enumeration, timeouts, builds, repository tests, compiler edits, or Git operations occurred during model construction. Two single-process probe invocations were run by the producer, the second after removing a redundant predicate and correcting resource reporting/request correlation. The first result was exploratory; only the final script and final result described here are retained. Their measured calculation CPU times were 1.562653 s and 1.173111 s, and internal wall times 1.527630 s and 1.141333 s: aggregate calculation CPU 2.735764 s and wall 2.668963 s. Each process enforced five-second CPU/wall termination and 256 MiB address-space limits. The final process reported Linux `VmHWM=12800 kB`, `VmPeak=18672 kB`. `getrusage.ru_maxrss` initially inherited a launcher high-water history inconsistent with current `/proc/self/status`; it is deliberately not reported as this probe's memory use. The primary reran the final command once at HEAD `bededb371`; it passed with 64 coordinates per predicate, 51,192 structural reference comparisons, and all targeted attacks passing.

Reproduce: `python3 tools/research_residual_admission_retraction.py`.

The unbounded theorem, arbitrary guards/Phi, many open classes, full equality quotient, arbitrary labels/atom alphabets, effects/invariant constructors, source inference and effective joint solving are omitted. Model success cannot establish the required predicate-transport premise. Recommended next action: adjudicate the premise against actual source admission laws; retain the original existential witness whenever those laws do not imply retraction.

## Frozen dependency and commit packet

An independent `spec_auditor` review found one minor reporting mismatch:
the note previously said “first encountered” while the checker keeps the last
representative for repeated bisimulation keys. This sentence now matches the
checker. The reviewer found no blocking or major issue in the bounded model.
Review was static; it did not rerun the probe or reproduce the recorded totals.

| Dependency | SHA-256 |
|---|---|
| `notes/design/2026-10-03-open-residual-factorization.md` | `02e6e04d1a4eea405442587206e34c653b45405677d653e6bfec37568fee4f43` |
| `notes/design/2026-10-03-scoped-structural-projection.md` | `b1b7e675902820d6e5d4488c656ab11332b4fc2f54dd64e0fa2cd2e5cf5519a0` |
| `notes/progress/2026-10-05-multi-atomic-record-projection-proof.md` | `28548a4f1702f997f625fd4bc8b5f0925247618155c731deecab2e8538613208` |

Baseline: `4b093702f`. Dependencies were read and hashes captured; no observed dependency change. The primary must recheck these against the pinned/current branch before integration. Frozen leased paths:

- `tools/research_residual_admission_retraction.py`
- `notes/progress/2026-10-05-residual-admission-retraction-model.md`

Claim/review status: statically reviewed bounded conditional model; reported run was not independently reproduced. Checks already run: final deterministic probe command above. Proposed checkpoint message: `research: bound residual admission retraction and omitted-premise failures`. Shared changes intentionally deferred: `tasks/current.md`, `tasks/research-lab.md`, theory/status maps and `notes/design/INDEX.md`. Proposed shared delta: record the omitted-premise counterexample and finite sufficiency evidence, retaining the source predicate-transport obligation and all production boundaries.
