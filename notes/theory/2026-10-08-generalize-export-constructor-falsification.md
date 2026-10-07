# Generalize/export constructor: minimal structural falsifiers

Date: 2026-10-08
Baseline: `2f85ec1790156a08fab87db677fc0d6c06aceb17`
Branch: `research/simple-sub-intrusion`
Status: unreviewed research checkpoint; bounded structural characterization
Method: countermodel construction, with a deterministic finite truth-table check
Lease: this new note only
Authority/implementation/gate closure: none

## Objective and governing boundary

Attack the candidate bridge from one complete emitted SCC relation, an
eligible/fixed partition and source anchors to a reusable exported view with
independently fresh incoming uses. The strongest surviving result here is
conditional: copying a **supplied legal scoped view**, retaining its complete
relation and all incidences, is a transport construction. It does not derive
that view's source eligibility, admission, nonemptiness or Direct evidence.

The pinned governing sections are:

- Authoritative [inferred Function views](../design/2026-10-05-inferred-function-call-views.md)
  §§1.1–2,5: source annotation/public scheme/internal evidence remain distinct;
  one original jointly scoped `nu,K,D`, stable slots, paths and source scope
  survive Generalize/use; Q cannot construct formation or authority.
- [Charter](../design/2026-09-29-scc-intrusion-redesign-charter.md)
  §§1–5,19–24: the charter's overall status is Reviewed, with the recorded
  user decisions authoritative in their own scopes. F5 Q/R is replacement
  material; independent incoming uses, fixed enclosing sharing and all-member
  visibility are required. Request packages retain dependent fields and
  witness correspondence. Template freshness does not classify Intro22.
- [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
  §§2.1–2.2,3.1–3.6: primitive/DescMem interpretations and typing are
  independently supplied; original scoped binding and complete admission are
  active; source-base realization assumes constructor conformance and
  transformation certificates. Production Option 2 extras remain separate.
- Reviewed [certified use](../design/2026-10-04-certified-callback-and-constrained-use.md)
  §§2–3,4.1,5: whole copying, rigid imports, joint hiding, original binder
  positions, and actual designated-root Direct evidence. §4.1 already
  falsifies independent admission/observation marginalization.
- [DAG](successor-proof-obligations.md) GENERALIZE, ROWS, PROJECTION,
  PRINCIPAL, FRESH-LIFE and CUTOVER: actual semantic binder eligibility and
  anchors remain open; ROWS requires a jointly scoped witness, independent
  admission and original universal worlds/histories; PRINCIPAL is conditional
  on the full upstream contracts and actual `B_common` query evidence.
  Current production cutover remains forbidden.

Existing results are dependencies, not targets for a repeat attack:
[PG-1](../progress/2026-10-06-source-generalization-eligibility-attack.md)
§§3–5 selects repeated projection endpoints and fixed capture anchors in its
bounded source envelope, conditional on the stated complete semantic leaves.
Its §5 already attacks freshening an inner capture, splitting a repeated
formal, and separating Bind/Name client joins. Reviewed
[RS/LX](../progress/2026-10-06-directional-recursive-generalization-supplier.md)
§§3.3–3.4,7.1 construct provenance/lexical import maps while retaining semantic
eligibility as a separate premise. The
[boundary contract](../progress/2026-10-05-scc-generalized-boundary-contract.md),
“Abstract producer/consumer contract” clauses 1–6, supplies the visibility and
failure obligations, without choosing the successor representation.
[Actual-export synthesis](../progress/2026-10-07-actual-export-synthesis-round3.md)
§§3.1–3.2,5–6 already distinguishes finite map construction, scoped strategies
and actual resolver evidence. This note adopts no new language interpretation.

## Candidate assumptions and claim classes

Let `E` be the complete finite source-associated presentation of one SCC,
`Gamma` its independently validated enclosing context, `F` its fixed tuple,
and `L` a candidate owned set. Let `T` be the original binder tree, `I` the
source/provider/path/receipt incidence and `R` the designated roots. A plain
relation `Phi(F,L)` means only its unquantified matrix; `Scoped_T Phi` also
specifies which witnesses may depend on which earlier challenges.

Distinguish these claims:

1. **Weak candidate, falsified below:** complete matrix plus identity
   partition is enough to choose binders/scopes or justify all reuse.
2. **Conditional transport, survives:** if the source has already derived a
   legal `L/F/T/I/R` view and complete primitive/admission transport laws,
   injectively copying all eligible identities, fixing `F`, and preserving
   `T/I/R` transports the whole supplied view. This is the existing certified
   transformation result, not a newly established Generalize theorem.
3. **Bounded characterization:** the embedded check evaluates explicit
   finite relations and named mutations. It proves no primitive/source
   generation law and no source-level acceptance claim.
4. **Established dependency scopes:** PG-1 and RS/LX have their cited reviewed
   local scopes. GENERALIZE, ROWS and source-wide export adequacy do not
   follow from this note. No claim here is independently reviewed.

Even if “complete relation” includes `T`, the bridge still needs a certificate
that the *exported/use presentation retains that tree*. The first falsifier
then attacks discarding it, rather than an absent input. A set `L` can contain
identities from different inner binder positions; membership in the set does
not authorize moving all of them to one boundary.

## Minimal witnesses and exact failed implications

All new finite witnesses below are **structural countermodels**. Their bits
are logical coordinates, not Yulang value descriptors. No complete original
Yulang primitive, descriptor, independent-world or source-admission package
has been constructed for them.

### 1. Binder placement and forall/exists exchange

Take domain `B={0,1}` and matrix `Phi(k,e) := (e=k)`, with `k` an independently
chosen challenge and `e` an owned local witness. The partition and all
unquantified atoms are identical in:

```text
A = forall k. exists e. Phi(k,e)       true: choose e=k
B = exists e. forall k. Phi(k,e)       false
```

For B, `k=0` forces `e=0`, while `k=1` forces `e=1`. Two challenge values
are necessary for this separation; on a singleton domain both formulas have
the same truth. The dual placement also exposes an unsound permissive
rewrite: replacing a required shared outer `exists s. forall k. s=k` by
`forall k. exists s. s=k` changes false to true. “Every binder is fresh”
does not distinguish these directions.

This is relevant to original challenge/world/history scopes, not a proposal
to implement explicit Skolem functions or to add rigid IR constructors.
The generalizer must preserve the original strategy dependencies. The
checker does not establish which Yulang constructor produces either tree.

### 2. Root covariance and premature member projection

For two member observations let

```text
J(r_f,r_g) := (r_f=r_g).
pi_f J = B; pi_g J = B; (pi_f J) x (pi_g J) = B x B.
```

The product admits `(0,1)`, which J excludes. Neither root has lost a
marginal value. One bit per member and two members suffice; no larger cycle
or recursive unfolding is needed. This falsifies *root marginal equality
implies complete generalized SCC interface equality*. Retaining J behind
separate member accessors survives the attack. Two independently fresh
incoming instances of the **whole** SCC may legitimately choose different
diagonal values; the forbidden tuple combines two roots inside the same
whole instance without its correlation.

This is a structural relation witness, not a theorem that Yulang's selected
recursive pair has the equation `r_f=r_g`. The already constructed native
recursive interfaces retain their own original meanings.

### 3. Witness ownership across uses and within one use

Let one legal per-use local witness satisfy `Phi_u(e_u) := (e_u=u)`, for
two incoming uses `u=0,1`. Independent local scope admits
`exists e_0,e_1. Phi_0(e_0) and Phi_1(e_1)` with `(e_0,e_1)=(0,1)`.
Caching one satisfying evidence value globally replaces it by
`exists e. Phi_0(e) and Phi_1(e)`, which is false. A fixed use-map graph
can therefore support different legal witness assignments; it must not be
confused with one ground witness chosen at export time.

Conversely, if the source says **one shared witness within a single use**,
`exists s. s=0 and s=1` is false, while separately projecting its segments,
`(exists s_0. s_0=0) and (exists s_1. s_1=1)`, is true. The correct transport
copies a scope with all its incidences once. Independence across eligible
uses gives no independence within that scope, across history segments, or
for fixed imported evidence.

These are minimal corroborating mutation instances, not new eligibility
results: RS §7.1 already describes the independent/shared placement cut and
PG-1 §5.3 already excludes segment-wise source joins. The new discriminator
is explicit **evidence assignment caching versus finite map construction**;
an injective identity map alone does not certify evidence reuse.

### 4. Fixed captured/import/world coordinates

For a fixed enclosing coordinate `f=0`, matrix `y=f` admits only `y=0`.
Replacing that same fixed import by existentially fresh `f_u` admits `y=1`
using `f_u=1`. Two values and one dependent observation suffice. The
freshening may be total and injective on the wrong set and still fail to
fix Gamma's original coordinate.

This is a mutation control, not a repeated source attack: PG-1 §5.1 already
supplies the conditional captured-closure witness and its source-realization
limit. The same algebra can name `f` a world coordinate, but that renaming
does not construct a Yulang world. A world is not authorized for freshening
by lexical locality or absence from printed ports. Actual fixed-world
identity and any permitted current-state evolution remain original semantic
premises.

### 5. Source anchors cannot be reconstructed from a root shape

Let two source-incidence records have the same descriptor `d`, but original
anchors `beta_0 != beta_1`. Suppose an independently supplied authority
predicate licenses only `beta_0`. Erasing the anchor maps both to `d`.
Reconstructing permission by `exists beta. shape(beta)=d and licensed(beta)`
then licenses `beta_1` with `beta_0`'s witness. Two anchors, one descriptor
and one licensed record are the smallest collision.

The finite authorization predicate is stipulated for the structural model.
Its connection to a Yulang effect permission is not proved. The
source-applicability conclusion is narrower and already authoritative:
Function views §2 forbids forming slots/paths/receipts/authority from shape
or Q success, and requires their stable incidence through Generalize/use.
A valid transport retains the original anchor mapping even when descriptor
substitution gives equal type shapes. An anchor label alone, without its
original proof and transitive dependencies, also fails the full contract.

### 6. SCC publication before all members validate

Two-member failure trace:

```text
predeclare f,g
stage f successfully
make f visible to an incoming reader
reader obtains f
validation/finalization of g fails
abort SCC
```

If “reader obtains f” is an observable successful publication, abort cannot
retroactively make this trace contain no successful component publication.
The counterexample needs two members to distinguish member success from
complete SCC success, and one reader between installations. It uses no
solver equation and asserts no particular compiler interleaving. Staging f
internally, then failing g, with **no reader visibility**, survives: physical
installation need not be indivisible. The required barrier concerns logical
visibility of a complete validated snapshot, as the charter explicitly says.

## Surviving construction and remaining source head

Fix independently justified primitive/admission meanings, a legal source
view `(F,L,T,I,R)` and its complete relation. For each incoming use u choose
one injective, sort-preserving, capture-avoiding map on its eligible owned
identities, fixing F, with pairwise disjoint eligible images for distinct
uses. Copy every repeated occurrence, scope reference, original residual,
provider/evidence incidence and root with that same map. Add all caller
constraints jointly to the enclosing context; keep any original scoped
witnesses at their original positions. Only a validated all-member result
becomes visible. These conditions exclude all six mutations above.

The conditional proof is syntactic substitution/induction over the supplied
presentation, using the independently established primitive transport laws.
Inverse renaming recovers each use-indexed original, while fixed identities
remain one original tuple. This does not select L, derive a legal export,
prove the residual satisfiable, or supply `Direct(R^fresh,R_V)` at the
designated export. That last proof is necessary for ordinary-use factorization
in certified-use §5.2; even semantic containment alone cannot force an actual
resolver to accept a nonidentity query.

The precise blocker is therefore the **source-derived legal scoped view and
its complete admission/evidence certificate**. LX's lexical partition,
nominal freshness, root covariance, and source anchor names are already
available inputs, but do not establish this semantic head. These experiments
leave it untouched. A larger Boolean enumeration would not help. The next
method should examine the owning source Generalize constructor's retained
certificate for one selected source boundary, with the original tree and all
actual evidence accessors, rather than create another equivalent toy model.

## Reproducible finite check

The check below has no randomized seeds: it enumerates all 16 binary
relations on `B x B`, plus six fixed mutation controls. The quantifier oracle
and marginal-product oracle are direct set comprehensions over the explicitly
stipulated relation, separate from the listed transformation formulas. They
share the finite domain and relation interpretation. Their agreement with
the hand derivations checks the model arithmetic, not source semantics or
independent mathematical review. No compiler transition evaluator is used.

```python
from itertools import product

B = (0, 1)
points = tuple(product(B, repeat=2))
exchange_gaps = []
covariance_gaps = []
for mask in range(16):
    rel = {p for i, p in enumerate(points) if mask & (1 << i)}
    forall_exists = all(any((k, e) in rel for e in B) for k in B)
    exists_forall = any(all((k, e) in rel for k in B) for e in B)
    if forall_exists != exists_forall:
        exchange_gaps.append(mask)
    left = {x for x, _ in rel}
    right = {y for _, y in rel}
    if rel != set(product(left, right)):
        covariance_gaps.append(mask)

assert exchange_gaps == [6, 9]
assert covariance_gaps == [6, 7, 9, 11, 13, 14]
eq = {(0, 0), (1, 1)}
assert all(any((k, e) in eq for e in B) for k in B)
assert not any(all((k, e) in eq for k in B) for e in B)
assert (0, 1) not in eq and (0, 1) in set(product(B, B))
assert any(e0 == 0 and e1 == 1 for e0, e1 in product(B, B))
assert not any(e == 0 and e == 1 for e in B)
assert any(s0 == 0 for s0 in B) and any(s1 == 1 for s1 in B)
assert not any(s == 0 and s == 1 for s in B)
fixed_f = 0
assert not (1 == fixed_f)
assert any(1 == fresh_f for fresh_f in B)
shape = {"beta0": "d", "beta1": "d"}
licensed = {"beta0"}
assert "beta1" not in licensed
assert any(shape[b] == shape["beta1"] for b in licensed)
trace = ("stage_f", "read_f", "fail_g", "abort")
assert trace.index("read_f") < trace.index("fail_g")
hidden_trace = ("stage_f", "fail_g", "abort")
assert "read_f" not in hidden_trace
print("16 relations; quantifier gaps=2; covariance gaps=6; six controls passed")
```

Reproduce without writing a checker/output file:

```sh
python3 - <<'PY'
from pathlib import Path
p = Path('notes/theory/2026-10-08-generalize-export-constructor-falsification.md')
code = p.read_text().split('```python\n', 1)[1].split('\n```', 1)[0]
exec(compile(code, str(p), 'exec'))
PY
```

Failure conditions: changed domain/relation semantics; altered original
binder dependency; added legitimate source rule licensing the questioned
transport; evidence that a supposed fixed coordinate is source-eligible at
that particular boundary; or a reader semantics in which the partial member
is still unobservable. A different view may evade a mutation while still
requiring its complete constructor/admission/Direct proof. No acceptance
comparison, compiler test/build, unbounded search, recursive operational
execution, method resolution, mutable State or production-extra enumeration
was performed.

## Resource and handoff record

Process budget: one lightweight deterministic Python check; no Cargo/build
process; no scratch or log outputs; finite 16-relation range, no seed; 60 s
timeout. Dependency/whitespace bookkeeping uses narrow read-only commands.
No production/test/shared/question/Git write, child agent or user question.
CPU/RAM were not measured; actual process duration and final dependency
fingerprints are supplied in the submission report. Larger domains remain
unsearched, and no in-language minimized source counterexample is claimed.

Freeze check result: the embedded command above passed with
`16 relations; quantifier gaps=2; covariance gaps=6; six controls passed`.
The Python calculation took 0.001256 s by `time.perf_counter`; this excludes
interpreter startup and research/read time. `git diff --check -- <leased path>`
passed; since the path is untracked, a separate Python scan also verified
every note line has no trailing whitespace. No wall-clock research timer or
peak memory measurement was taken.

Direct dependency fingerprints below name **committed baseline bytes**.
Eight live inputs matched those bytes at freeze. The live DAG was changed
by another owner: its observed SHA-256 was
`f5f8fc77afb3516a5fdc6eed8e4c47528674d7c9d928799a5a5a31686596be2f`.
Its uncommitted contents were not consumed; statements about DAG status in
this note refer only to the pinned baseline. The primary must reconcile
this change before applying the note to a later DAG snapshot.

| Dependency | Baseline SHA-256 |
| --- | --- |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-04-certified-callback-and-constrained-use.md` | `887bc7c0743d2f34608b46ccb8e5ee9b58ea4a39995b93a5aaced764295bae80` |
| `notes/theory/successor-proof-obligations.md` | `7f8b42631758762bd71ddabe0e82981862fe2800f70c60f6656718f6836f0e71` |
| `notes/progress/2026-10-06-source-generalization-eligibility-attack.md` | `2445a67ab8ce3372e7acd62fd90d598ca1ea3bc92872ff9b8588f176fc077d3e` |
| `notes/progress/2026-10-06-directional-recursive-generalization-supplier.md` | `2f169e0f894fff8695cf8e1ef40f5a9734abfe87484d9db6aab23eae941b8898` |
| `notes/progress/2026-10-05-scc-generalized-boundary-contract.md` | `9e117cac7bf5566d231b8cd7499222913ba639510d33d9a99d62b50118b40271` |
| `notes/progress/2026-10-07-actual-export-synthesis-round3.md` | `27f66d5d6167fc42f7757cef7b916410ff8332b9b8057e8fd314e304b147762a` |

Recommended next action: audit one selected source Generalize constructor
certificate for the original eligible/fixed/tree/incidence/admission package,
then test its actual ordinary exported-root query. Reuse PG-1 and RS/LX;
avoid additional capture or port-splitting probes.

Commit packet:

- Exact leased path: `notes/theory/2026-10-08-generalize-export-constructor-falsification.md`.
- Baseline: `2f85ec1790156a08fab87db677fc0d6c06aceb17`.
- Dependency changes: live DAG differs from its baseline fingerprint as
  recorded above; no other direct dependency changed at freeze. Only
  committed baseline bytes were consumed.
- Review status: producer-authored, unreviewed research; no independently
  reviewed theorem, gate promotion or production authority.
- Checks: embedded finite truth-table check and leased-path whitespace check;
  exact commands/results in the submission report. No compiler tests/builds.
- Proposed checkpoint message: `research: falsify weak generalize export bridges`.
- Shared-record deltas intentionally deferred to primary/curator: preserve
  existing GENERALIZE/ROWS/PRINCIPAL/CUTOVER statuses; record binder-tree and
  evidence-scope preservation as retained premises; cite existing capture,
  port-correlation and hiding countermodels rather than reopening their
  completed bounded results. No task/index/authority/question change proposed.

Writes stop before submission; this artifact is frozen for review.
