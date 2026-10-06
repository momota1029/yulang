# Effective scoped projection: finite incidence, name orbits, and the FMP cut

Date: 2026-10-07 (session UTC date 2026-10-06)
Baseline: `ad514061de2792c374a4b5c224dff7f4772906e8`
Status: independently reviewed restricted construction and metatheorem obstruction
Exclusive lease: this note and `tools/research_successor_effective_projection_round2.py`
Semantic/implementation authority: none
Independent review: [round-2 compiler/spec review](2026-10-07-successor-round2-review.md); both clean within the stated observer/rule class

## Result and exact delta

There is a constructive finite quotient for **identity-only hidden name
coordinates**, and it supports effective projection without a finite universe
of actual names, worlds, or source executions. It constructs the finite
incidence context carrier from a specified relational rule algebra rather
than importing an already finite `J_T`. It also constructs witness strategies
at the original binder positions, including existential/universal alternation.
Its projected relation is the whole correlated relation, not a product of
member projections. Independent admission clauses remain independent clauses.

These are two restricted mathematical sublemmas for `CTX_FINITE` and
`PROJECTION`. Neither is an unrestricted source-gate closure. Applying them
to actual source rules requires showing that the actual context operations
and every observer of an eliminated name have the stated finite syntax. The
inspected source packages do not yet provide that correspondence. This note
does not count an assumed source interpretation as a derived source rule.

A concrete obstruction establishes a sharper negative boundary: finite
syntax, finite nominal support, and decidable checking of each individual
regular candidate together do **not** imply a computable complete joint
candidate bound. One decidable primitive inspecting finite mandatory Record
chains suffices for a halting reduction in a mathematical extension of the
pure package. This is not a source counterexample or an undecidability theorem
for Yulang. It pinpoints the extra reflection law that an actual primitive
must supply before pure FMP can be reused.

Quantified delta: two constructive restricted sublemmas; one general
nonimplication theorem; zero unrestricted successor gates closed; zero
independent membership/admission clauses or source acceptance rules adopted.
The existing actual-export Integer/Top and nonidentity `VIncl` cuts remain.

## Inputs and retained meaning

The governing inputs are the current DAG `CTX_FINITE`, `JOINT_DEC`,
`PROJECTION`, `IFACE_FORM`, `CI_ALPHA`, `CI_USE`, `ALL_VIEW`, and `PRINCIPAL`;
the scoped constraint-solving package §§1–2, 5; source-context finite closure
§§2–6; open residual factorization §§2–7; reviewed pure FMP §§1–2, 9–11 and
its reviewed effective-decision corollary; global synthesis §§2, 5–6;
recursive synthesis §5; certified uses §§2, 5–6; and the whole-relation,
actual-export and Integer `VIncl` attempts. Direct dependency hashes are
recorded below by the single checker run.

Fix the original source occurrence/binder tree `T`, original `X`, and original
`xi=(nu,K,D)`. All structural/effect endpoints, runtime providers, source
occurrences, receipts, origins and original opening identities retain their
original sorts, scopes and incidence. Runtime provider identities are not
automatically eligible names. Eligibility to hide/freshen remains a separate
Generalize/source judgment. A hidden name in this note is eligible only if
that judgment already permits the displayed binding.

`J_T` denotes comparison contexts, not independently valid semantic worlds.
Independent all-world, descriptor and admission predicates are not defined by
successful quotient construction, finite support, observed support, or query
success. In particular, an ordinary guard in a quantified challenge formula
is still its original independently interpreted `D`, not solver-produced
membership.

## 1. Deriving a finite context carrier from relational operations

Let `I` be the disjoint union of finite static ports supplied by a finite
typed derivation: endpoint ports `P`, binder ports `L`, witness ports `W`,
source/evidence ports `E`, and original obligation ports `B`. Port sort and
binder ownership are constants. Sibling openings have different ports even
when spelling and numeric depth agree.

Specify a finite context signature `(R_1:k_1,...,R_m:k_m)` over `I`.
A context is the tuple of finite relations `r_i subseteq I^k_i`. For example,
one unary relation records original declared assumption ports, one binary
relation records permitted opening incidence, and another records witness
correspondence. These examples do not choose production fields. Any additional
actual observer must have an explicit entry in the signature or remain an
unchanged external operand.

The permitted child-context expressions are finite relational algebra over
this signature: union, intersection, difference, coordinate permutation,
projection, relational join/composition, restriction to static sorts/owners,
and insertion/deletion of tuples of existing ports. Alias transport acts by
an explicit port map, preserving original identifiers through a retained root
map. It may not create a fresh history ID or an unbounded constructed term.
Original guard interpretation and source-rule soundness are separate; the
construction does not assert that any displayed operation is a legal Yulang
source operation.

**Incidence-context theorem.** For rules given in this syntax, a computable
context carrier is

```text
J_inc = product_i PowerSet(I^k_i)
|J_inc| = 2^(sum_i |I|^k_i).
```

Encode each relation by its bit vector in the fixed lexicographic static-port
order. Each permitted relational expression is a total terminating operation
on these vectors and stays inside `J_inc`. Identity of contexts is equality
of their complete vectors. No source-relevant entry is forgotten merely to
make the key finite. Because every rule sees precisely these relations and
unchanged external operands, equal encodings give the same rule arguments;
preservation and reflection of context observations follow by induction on
the expressions. This is stronger than arbitrary alpha freshness and weaker
than assuming a finite space of structural assignments or semantic worlds.

Use canonical comparison states `(b,j,u,v)` as before. Rule labels retain
the rule identifier, static operand incidence and ordered premise/conclusion
state references. If the maximum total edge-reference arity is `r` and the
finite non-reference label alphabet has size `A`, the number of states is at
most `M=|B| |J_inc| |P|^2`; the number of labelled hyperedges is at most a
finite sum of terms `|Rules| A M^r`. Recursive derivations use back-references.
Conjunctive parents stay conjunctive; alternatives stay different rules or
root alternatives. No nested proof-history term is stored in a label.

For updates, include permission and alias information as finite relations.
If the actual update rules add facts monotonically, or remove only previously
present permission tuples and merge alias classes, their changes terminate:
there are finitely many relation bits and alias merges. Fair rechecking of
the dependent states then terminates. An arbitrary invalidation rule that can
toggle a bit forever does not satisfy this update premise. Finite carrier
alone cannot prove update termination.

This derives `J_T` and the canonicalizer from a **checkable syntactic rule
class**. The seven abstract premises of source-context finite closure are
replaced, within this class, by finite signature/relational-expression checks,
static source-port ownership, and the stated monotone update discipline.
The source-preserving law for the actual rules is still needed. The finite
representation-preserving checking corollary supplies initial source ports;
it supplies neither this source rule inventory nor general instance closure.

An observer of depth, constructed type shape, ordered unbounded history,
fresh runtime provider identity or a recursive proof tree invalidates the
class unless separately represented by a sound finite schema. The
`t -> Box(t)` recurrence is consequently outside it, rather than silently
identified by alpha renaming.

## 2. Exact orbit projection at the original binders

Let `A` be an infinite countably enumerable set of one name sort, with
decidable equality. These are semantic atom values, distinct from the fixed
syntactic binder-port identities. A binder port is never renamed into a
sibling merely because both may receive the same atom value.

Consider a finite scoped formula whose eligible hidden atom coordinates
occur only in equality/disequality literals, finite Boolean combinations,
and their original atom quantifiers. Every other atom-dependent predicate,
including any independently defined `D`, must have an independently justified
finite Boolean expansion in those literals. Non-name predicates
`G(X,xi,w,...)` can remain arbitrary original predicates, but they must not
read an eliminated atom. Their complete original tuple and binder scope stay
in the residual. This is an exact observer restriction, not a claim that
equivariance alone implies it.

All fixed atom constants and public atom ports are recorded. For a current
valuation of earlier atom ports, let `S` contain their distinct values and
fixed constants. The permutations of `A` fixing `S` have exactly `|S|+1`
orbits on the next atom: each singleton in `S`, and the complement `A-S`.
Consequently a binder may be evaluated against one representative of each
of these classes, using one new symbolic fresh representative for `A-S`.
Future binders extend the current equality partition; they do not reuse a
fresh representative independently at different occurrences of one binder.

**Scoped orbit-projection theorem.** Bottom-up orbit evaluation constructs a
finite Boolean residual for the exact projected whole relation. It preserves
truth and permitted witness strategies at every original binder, for every
original `X,xi` and every other unmodified world/challenge parameter.

Proof: equality and disequality are invariant under permutations fixing the
current `S`; the hypothesis gives the same property for every eliminated-name
observer. Unchanged `G` leaves have identical arguments. Boolean connectives
preserve the correspondence. At an existential atom binder, every original
witness belongs to one representative class, and every representative has
an actual witness in its class. At a universal atom binder, each original
atom is carried to its representative by such a permutation, so checking all
representatives is equivalent to checking every original atom. Apply this
argument recursively with the enlarged equality partition at that binder.
No quantifier is moved across another binder. The proof is structural
induction on the original finite formula/binder tree, not per-world choice
of a new presentation.

Witness preservation is explicit. Choose the successful representative branch
at its existential node as a function of the permitted earlier valuation.
If it is a singleton, use that earlier atom. If it is fresh, choose the first
enumerated atom outside the current finite `S`. Under a later universal move,
transport the subsequent strategy by the same permutation of the whole
remaining tuple. Conversely an original winning strategy supplies the
successful orbit branch at that node. The constructed strategy cannot depend
on a later challenge; an existential binder before that challenge chooses
once at that position. Witnesses in siblings share only the coordinates
shared in the original formula.

For a finite presentation with `k` atom ports and `s` distinct fixed atoms,
the number of complete equality patterns is at most `(s+k)^k` (with the empty
case represented by one pattern). Bell-number bounds can be tighter. There
is no finite actual-name universe: the finite objects are equality patterns.
Case-split public equality patterns before eliminating hidden ports, retaining
the equality/disequality guard for each public case. This computes a finite
formula over the original public ports and unchanged `G` leaves. It does not
construct a closed substitution for unknown Record fields or discard `Phi`.

If every remaining `G` is decidable at its retained input, this gives
pointwise public membership decision. If none remains and the only domains
are these atom sorts, it gives complete satisfiability decision. If `G`
contains arbitrary structural, descriptor, history or world quantification,
the result is an effective **exact residual**, with those obligations still
present. A successful name elimination cannot decide those obligations.
Recursive operators are not unfolded by this construction. Eliminating a
coordinate through an operator that can read it requires a separate pointwise
operator-conjugacy/elimination law with its designated fixed-point meaning;
CI_USE's existing operator law may transport a supplied correspondence, but
does not prove this elimination law. Such an operator is outside the finite
formula theorem until that premise is discharged.

Independent admission is handled in its actual formula position. For an
atom challenge, `forall c. D(c;X,xi) => M(c;X,xi)` uses the same representative
classes for both predicates, after their independent exact observer expansions
are justified. For a non-atom world, `forall w` stays unchanged, and elimination
inside its body remains pointwise uniform over every `w`. A predicate reading
unbounded world structure through a hidden atom has no such expansion here.
No admission is inferred from nonempty observations.

## 3. Correlation, uniformity, and principality limits

One shared hidden atom yields the exact projection

```text
exists a. (p=a and q=a)   iff   p=q.
```

Independent projection of the two clauses instead gives every pair. Likewise
`exists a. forall c. a=c` is false on an infinite atom domain, while
`forall c. exists a. a=c` is true. A per-challenge hidden choice would change
the former into the latter. The orbit construction keeps the binder order
and whole tuple, so neither error is possible.

Let `E` be the constructed residual. The theorem proves exact original-fiber
projection and witness factorization through `E`, relative to the specified
observer class. Repeated uses take a whole fresh copy with one map per use,
retaining all original import and client correlations. The finite pattern
residual is a complete interface for those listed observations; CI_ALPHA can
compare its full finite graph, and CI_USE applies only with its actual
primitive/query covariance premises. This is relation-level principality for
the projected fragment, not all-valid-view ordinary Function principality.

In particular, retaining an original `Direct` leaf with unchanged operands
preserves its truth and evidence; this construction cannot establish a new
`Direct(B_common,R_V)` leaf. It neither fills the independent Integer/Top
decorated membership premise nor provides the missing actual-root
result-widening resolver case. `ALL_VIEW` and `PRINCIPAL` stay open.

## 4. A concrete obstruction to a source-size/FMP candidate bound

Work in the pure mandatory Record grammar already admitted by FMP. Put
`R(t)=Record{f:t}` and `C_n=R^n(Record{})`. Every `C_n <= Record{}`. The
unconstrained pure package `X <= Record{}` has a tiny FMP witness and finite
syntax, while its fiber contains all these chains. Their equality cannot
be decided from nominal incidence: they have no names at all and have
different constructor depths.

Extend the mathematical input by one primitive, independently defined as
follows. For an encoded deterministic machine `e`, let

```text
H(e,X) iff X is exactly C_n for some n,
            and machine e halts within n transition steps on empty input.
```

Checking `H` on any supplied finite regular graph terminates. Recognize the
single-field acyclic chain (reject cycles and other shapes), compute `n`, and
simulate exactly `n` machine transitions. It has no atom observations, so its
nominal support is empty; it is invariant under every atom renaming. It is
given by one finite algorithm. The independent joint relation is

```text
X <= Record{} and H(e,X).
```

It is satisfiable iff `e` halts. Hence no computable complete candidate bound,
candidate enumeration with terminating complete checks, or complete joint
decision algorithm exists for this extension. Otherwise testing the finitely
many candidates would decide halting. This remains true when `e` is supplied
as a finite fixed input, with its encoding size counted in the input size.
The obstruction is not an artificial omission of a large numeral from `N`.

More concretely, if a computable graph-size bound `b(e)` were complete, a
finite graph representing `C_n` would have at least `n+1` distinct states:
its suffixes have different remaining depths and cannot be bisimilar.
Simulating `e` for `b(e)` steps would therefore decide whether any satisfying
bounded graph exists, and by completeness decide halting. Consequently, for
every proposed computable complete bound some halting machine has no witness
within it. This argument does not rely on a particular large busy-beaver
value or an unbounded test run. Pure FMP still applies to the pure clause and
says nothing false: its small replacement witness can fail `H`.

This refutes the implication from finite syntax, pointwise decidable
primitives, empty nominal support and pure FMP to complete joint solving.
It does **not** prove that actual Yulang has the primitive `H`, nor that any
actual independently interpreted admission/descriptor clause realizes this
reduction. No such source realization has been established.

There is a separate presentation distinction. The displayed joint relation
already is a finite exact residual if `H` is an allowed independently
interpreted primitive. Thus the example does not refute finite residual
syntax. It refutes inference of an effective decision/reflection certificate
from that syntax. A finite equality-incidence quotient cannot represent the
whole chain distinction: all chains have the same empty atom incidence,
while `H` distinguishes them. A richer finite recursively interpreted
residual may express `H`; its existence does not make satisfiability decidable.
These three claims must not be conflated.

The actual minimum required bridge is therefore either an exact effective
elimination/decision law for every active primitive at its original operands,
or a proved preservation-and-reflection law through the particular structural
regularization/candidate quotient. Merely proving nominal equivariance, or
inheriting the pure `8^N` bound, supplies neither law. The positive identity-only
construction above supplies such a law for its exact observer class.

## 5. Checks, resources, dependencies, and commit packet

This section preserves the producer's pre-review execution and handoff record.
Independent review subsequently closed at the exact scope linked in the header.

The standard-library checker compares direct finite-domain quantifier
evaluation with equality-orbit evaluation over all 8 alternations of three
binders, both public equality patterns, and every signed equality literal or
binary conjunction/disjunction of two such literals over five ports. The
reference uses actual domain values; the candidate uses existing equality
classes plus one fresh representative at each original binder. Both share
the explicitly supplied equality semantics. It also checks the uniformity
and marginal mutations, sibling binder-port distinction, and 33 concrete
finite-depth-sample omissions. It does not execute a halting oracle or model
Yulang primitive semantics. The infinite-domain claims are proved above;
finite comparisons are consistency evidence for the algorithm.

Verification budget: one single-process finite checker, at most 60 seconds
and 1 GiB address space; zero Cargo/build/test processes, children, Git
operations, compiler/shared-record edits, question bundles or authority changes.
The checker produces only stdout and dependency hashes; no shared cache or
generated output is written. A unique optional capture path is
`/tmp/successor_effective_projection_round2_ad514061.log`.

Exact command and observed check results are appended below after the sole run.
The full baseline is supplied by the primary. Git access is excluded by this
packet, so current dependency hashes are recorded without claiming independent
baseline-byte equality. Primary must compare them to the pinned revision
before integration. Navigation reads with truncated output were followed by
bounded rereads of the decisive theorem/rule sections.

Omissions: actual source rule correspondence and Generalize eligibility;
exhaustive primitive/descriptor/world/admission interpretation; all-world
source adequacy; full structural/effect projection; ordinary actual-export
Direct completeness; production conformance; parser/Oracle/VM execution;
independent review; numerical performance claims. No supported-input boundary,
production representation, recursion policy, or semantic restriction is chosen.

Commit packet:

- Exact paths: this note and `tools/research_successor_effective_projection_round2.py`.
- Baseline: `ad514061de2792c374a4b5c224dff7f4772906e8`.
- Claim/review status: frozen unreviewed restricted constructions and a
  metatheorem obstruction; research-only, no unrestricted gate closure.
- Proposed message: `research: construct scoped identity projection and isolate FMP reflection cut`.
- Shared-record deltas deferred: link the two restricted sublemmas under
  `CTX_FINITE`/`PROJECTION`; keep the actual source-operation/observer audit,
  `JOINT_DEC`, `ALL_VIEW`, and `PRINCIPAL` open. Record that finite syntax and
  even decidable candidate membership are insufficient for a complete joint
  bound, without labeling actual Yulang undecidable.

Writes stop at submission; review repair requires an explicit returned lease.

### Executed verification and dependency snapshot

Executed once:

```text
timeout 60s python3 -B -c 'import pathlib, resource, runpy; resource.setrlimit(resource.RLIMIT_AS, (1073741824, 1073741824)); p = pathlib.Path("tools/research_successor_effective_projection_round2.py"); compile(p.read_text(), str(p), "exec"); runpy.run_path(str(p), run_name="__main__")'
```

Result: PASS, 1,830 matrices, 8 original binder alternations, 2 public equality
patterns, and 29,280 candidate/reference comparisons on a six-atom domain.
Three named shortcut mutations were discriminated; 33 finite-depth samples
were each shown incomplete for their specified successor-depth predicate.
The process completed before timeout with exit 0. The first tool call yielded
after about one second; total process wall time, CPU and RSS were not measured.
The explicit 60-second and 1-GiB limits were enforced. Zero seeds or uncovered
shards apply; this finite equality envelope is exhaustive as described.
Compilation occurred in the same process without bytecode/cache output.
An `awk` inspection of both exact leased paths reported no trailing whitespace
and exited 0; no Git-based diff or repository-wide check was run.

Current dependency SHA-256 values from that same process:

```text
ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd rules/research-lab.md
9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29 rules/design-authority.md
e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e rules/git-concurrency.md
18bfa4e5bb461616ca17a0c9a1492f75ff7fca2f6231a13b3d68e0a3335136dc notes/theory/successor-proof-obligations.md
a64ffaddf0f15b73e59b0eacb02d1e4c30331340ff55ed869e6112aa201633b4 notes/design/2026-10-03-scoped-constraint-solving.md
dba409842c631d81dfeedbeafc7ca34dcd9edeaaa0a80f49bba0cb3f6916f8cf notes/design/2026-10-03-source-context-finite-closure.md
02e6e04d1a4eea405442587206e34c653b45405677d653e6bfec37568fee4f43 notes/design/2026-10-03-open-residual-factorization.md
29f7b04196d577f77ff9040dab19a1d83172ba323ff9bebd81ea5177ff6e926e notes/design/2026-10-04-structural-fmp-fence-completion.md
37bc762c22d32258355e835a29f598a8b50aa7307a88c01454ef63849c11e133 notes/progress/2026-10-05-pure-structural-effective-decision-corollary.md
887bc7c0743d2f34608b46ccb8e5ee9b58ea4a39995b93a5aaced764295bae80 notes/design/2026-10-04-certified-callback-and-constrained-use.md
b34c5b3644637bc1340f5636e0b6dc3fcc42c39de5d9cc73bcb48b84293e417e notes/progress/2026-10-07-successor-global-synthesis.md
e34a568946f5c1946c01828aae34e890747477ee8c272775408438acd95aa43f notes/progress/2026-10-07-successor-recursive-synthesis.md
9dbf397ec1ea5f9ce5ea8ed732e4c5c5c6bfdb5c9719010d5fc8b002a8f98487 notes/progress/2026-10-07-principal-whole-relation-factorization-attempt.md
b259389ec2312d101a3eb1be53dc343f3918fd863abed263b03d8cb9107c1939 notes/progress/2026-10-08-principal-actual-export-rule-attempt.md
c61a87796c3809fd10e2c59c0a40a30af03e795aead2585b5fcbfc13b278ca3d notes/progress/2026-10-08-principal-vincl-actual-root-bridge-attempt.md
1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186 notes/design/2026-10-05-source-contracts-and-common-allowance.md
```

Dependency changes relative to baseline: not independently established in this
Git-free packet; primary comparison remains required. No unfinished worker
artifact was used. Shared task/index records were navigation, not proof inputs.
