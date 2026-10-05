# Conditional joint-root separation for recursive name returns

Date: 2026-10-06
Status: research-only reviewed conditional derivation; no implementation authority
Baseline: `e8956d07edda3bbacb24ad98310c8dda1866015b`
Assigned branch: `research/simple-sub-intrusion`
Exclusive write lease: this file only
Method: hand derivation and counterassignment minimization; no executable model

## Objective and governing sections

Compare the joint exported-root relations of the candidate and production's
syntactic pure projection for `my f x = g; my g y = f`, under the assigned
crosswalk `s_g=U_fg`, `s_f=U_gf`. The question concerns existential projection
of the complete two-member graph onto `(R_f,R_g)`.

Exact governing inputs:

* [Production crosswalk](2026-10-06-rec-name-return-production-crosswalk.md):
  "Source and endpoint reconstruction", "Candidate graph and the exact
  missing correspondence", and "Compact conditional separator".
* [Candidate SCC rules](2026-09-30-intrusion-scc-constraint-scheme-rules.md):
  "Recursive group generation" and "Graph scheme and use".
* [Pure source typing rules](2026-09-30-intrusion-pure-source-typing-rules.md):
  "Semantic fragment" and "Correspondence theorem for this fragment".
* [Recursive-group adequacy](2026-09-30-intrusion-pure-recursive-group-adequacy.md):
  "Declarative group rule", "Generation relation", and "Adequacy theorem".
* [Redesign charter](../design/2026-09-29-scc-intrusion-redesign-charter.md)
  §§1–4: F5 is comparison material; soundness/principality precede final
  Oracle acceptance compatibility; implementation requires a separate gate.

The primary's accepted decisions remain premises: candidate `RecGroup` is
not intended Yulang authority; individually successful concrete comparisons
are not automatically the fixed transitive preorder. Meaningful source
constraints remain retained. No language meaning is selected by this note.

## Exact hypotheses and relation definitions

H1. `D` is a fixed reflexive transitive preorder with a Function constructor
satisfying the complete law

```text
Fun(A,T) ≤ Fun(A',T')  iff  A' ≤ A and T ≤ T'.
```

H2. The production relation being compared consists exactly of the four
assigned pure value clauses, with freely assignable body endpoints:

```text
P(a,b,R_f,R_g,U_fg,U_gf):
  Fun(a,U_fg) ≤ R_f
  R_g ≤ U_fg
  Fun(b,U_gf) ≤ R_g
  R_f ≤ U_gf.
```

The candidate relation consists exactly of its four clauses:

```text
C(a,b,R_f,R_g,s_f,s_g):
  Fun(a,s_g) ≤ s_f
  Fun(a,s_g) ≤ R_f
  Fun(b,s_f) ≤ s_g
  Fun(b,s_f) ≤ R_g.
```

This is the reviewed crosswalk's H1–H2 interpretation, not a proved denotation
of production's polarized Function/effect facts. A larger actual production
relation, additional bounds, or a different denotation is outside H2.

For fixed parameters define

```text
P_ab = { (R_f,R_g) | ∃U_fg,U_gf. P(a,b,R_f,R_g,U_fg,U_gf) }
C_ab = { (R_f,R_g) | ∃s_f,s_g. C(a,b,R_f,R_g,s_f,s_g) }.
```

H3, needed only for strictness. `D` has least `Bottom`, greatest `Top`, and a
value `Z` with `Z=Fun(Bottom,Z)` and `Top ≰ Z`. The equality is an additional
carrier premise, such as a guarded regular Function value, not a source rule
equating recursive endpoints. H1 alone does not require this value or strict
extrema: the singleton carrier satisfies H1 and cannot support strictness.

## Conditional inclusion and exact production elimination

Under H1–H2, for every fixed `a,b`,

```text
P_ab = { (R_f,R_g) | Fun(a,R_g) ≤ R_f and Fun(b,R_f) ≤ R_g }
P_ab ⊆ C_ab.
```

For elimination forwards, `R_g≤U_fg` and Function result covariance imply
`Fun(a,R_g)≤Fun(a,U_fg)≤R_f`. Likewise,
`Fun(b,R_f)≤Fun(b,U_gf)≤R_g`. Backwards choose `U_fg=R_g`, `U_gf=R_f`; the
two routing edges are reflexive and the other clauses are the displayed
diagonal obligations. Thus existential elimination is exact.

For inclusion using the assigned crosswalk directly, set `s_g=U_fg`,
`s_f=U_gf`. The two candidate root clauses are production's Function clauses.
The candidate self clauses follow from

```text
Fun(a,U_fg) ≤ R_f ≤ U_gf
Fun(b,U_gf) ≤ R_g ≤ U_fg.
```

Production therefore entails the candidate clauses plus `R_f≤s_f` and
`R_g≤s_g`. Conversely those added edges and the candidate root clauses give
all four production clauses. Endpoint renaming alone does not remove these
extra obligations. A second inclusion proof chooses `s_f=R_f,s_g=R_g` after
elimination. Both proofs use the same H1–H2; neither is independent evidence
for their source interpretation.

## Reduced counterassignment and all four variance checks

Under H1–H3 fix the parameter assignment and roots as follows:

```text
a = b = Bottom
s_f = s_g = Z
R_f = Top
R_g = Z.
```

All four candidate obligations hold:

| Clause | Assigned inequality | Reason |
|---|---|---|
| f self | `Fun(Bottom,Z) ≤ Z` | `Z≤Z`; unfold the assumed equality |
| f export | `Fun(Bottom,Z) ≤ Top` | `Z≤Top`; Top is greatest |
| g self | `Fun(Bottom,Z) ≤ Z` | `Z≤Z`; unfold the assumed equality |
| g export | `Fun(Bottom,Z) ≤ Z` | `Z≤Z`; unfold the assumed equality |

The self/export comparisons against `Z=Fun(Bottom,Z)` use Function domain
contravariance in the correct direction: target domain `Bottom≤Bottom` and
source result `Z≤Z`. No reversed domain inequality is being assumed.

Production cannot realize the same pair. Exact elimination would require

```text
Fun(Bottom,Top) ≤ Z = Fun(Bottom,Z).
```

By H1 this requires both `Bottom≤Bottom` and `Top≤Z`. The latter contradicts
H3. The other diagonal production inequality,
`Fun(Bottom,Z)≤Top`, holds; it cannot repair the failed g obligation.

The failure also follows without eliminating any body endpoint. Production
would give `Top=R_f≤U_gf` and `Fun(Bottom,U_gf)≤Z=Fun(Bottom,Z)`. The Function
law yields `U_gf≤Z`; transitivity then yields `Top≤Z`. Thus no alternate body
assignment can rescue the pair.

Consequently `P_Bottom,Bottom ⊊ C_Bottom,Bottom`. Even existentially freeing
the parameters cannot admit this root pair into production: for every `b`,
`Fun(b,Top)≤Fun(Bottom,Z)` still requires `Top≤Z`. This establishes strict
joint-root inclusion for the unconditioned parameter projections as well,
under the same H1–H3.

This reduces the crosswalk's witness by replacing `Int` with `Bottom` and
`Fun(Int,Top)` with `Top`. It uses one regular back-reference and no integer
atom or extra constructed export value. No exhaustive global minimality
claim is made; this is a direct algebraic reduction in the assigned source
pattern, not a search over smaller source graphs.

## What the witness does and does not observe

Each witness coordinate is separately realizable by production at the same
fixed parameters. The pair `(Top,Top)` is in `P_Bottom,Bottom` by choosing
both body endpoints Top. The pair `(Z,Z)` is in `P_Bottom,Bottom` by choosing
both body endpoints Z. Hence neither `R_f=Top` nor `R_g=Z` by itself witnesses
a marginal difference. Their simultaneous pairing is the obstruction.

This does not prove equality of the complete individual marginal relations.
It does not compare independent incoming-use instances, finalized schemes,
call acceptance, whole programs, runtime behavior, or Oracle acceptance. In
particular, existentially projected member views need not observe this joint
root pair. A source observer capable of fixing or relating both exports has
not been supplied. No operational or intended-source correctness consequence
is drawn from a separation of these conditional graph relations.

## Independence, coverage, and failure conditions

This artifact is a fresh hand derivation of the assigned equations and a
smaller valuation than the supplied crosswalk. It is not an independent
review of that crosswalk, whose premises and separator were supplied as
inputs, nor an independent review of this artifact. Production endpoint
ownership is taken from the reviewed crosswalk and was not re-audited here.

The comparison shares the transitive preorder, full structural Function law,
and stipulated pure projection on both sides. No checker or transition model
was executed; no claimed evidence independently derives these source rules.
The frozen Oracle was neither consulted nor run. Coverage is the exact
two-member name-return graph, a fixed `a=b=Bottom` assignment, and the
symbolic all-`b` production impossibility. Seeds/ranges are not applicable;
there was no enumeration. No executable mutation ran. The targeted shortcut
is forgetting the two extra root-to-body/self bounds in the crosswalk.

Strictness fails as a conclusion if H3 is unavailable. Inclusion/elimination
may fail without H1 transitivity/covariance, or if H2's projection is replaced
by another meaning. Omitted cases include effects, concrete solver comparison
nontransitivity, replay, generalization, member-specific boundaries, nested
lets, actual Function use, source adequacy, and final acceptance. No broad or
heavy process ran, and no tests, builds, formatters, or Git operations ran.

Recommended next action: independently review this conditional joint-root
derivation, then determine through the primary whether the intended source
observer uses joint exports or only separately instantiated member lenses.

## Independent review

`compiler_referee` reviewed the H1–H3 definitions, exact production
elimination/inclusion, strict witness including its parameter-unfixed form, and
the marginal limitations. The reviewer found no blocking, major, or minor
findings. This certifies only the conditional relation result; it does not
establish production denotation, a source observer, finalized schemes, or
Oracle acceptance.

## Dependency snapshot and checks

The primary supplied the full pinned baseline SHA above. No Git command was
used by this worker. Four candidate/charter hashes below match the recorded
dependency hashes in the supplied reviewed crosswalk. The crosswalk's own
hash is a live snapshot; its equality to the baseline was not independently
checked by this worker. All five hashes were rechecked for stability before
freezing this note. Unrelated shared task/theory edits were not consumed.

```text
e9fdd07b254e262312175771ba86c514db568434b4211107803446e5ff78c70f  notes/progress/2026-10-06-rec-name-return-production-crosswalk.md
78d3a34508b7771701044b7b66d423ed0e7278cb52c9f9f368734bfb524cbdda  notes/progress/2026-09-30-intrusion-scc-constraint-scheme-rules.md
beb998aabe285ed026a04cddb90055a6ea579c463457a4f1639e1e6ffc019a73  notes/progress/2026-09-30-intrusion-pure-source-typing-rules.md
6227dc1875602c26d6aa7b1a8fbb15f981bc8a78e50f647339cdab3849640d99  notes/progress/2026-09-30-intrusion-pure-recursive-group-adequacy.md
547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed  notes/design/2026-09-29-scc-intrusion-redesign-charter.md
```

Checks: narrow `cat`/`sed`/`rg` reads; `sha256sum` of the five dependencies;
one Python metadata check of unchanged dependency hashes, trailing whitespace,
final newline, and conflict markers in this note. These are artifact integrity
checks, not executable semantic validation. Process/RAM/wall-time totals were
not instrumented; only lightweight reads and one metadata check were used.
No search envelope, seeds, timeout, partial enumeration, or extra output path
exists to report.

## Commit packet

* Exact leased path:
  `notes/progress/2026-10-06-rec-name-return-root-relation-separator.md`.
* Baseline SHA: `e8956d07edda3bbacb24ad98310c8dda1866015b`.
* Changed dependency hashes: none observed between the initial and final live
  snapshots; four match recorded crosswalk hashes. Crosswalk-to-baseline
  equality remains a primary integration check.
* Claim/review status: reviewed conditional theorem and reduced witness;
  research-only; no intended semantics, Oracle, or production closure.
* Checks already run: narrow input reads, five dependency hashes and final
  stability recheck, note whitespace/newline/conflict-marker inspection.
* Proposed one-line commit message:
  `research: separate recursive name-return joint root relations`.
* Shared-record deltas intentionally left for the primary/curator: record the
  H1–H3 conditional strict joint inclusion and reduced `(Top,Z)` witness;
  preserve the open source observer, marginal-equivalence, finalized-scheme,
  concrete denotation, and final-acceptance bridges. No shared file was edited.

This artifact is frozen at submission. Its SHA-256 is supplied in the return
packet; subsequent repairs require a returned finding and renewed lease.
