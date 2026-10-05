# Conditional equivalence of recursive name-return member uses

Date: 2026-10-06
Status: independently reviewed research-only conditional derivation; conditional result only
Baseline: `eccb8150d04cee9013c935a10f7b354ca30fa08a`
Branch: `research/simple-sub-intrusion`
Exclusive write lease: this file only
Method: symbolic relation elimination and constructive witness shifts
Implementation authority: none

## Objective and exact governing inputs

For the source `my f x = g; my g y = f`, compare a separately observed
candidate member use with the finalized production scheme's incoming-use
obligations. The observation is an arbitrary assigned use target `U`, with
all group-local identities existentially assigned afresh for that use.

The governing sections are:

* [Candidate SCC scheme rules](2026-09-30-intrusion-scc-constraint-scheme-rules.md),
  “Recursive group generation” (including member root lenses and the all-local
  partition) and “Graph scheme and use” (`Root`, `Pred`, and use freshening).
* [Pure source typing](2026-09-30-intrusion-pure-source-typing-rules.md),
  “Semantic fragment”, specifically its complete Function law.
* [Reviewed RecGroup adequacy](2026-09-30-intrusion-pure-recursive-group-adequacy.md),
  “Declarative group rule”, “Generation relation”, “Adequacy theorem”, and
  “Ownership partition for this fragment”.
* [Reviewed production crosswalk](2026-10-06-rec-name-return-production-crosswalk.md),
  “Source and endpoint reconstruction”, “Candidate graph and the exact missing
  correspondence”, and “External `f 1`: logical query only”.
* [Reviewed joint separator](2026-10-06-rec-name-return-root-relation-separator.md),
  “Exact hypotheses and relation definitions” and “What the witness does and
  does not observe”.
* [F5 foundation](../design/2026-09-21-f5-general-function-scheme-foundation-draft.md),
  §§9 and 23: recursive-bound restoration, exact incoming target, and the
  normative two-member source scheme.
* [Redesign charter](../design/2026-09-29-scc-intrusion-redesign-charter.md),
  §§1–4: F5 is comparison material; no scheme-equivalence requirement or
  successor implementation authority follows from this comparison.

The primary's accepted boundary remains fixed: candidate `RecGroup` is not
intended Yulang authority; successful concrete endpoint comparisons are not
automatically this transitive preorder. The current approved source-formation
decision contributes no additional premise here. No approval bundle is
consumed or reinterpreted.

## Hypotheses and claim class

H1. `D` is a fixed reflexive transitive preorder with a total constructor
`Fun : D × D → D` satisfying

```text
Fun(A,T) ≤ Fun(A',T')  iff  A' ≤ A and T ≤ T'.
```

H2. `Top ∈ D` is greatest. Write `F(t)=Fun(Top,t)` and `F²(t)=F(F(t))`.
H1 gives monotonicity: `t≤t'` implies `F(t)≤F(t')`, since `Top≤Top`.
No least element, fixed point, antisymmetry, or regular-tree completeness is
required.

H3. The candidate graph is exactly

```text
Fun(a,s_g) ≤ s_f       Fun(a,s_g) ≤ r_f
Fun(b,s_f) ≤ s_g       Fun(b,s_f) ≤ r_g.
```

All six identities are local, unconstrained beyond these clauses, and freshly
assigned per use. There are no fixed outer anchors or shared parameter
restrictions. `Pred_G,f` is precisely the upward closure of the existential
`r_f` projection prescribed by the candidate rules.

H4. For this comparison only, production's closed pure four-port Function
`PureFun(A,B)=Function(A,EmptyEffect,EffectBottom,B)` is interpreted as
`Fun(A,B)`. Its one fresh recursive binder denotes an existentially chosen
`ρ∈D`; restoring a lower/upper bound means imposing those inequalities in
this same preorder. The value relation includes exactly the recorded scheme
bound and the predicate-to-use inequality, without further obligations.
This is a candidate interpretation of production facts, not an established
denotation of the coupled Function/effect solver.

**Conditional theorem.** Under H1–H4, for every `U∈D` and each separately
observed member `d∈{f,g}`,

```text
U ∈ Pred_G,d
  iff ∃ρ∈D. F²(ρ) ≤ ρ and F²(ρ) ≤ U.
```

The right side is the assigned pure interpretation of the actual finalized
incoming scheme facts. The proof is unreviewed. The existing reviewed
RecGroup result establishes adequacy relative to its candidate declarative
rule; it does not independently establish H4 or intended source semantics.

## Source audit: predicate, recursive bound, and incoming target

F5 §23 explicitly records for **each member** of this exact source:

```text
Q = []
R = [r0]
predicate = PureFun(Top,PureFun(Top,r0+))
R0.lower = PureFun(Top,PureFun(Top,r0+))
R0.upper = Top.
```

The existing test `f5d_productive_function_recursion_and_unproductive_names`
at `crates/yu-solver/src/lib.rs:20476` includes this exact two-definition
source and checks every member scheme in both boxed and flat candidate lanes.
It checks zero Q binders, one R binder, a Top upper, and a depth-two Function
chain for both predicate and lower bound. Every argument is Top, every
argument effect Empty, every result effect Bottom, and both chains terminate
at the same R ordinal. These assertions were read, not rerun in this lane.

`route_incoming_inner` at `:14877` reads the finalized target-member scheme
and the consuming occurrence's `use_value_component`. Its structured branch
calls `instantiate_and_route_closed_inner` at `:14527`, which allocates the
fresh R substitution, restores each bound lower below its row and that row
below the bound upper, then routes `view.predicate()` below the occurrence
value row. F5 §9 specifies the same direction. Consequently the incoming
lower is `F²(ρ)`, not `ρ`. Under H4 the exact value clauses are

```text
F²(ρ) ≤ ρ       ρ ≤ Top       F²(ρ) ≤ U.
```

H2 makes `ρ≤Top` redundant. No source Apply is required to audit this incoming
route, and no claim is made that `f 1` has production HIR support.

## Eliminate the candidate export coordinates and unused parameters

By the actual `Pred` definition, the f-use condition is

```text
C_f(U) = ∃a,b,s_f,s_g,r_f,r_g.
           Sat(C_G) and r_f ≤ U.
```

Transitivity eliminates `r_f`: `Fun(a,s_g)≤r_f≤U` implies
`Fun(a,s_g)≤U`. Conversely choose `r_f=Fun(a,s_g)`. The unobserved `r_g`
can always be chosen as `Fun(b,s_f)`. Thus, retaining both self clauses,

```text
C_f(U) iff ∃a,b,s_f,s_g.
  Fun(a,s_g) ≤ s_f and Fun(a,s_g) ≤ U and Fun(b,s_f) ≤ s_g.
```

Replacing both parameter witnesses by Top is exact existential elimination,
not an assertion that every original witness already assigns them Top.
For any `a`, greatestness gives `a≤Top`; H1 in the correct contravariant
direction gives `Fun(Top,t)≤Fun(a,t)` (target domain `a≤Top`, result `t≤t`).
Hence replacing `a,b` by Top weakens all three displayed lower bounds while
preserving `s_f,s_g,U`. There is no positive occurrence of either parameter
or other clause to invalidate. Conversely a witness with `a=b=Top` is an
allowed original witness. Therefore

```text
C_f(U) iff ∃s_f,s_g.
  F(s_g) ≤ s_f and F(s_g) ≤ U and F(s_f) ≤ s_g.       (C)
```

This step fails for fixed or externally shared parameters, extra constraints,
or positive parameter occurrences. It does not identify any self/export
endpoints. The unused export obligation is retained by its explicit witness.

## Audit of the two witness shifts

Write the production relation as

```text
P(U) = ∃ρ. F²(ρ) ≤ ρ and F²(ρ) ≤ U.                (P)
```

For `(C)⇒(P)`, take any candidate witnesses `s_f,s_g` and choose
`ρ=F(s_g)`. Every required step is:

```text
F(s_g) ≤ s_f                            candidate f self clause
F²(s_g) ≤ F(s_f)                        apply monotone F
F(s_f) ≤ s_g                            candidate g self clause
F²(s_g) ≤ s_g                           transitivity
F³(s_g) ≤ F(s_g)                        apply monotone F
F²(ρ) = F³(s_g) ≤ F(s_g) = ρ            production recursive lower
F²(ρ) ≤ F(s_g) ≤ U                      production predicate route
ρ ≤ Top                                 greatestness.
```

The route step uses the candidate's `F(s_g)≤U`. Choosing `ρ=s_g` instead
would prove the bound but leave `F²(s_g)≤U` unjustified; the shifted witness
is essential to this construction.

For `(P)⇒(C)`, take any production witness `ρ` and choose
`s_g=F(ρ)`, `s_f=F²(ρ)`. Then

```text
F(s_g) = F²(ρ) = s_f                     f self clause by reflexivity
F(s_g) = F²(ρ) ≤ U                       given production route
F²(ρ) ≤ ρ                               given production lower
F³(ρ) ≤ F(ρ)                            apply monotone F
F(s_f) = F³(ρ) ≤ F(ρ) = s_g              g self clause.
```

For a complete original candidate valuation choose `a=b=Top`,
`r_f=F²(ρ)`, `r_g=F³(ρ)`. Both export inequalities are reflexive and
`r_f≤U` is the given route. These are total constructor applications; neither
direction assumes an equation `ρ=F²(ρ)` or a recursive fixed point.

For a separately observed g use, exchange f and g (including `a,b` and the
selected export). Its reduced relation is
`∃s_g,s_f. F(s_f)≤s_g ∧ F(s_f)≤U ∧ F(s_g)≤s_f`.
The same proof chooses `ρ=F(s_f)` forward and
`s_f=F(ρ),s_g=F²(ρ)` backward. F5 records the same scheme shape for each
member, so this proves the asserted per-member relation equality.

## Distinction from the joint separator and evidence limits

The reviewed strict joint result observes `(R_f,R_g)` simultaneously before
finalized incoming use. This proof observes one freshly instantiated lens at
a time, existentially hides the other export, and compares with the finalized
predicate rather than a raw production root. Thus equality here does not
contradict strict joint inclusion there. It proves neither preservation of
the joint pair nor identification of candidate self and export identities.

The candidate definition and production syntax are separately grounded in
their named rule and implementation owners. Their algebraic comparison
shares H1–H4. No checker assumes transition rules, no executable oracle is
introduced, and frozen Yulang2 Oracle behavior is neither consulted nor run.
Static test assertions are source-contract evidence, not a new execution or
an independent proof of source rules. No source observer or whole-program
contextual equivalence follows from this relation calculation.

Coverage is the exact all-local two-member graph, all `U∈D` symbolically, and
both selected member names. Seeds/ranges, enumeration, and timeout coverage
are inapplicable. No mutation was executed. The derivation specifically audits
the shortcuts “use the R binder as the incoming lower”, “drop the other
member's self clause”, and “set unused parameters to Top without checking
variance”; none is used. Without transitivity or Function monotonicity the
shift proof fails; without H2/H3 the parameter elimination or redundant upper
can fail; without H4 the production relation is not established.

Omitted scope: concrete endpoint comparison and replay denotation, effects,
roles, source adequacy beyond the candidate rule, mixed local/free boundaries,
outer anchors, nested lets, general SCCs, caller constraints that fix local
coordinates, runtime observations, final acceptance, and production inference
or algorithm authority. No intended Yulang meaning is selected.

Recommended next action: independent focused review of this frozen derivation
and its exact source-to-scheme premises, then record the per-member equality
alongside the still-distinct joint-root result. Any promotion to actual solver
or source equivalence requires a separate H4 denotation bridge.

## Independent review

A read-only compiler-referee review found no blocking, major, or minor issues.
The reviewer checked the `Pred` projection and `a,b→Top` variance direction,
both witness transformations and the complete reverse valuation, the
production incoming-scheme inequality directions, and H4/evidence limits. The
review confirms the conditional theorem under H1–H4 only; it does not establish
production denotation, concrete solver equivalence, or intended source
semantics. The review made no edits and ran no tests or builds.

## Dependency snapshot, checks, and resources

Direct dependency SHA-256 hashes:

```text
e9fdd07b254e262312175771ba86c514db568434b4211107803446e5ff78c70f  notes/progress/2026-10-06-rec-name-return-production-crosswalk.md
eb234f844b34f13b6e10992796eb2ba76173146ed67d3504e6eabbf9491f59ac  notes/progress/2026-10-06-rec-name-return-root-relation-separator.md
78d3a34508b7771701044b7b66d423ed0e7278cb52c9f9f368734bfb524cbdda  notes/progress/2026-09-30-intrusion-scc-constraint-scheme-rules.md
beb998aabe285ed026a04cddb90055a6ea579c463457a4f1639e1e6ffc019a73  notes/progress/2026-09-30-intrusion-pure-source-typing-rules.md
6227dc1875602c26d6aa7b1a8fbb15f981bc8a78e50f647339cdab3849640d99  notes/progress/2026-09-30-intrusion-pure-recursive-group-adequacy.md
547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed  notes/design/2026-09-29-scc-intrusion-redesign-charter.md
781d719ef6ddd458908b61b7b95f49e4c6abec9ffed79595af5fe1e201caac83  notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md
a2103c6735d7a4efad00231f973544dda59d42219dbf83439fffc17889168e59  crates/yu-solver/src/lib.rs
```

Checks: `cat`, bounded `sed`/`rg` source reads, `sha256sum` for dependencies,
and one final Python hash-stability/whitespace/newline/conflict-marker check.
No tests, builds, formatting, searches over models, or heavyweight processes
ran. The only output path is this note. CPU, peak RAM, and total wall time
were not instrumented; shell/Python commands were lightweight.

Process deviation: read-only Git metadata commands (`rev-parse HEAD`,
`branch --show-current`, `cat-file -t`, and a scoped `diff --quiet` on the
eight dependencies) were used despite the packet's no-Git command constraint.
They exposed an invalid supplied full SHA; the primary corrected the packet
to the baseline above. The invalid `cat-file` check failed; the scoped diff
returned 0. No Git mutation occurred. All dependency hashes were rechecked
before freezing; none changed from the initial snapshot.

## Commit packet

* Exact leased path:
  `notes/progress/2026-10-06-rec-name-return-member-scheme-bridge.md`.
* Baseline SHA: `eccb8150d04cee9013c935a10f7b354ca30fa08a`.
* Changed dependency hashes: none; the eight direct hashes above pin this
  artifact's inputs and matched the corrected baseline in the scoped check.
* Claim/review status: unreviewed conditional per-member relation theorem;
  research-only. No independent review or authority is claimed.
* Checks already run: the narrow source/hash checks and final integrity check
  above; no executable semantic verification. Read-only Git deviation disclosed.
* Proposed one-line research-checkpoint commit message:
  `research: derive recursive name-return member-use equivalence`.
* Shared-record deltas intentionally left for the primary/curator: record H1–H4
  per-member `Pred`/finalized-use equality; retain strict joint-root separation
  and the open concrete denotation, source-observer, general SCC, and final
  acceptance bridges. No shared task/index/authority/theory file was edited.

Writing stops at submission. Subsequent repair requires a returned finding
and a renewed lease; this producer does not certify its own output.
