# Direct structural FMP attack: finite feedback and fixed-package quantifiers

Date: 2026-10-04
Branch: `research/simple-sub-intrusion`
Base inspected: `be138584741a007e084aabe1c0e66641dac497b2`
Integration base: `8ddd2df276d5f6179a80c8e8610ac349e413d54f`
Status: reviewed historical classification C; subsequent finite-fence proof closes FMP and BR
Implementation authority: none

**Later completion:** [the finite-fence FMP proof](2026-10-04-structural-fmp-proof.md)
closes the fixed-package theorem and (BR), with two independent clean
reviews. The remaining-action statements in this record are historical.
The finite-feedback theorem and restricted executable playground below
remain valid evidence; neither is being reclassified as the full proof.

## Request and classification

The user explicitly requested a direct attack on finite-quotient conflict
reflection for one fixed normalized pure structural package, prioritizing a
full FMP proof, then an every-finite-quotient counterexample, then an exact
further localization. Compiler implementation and existential-type inference
are outside this task.

Mode: M3, mathematical soundness and complete-constraint conformance. The
review budget is two independent read-only compiler referees, with focused
delta repair only for an accepted blocking/major issue. The primary owns
research adjudication, documentation, verification and Git integration.
No performance measurement or compiler-suite budget is allocated.

The working copy was isolated from other active worktrees and synchronized to
the named branch. The task/current and direct-main-gate records, the actual
least-closure and trace/unary clauses, Structural S, two-sided constructor
bounds, normalization/equality and scoped structural semantics were read.
The repository question board has no pending structural decision required
for this mathematical task; the consumed Function-observation answer concerns
the separate callback lane and supplies no structural assumption here.
While this work was in review, the branch gained the one-sided default
counterexample at `2327fd57`. It was read and retained. That result refutes an
independent empty-Record default in the powerset construction; it does not
refute the coherent finite-stage scaffolds below. The fixed cutoff package
here uses the same recursive Function-bound pattern to prove an additional
unbounded-rank statement.
Final synchronization also retained the concurrent cross-edit rebuild
decision at `8ddd2df2`; its lifecycle scope changes no structural premise in
this proof.

## Result and durable argument

Classification: **C**, not A or B. The complete reviewed argument is
[Finite feedback quotients and the exact remaining FMP premise](../design/2026-10-04-structural-finite-feedback-quotients.md).

The direct theorem attack produced a finite-feedback quotient construction:
for a free-conflict-free fixed package, any prescribed finite number of
head/presence–activation feedback rounds can be preserved by one finite
surjective monoid quotient. The construction includes full domain/head/child
coherence, regular domain scaffolds and exact descriptor sharing. Default
heads build those scaffolds; they are not inserted into the forced positive
facts.

The theorem reduces the remaining FMP step to a conditional bound on
first-conflict ranks along a cofinal tower of all finite monoid quotients.
The still-open negative case is one fixed package for which all these ranks
are finite but escape to infinity. Proving finite-horizon safety does not
exchange `forall horizon, exists quotient` with `exists quotient, forall
horizon`.

A concrete fixed regular package also shows why an unconditional bound on all
*failing* quotients is too strong:

```text
i=Int, q=Function(x,i), x <: q.
```

It has the regular witness `x=q=Function(self,Int)`. Every length-cutoff
quotient fails, with unbounded first-conflict feedback ranks as the cutoff
grows. Another finite quotient satisfies it. The theorem note gives the exact
free stage formulas and both arguments. This is not an FMP counterexample.

## Direct proof and negative searches

Two independent read-only architecture explorations tested the order/witness
construction and Horn conflict reflection. A third bounded read-only
exploration attacked fixed-package counterexamples after the positive routes
had exposed their remaining obstacles. Role-configured launches requested
`gpt-6.1-sol` with medium reasoning; the root supplied the concentrated Astra
mathematical analysis. Requested launch settings are not an independent
attestation of runtime model identity. Agents received isolated task packets
and did not edit files, spawn children or perform Git operations.

### The preclosed extension requires a new comparison invariant

Allowing an empty side in the two-sided powerset states cannot preserve its
old comparison lemma (G). The exact `x<=Int, y<=Bool` example forces a common
proper upper tree for distinct identity atoms if that lemma is retained.
The theorem note gives the full argument, independent of any particular
default-head policy. Adding head information avoids this example but leaves
finite reuse of newly created child contexts unproved. No global Top/Bottom
or carrier completion is proposed.

### A one-sided multiple-anchor negative attempt has a fresh regular witness

The following attempted counterexample lies outside one-open-anchor incidence,
the two-sided constructor-bound predicate, and incident-anchor selection:

```text
A={a:X}, B={b:X}, C={f:X}, D={g:X},
Q=Function(A,C), R=Function(B,D),
X <: Q, X <: R.
```

Both anchors are open through `X`. There is no constructor-bearing lower
bound on `X`. Choosing `X=Q` or `X=R` fails the other bound by Record width.
However, the simultaneous regular choice

```text
E={}, S={f:T,g:T}, T=Function(E,S), X=T
```

satisfies both original comparisons. Their negative arguments require
`{a:T}<:E` and `{b:T}<:E`; their positive results require `S<:{f:T}` and
`S<:{g:T}`. All four hold directly by width and reflexive payload comparisons.
Thus failure of the known sufficient predicates still does not force
nonregularity.

### A signed marker renewal exists, but the tested composition fails

The negative search did not merely assume that suffix descent renews a unary
marker. It checked the following actual legal step. At a trace with
`L(w)<:U(w)`, suppose `U(w)` has field `m` and the descriptor scaffold supplies
`L(w m)=Function(R,Z)`, with `R={m:E}` and `E={}`. Descent through `m`, then
the negative Function argument, yields

```text
U(w m arg) <: R,
U(w m arg m) <: E.
```

Hence field `m` really is forced at the renewed address `w m arg`. The payload
is constrained to have a Record head, however. A second use of the same layout
at that renewed address would force a Function head at its `m` payload and
give a finite conflict. This rejects only the terminal-payload layout.

A recursive scaffold `L={m:Function(L,E),...}` removes that payload clash.
For one original comparison `L<:U`, successive descents by `t=m arg` instead
alternate directions. The first gives `U(wt)<:L` and forces `m`; the second
returns to `L<:U(wt^2)`, where the fixed lower field does not force another
marker. A phase construction or another comparison is still needed. Forcing
universal navigation through `m arg` would also force `m` independently of
the intended marker, since that field is needed for the navigation itself.

These are bounded checks of explicit layouts. They do not exclude a different
multi-bound phase gadget. No exact package with a free model and failure on
every finite quotient was obtained. In particular, no generic two-ended Horn
rule is treated as source-generated without its structural realization.

## Verification and review

The primary ran focused finite mathematical probes of the fixed
`q=Function(x,Int), x<:q` example on eight length-cutoff monoids, depths 2–9.
The initial probe retained the signed original trace, primitive descriptor
prefix transport, Function head transfer/descent, domain transport/parent
closure and the exact atom's absent children. After the accepted coherence
repair, the eight instances were rerun with explicit reverse
child-domain-to-parent-head saturation: sixteen bounded instances in total,
eight under the complete presentation. All predicted pre-overflow head/trace
formulas agreed. The complete presentation checked 28 pre-overflow stage
cases; the numbers of completed feedback rounds before the first legal
conflict were again 1–8, respectively. This bounded computation checks the
example, not unrestricted FMP or the general regular-stage theorem. The full
argument is in the theorem note; no experimental pattern is used as a proof.

All 17 relative links introduced in the five changed files passed target and
heading-anchor checks; the new documents' code fences and all five files'
whitespace checks passed. `git diff --check` on the full staged diff also
passed before integration.
No compiler code, test contract, source generator, Cargo build, Oracle run or
performance benchmark was changed or run. No broad test suite is relevant to
these mathematical document changes.

### Accepted initial review finding and repair

Two independent read-only compiler-referee reviews covered (i) free-stage
reachability, exact descriptors and simultaneous quotient transfer, and
(ii) the fixed-package quantifiers, cofinal rank reduction and examples. Both
identified the same major issue, classified as blocking by the quantifier
review: the old free `F/G` plus one-way liveness presentation did not prove
complete-model construction on an arbitrary finite quotient. With only
Function arg/ret coordinates, `q=Function(q,q)`, an unrelated free `x`, and
the singleton quotient, `x` is live at root and children; defaulting its
unforced head to empty Record is invalid, while a Function loop is valid.
This was a defect in the proposed quotient-completion argument, not a
counterexample to free completion or FMP.

The primary accepted the shared finding as one repair bundle. The theorem
note now expands the complete package's existing tagged domain/head/child
coherence into its entailed Horn implications and names the resulting proof
schedule `Fbar/G`. A live ranked child forces its owning constructor head;
a live Record payload forces its field present. This is model-conservative
on each fixed quotient, not an addition to the source fragment or solver
rejection policy. It is not claimed to follow from the old one-way `Live`
listing alone.

Lemma 1 proves that those reverse implications are redundant on the coherent
free stages generated from the fixed package's seeds: every canonical child
has forced parent shape, and a default has no children. Lemma Q separately proves complete
finite-quotient default completion after `Fbar/G` stabilizes. Theorem 3 uses
the resulting unary/domain envelopes, and the rank equivalences depend on
that complete quotient lemma. The initial reviewers' clean findings on the
other regions are retained. One fresh focused delta reviewer checked exactly
this accepted repair and its dependent claims, including the actual
repository coordinate encoding and the fixed-quotient model construction.
That review found no remaining blocking or major issue. Its one diagnostic
clarification, spelling out `I={arg,ret}` for the singleton example, was
accepted and incorporated. The review did not independently re-prove the
cited prefix-pushdown regularity theorem or certify the production
Function/effect bridge. No unrestricted FMP claim was submitted or approved.

## Integration and remaining action

The reviewed theorem, this progress record, `tasks/current.md`, the direct
main-gate navigation and design index are synchronized without changing the
unrestricted gate's open status. The initial and focused delta reviews close
the mathematical claims actually made in the note. No source-generation
assumption was added, and no claim that production derives Structural S,
two-sided closure or (BR) was made.

The mathematical next task is exactly the conditional bounded-rank premise
(BR), or one fixed normalized package with finite but unbounded cofinal
conflict ranks. The existence of a satisfying quotient excludes that negative
target immediately; failure on a non-cofinal family does not establish it.
Compiler implementation remains unauthorized.

## Executable finite-quotient playground follow-up (2026-10-04)

Following the user's explicit research-playground direction, a standalone
checker was added at [`tools/research_structural_feedback.py`](../../tools/research_structural_feedback.py).
It implements the reviewed `Fbar/G` clauses for the fixed package
`q = Function(x, Int), x <: q` over the restricted `{arg, ret}` alphabet:
exact left-shifted descriptors, right/suffix Function descent with signed
orientation, descriptor and active-head transfer, domain prefix/child
coherence, and atom child denials. For conflict-free finite quotients it
completes unknown live leaves with empty Records, then independently checks
the resulting graph's exact descriptor equalities and `x <: q` by coinductive
graph traversal.

The run `python3 tools/research_structural_feedback.py 8` checked cutoff
monoids of depths 2–8. First conflict ranks were 1–7, matching the earlier
hand-bounded ranks for depths 2–9. It also exhaustively enumerated 449 labelled
two-generated monoid presentations through size 4: 443 conflicted and 6
survived; each surviving quotient produced a finite graph that independently
passed both exact descriptor equations and the original comparison. The first
survivor has four elements and noncommuting generator actions (`arg*ret=2`,
`ret*arg=1`), which directly exercises the distinction between descriptor
prefix shifts and comparison suffix descent.

An independent compiler-referee review found one rank-convention bug in the
first checker revision: the singleton quotient's descriptor-only Function/Int
clash had been counted as round 1, while the governing characterization
assigns descriptor-only conflicts rank 0. The checker now runs initial
descriptor/domain/coherence saturation without comparison transfer before
counting feedback rounds, and asserts the singleton case. Re-run histogram:
417 of 449 presentations conflict at rank 0, 26 at rank 1, and 6 have checked
models. The reviewer confirmed the corrected left/right action order, exact
limited domain rules, enumeration count and independent graph checks; its
finding is closed with no remaining review issue.

This is a bounded executable characterization of one reviewed package, not
an FMP proof or a counterexample search over arbitrary `Gamma_P`. The package
already has a regular model, so the surviving quotient is a consistency
check; the experiment neither closes (BR) nor generalizes to other descriptor
systems. Exact arbitrary-package encodings, broader package generation, and
counterexample shrinking remain the next playground work. The exact command
and Python compilation check passed; no compiler behavior changed.

## Generated-package quotient search (2026-10-04)

A second model, [`tools/research_gamma_quotients.py`](../../tools/research_gamma_quotients.py),
generalizes the fixed example to a finite generated family while keeping the
same reviewed left/right address actions and closure schedule. Its `Package`
records separate original bound IDs, fixed heads, and exact constructor-port
equations. The exhaustive generator covers all nine choices for the two
children of one fixed Function root (`q`), one fixed Int root (`i`), one free
root (`x`), and every zero-, one-, or two-bound multiset from the nine ordered
root inequalities. This yields 495 packages, including duplicate inequalities
with distinct IDs. The generated family uses Function `(-,+)`, an Int atom,
and empty Record defaults; there are no nonempty Record descriptors, optional
fields, lexical rigid permissions, effects, or source-generation rules.

`python3 tools/research_gamma_quotients.py 4` exhaustively checked these
packages against all 449 labelled two-generated monoid presentations through
size four: 222,255 package/quotient pairs. Of these, 27,383 quotient
saturations completed conflict-free and each produced a graph that was
independently checked for fixed root heads, root liveness, shifted descriptor
domain/equality, and every original bound; 194,872 reached a conflict. The
special fixed package from the first playground matched its feedback ranks
under both implementations on all 449 monoid presentations. Focused malformed
input and deliberately damaged-witness checks also rejected both cases.

The finite package search asserts no counterexample to unrestricted FMP: it
only checks regular quotient models in a restricted generated package family.
If a saturation ever claims SAT while its independently constructed graph
fails, a greedy bound-removal shrinker reports a smaller package. No such
mismatch occurred. Independent compiler-referee review found and localized
three checker defects before closure: G initially advanced only one path edge
per feedback round; validation allowed descriptor edges without a fixed
constructor parent; and the graph checker initially omitted fixed root-head
and root-domain checks. Each was repaired, and the focused counterexamples
were turned into assertions. The final review also checked descriptor-domain
equivalence and confirmed complete G closure within a round. No source/package
counterexample was found; these were playground implementation defects.
Production inference remains untouched.
