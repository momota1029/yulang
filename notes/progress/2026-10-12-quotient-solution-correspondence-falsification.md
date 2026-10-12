# Quotient solutions: flat-store characterization and source-allocation obstruction

Date: 2026-10-12
Status: frozen unreviewed research; conditional characterization, no new
source-qualified counterexample or parent theorem closure
Assigned baseline: `d12c80b0bf5ea1c55eb24b27fc1de0dfe9b6706a`
Exclusive lease: this file only; complementary researcher, no delegation
Budget: 30-minute ceiling, at most one lightweight process, no builds/tests

## Objective and governing scope

Attack the proposed correspondence between a finite quotient store and the
original store's solutions satisfying an occurrence-qualified Value-coordinate
equality. The assigned fixed inputs are the independently reviewed
[fixed Q construction](../theory/2026-10-12-fixed-term-quotient-transition-proof.md)
and [dependency census](2026-10-12-fixed-term-quotient-transition-falsification.md).
The method is semantic-definition inspection and a handwritten substitution
discriminator, followed by source-publication/allocation owner inspection.
This lane does not reconstruct the main constructive theorem.

Governing sections are:

- Top-level inference principles §§1–5.
- Parent-copy SCC decision: Selected operation and compiler responsibility;
  Value-reference SCC clarification; Apply-result ownership; Nested Apply
  membership; Definition-root ownership; Retained boundary.
- Value/type association: Approved extrusion-event qualification;
  Definition-root origin for nested call-demand extrusion; Qualification;
  Implementation and proof boundary, including the final source/generalization
  preservation requirement.
- Copied-row ownership: Decision; Scope and proof boundary.
- Contextual residual lineage selection: Selected policy; Preserved contract
  and open obligations.
- Source Generalize definition §§2–3, selecting construction §§3–5; directly
  inspected construction §§3.3, 3.4's scoped-strategy definition, 4, 5.1–5.2.

The selected operation qualifies an authentic extrusion occurrence using its
origin/receiver Values' SCC and equates its actual retained type pairs. Value
vertices, type coordinates, subtype constraints, storage adjacency and raw
parent/polar provenance remain separate domains. Copying/freshening introduces
no Value-reference incidence. Same-SCC qualification does not classify a
coordinate as a source template or fixed publication anchor.

## 1. What correspondence is actually defined

The fixed Q input explicitly defines a finite operational transform and its
native suffix for one term. It excludes all-assignment preservation and does
not define a general `Sol(store)` relation. Consequently a new all-store
solution theorem requires an explicit interpretation; its conclusion cannot
be attributed to that input or approved solely by defining the theorem.

The approved Source Generalize construction does define
`Sat(J_m;v,s)` (§5.2): one assignment and one scoped strategy satisfy every
active clause and client predicate in an allocated source program. This is
richer than assigning an unscoped type to each solver row. Its genuine local
constructor laws remain independent premises L1–L5. The missing definition
for this packet is the mapping from the proposed finite compiler store,
live operands, equality classes and contextual obligations into that source
program and its declaration/allocation scopes. There is no supplied general
store-to-`J_m` correspondence for the new equality operation.

The following flat-store interpretation is therefore a **candidate assumption**
used to delimit falsification, not adopted language meaning:

1. Every type coordinate has one valuation in its kind's semantic domain.
2. A structural description is interpreted compositionally from its children.
3. Lower/upper entries denote their complete subtype clauses. Every other
   active clause has explicitly identified coordinate operands; none is lost.
4. Equality means equal valuations. Allocation levels, historical cache keys
   and raw provenance are not additional semantic predicates in this model.
5. Quotienting substitutes class representatives in every clause operand while
   preserving primitive relations, constructor tags and noncoordinate data.

Hypothesis 4 is a boundary, not a claim that levels/history never matter to
inference. They determine future operations outside this static model.

## 2. Why the exact flat-store attack has no counterexample

Let q map raw coordinates onto equality classes. For a quotient assignment w,
define its raw lift by `v(a)=w(q(a))`. Conversely every raw assignment v
satisfying the selected equalities has one well-defined class assignment w.
The interpretation of each substituted structural operand under w equals
the original operand's interpretation under v, by compositionality. Each
whole clause consequently has the same truth value on the two sides.

This is a conditional characterization of the candidate interpretation.
It explains why neither Function variance nor a larger finite valuation
enumeration can falsify it. For example, replacing both operands of
`Function(a,b) <: Function(c,d)` preserves the same contravariant argument
test and covariant result test; no reversal or equality of Function roots is
introduced. Shared occurrences use the same q, while opposite-polar copies
are identified only when their actual qualified pairs require that equality.

Concatenating both member bound sides preserves each conjunct, even if their
union is inconsistent. A newly conflicting lower/upper pair means both the
quotient and the equality-constrained original have no solution. It is not a
static correspondence counterexample. Missing replay would be an operational
incompleteness issue, requiring a consumer proof beyond this characterization.

Raw history can remain outside these clauses without affecting their truth.
Its cache interaction and owed work still require the separate operational
proof already exposed by the fixed Q input. No canonical-cache mutation or
omitted-Lambda-local attack was repeated here.

## 3. Freshening discriminator and the existing source witness

A handwritten preliminary discriminator used a high parent B at level 2,
positive-extrusion copy C at level 1, native link `U(B)=[C]`, qualified B=C,
and publication boundary 1. Native raw `freshenAbove(1,B)` copies B into
separate use rows while retaining C. Quotient-first freshening of the live
representative C retains that one row. This shows that raw cutoff/freshening
and quotient substitution do not automatically commute.

Two independently copied rows can be refined to Int and Bool while both
remain below one common upper type. If both uses instead consume the same
retained coordinate and both refinements are imposed as equalities, they
conflict. This is a discriminator for an equality-unaware freshener, not a
counterexample to complete transport of the equality into lawful use frames.
The raw copying side did not preserve that latter premise.

On tracing the requested actual source event, this discriminator was found to
repeat the mechanism already derived in
[correlated helper search](2026-10-12-intrusion-occurrence-counterexample-search.md)
§§1–3. That artifact supplies the authentic recursive f/nested g term,
same-SCC G-to-F call-demand occurrence and actual polar pairs, two native
helper instances, and conditional `bool <: int` failure when C=B is enforced
in those instances with the fixed boundary-1 C anchor. Its source derivation
was inspected; it was not rerun or presented as new independent evidence.
No new minimized source witness is claimed by this lane.

Early activation is mathematically possible for that source: its resolved
F-to-G and G-to-F references already determine qualification before the
helper publication. The approved root ownership rule and these source facts
do not supply an actual early consumer. A delayed schedule leaving previously
independent instances intact is not refuted by the conditional early-failure
argument. Neither this lane nor the existing witness establishes failure
for every lawful schedule and complete source-use allocation.

## 4. Precise publication/allocation obstruction

The Source Generalize construction gives a discriminating owner test rather
than another scalar probe:

- §5.1 obtains the validating source component from recursive-group/definition
  registration. It does not obtain that component from Value-reference SCCs.
- §5.1 retains the whole relation of own-component Internal descriptions.
  Eligible ordinary Desc declarations outside the fixed dependency closure
  become templates at their original scopes.
- Established/Mono/OneShot contracts fix their free descriptive dependencies;
  Shared binders remain once. A raw provider identity does not alone fix its
  separate Internal inferred description.
- §5.2 allocates one whole component frame per independent instance before
  assignments or histories, and routes monomorphic aliases to one frame.

Therefore `level(C)=1` and `SCC(F)=SCC(G)` do not decide whether source
allocation keeps C once, templates its descriptive coordinate with the whole
component, or retains an equality to an independently fixed anchor. Original
Simple-sub's level cutoff is evidence for its native operation, but no
correspondence identifies that cutoff with this approved source classification
for the intrusive cross-level helper.

The exact absent premise is:

> At the actual helper publication, owning source records classify the parent,
> copy, equality clause and their free dependencies; the source Generalize
> allocation and the proposed quotient/freshener use those same classifications
> and original telescopes in every independent or aliased frame.

If this owner establishes that C stays fixed and each frame retains C=B_i,
the existing correlated-helper contradiction applies to that construction.
If the owner establishes a different lawful whole-component allocation, that
contradiction cannot be imported by treating the native level as a semantic
fixed-anchor certificate. This note selects neither classification and does
not weaken the parent source theorem or reopen an approved language meaning.

## 5. Effect coordinates and residual lineage boundary

The flat characterization extends to an effect clause only after its
interpretation and coordinate operands satisfy the explicit compositionality
premise. Function variance alone provides no such owner proof for effect
attachments, filters, contexts, guards, provider evidence or future residual
replay. The pure reference Typer has no Effect coordinate/recipe constructor.

Approved residual policy requires keeping each recipe's constructor lineage
and propagating applicable current/future lowers to every retained recipe,
with its exact attachment, filter, origin and context. Row-coordinate equality
does not identify recipe identities or authorize coalescing residual gammas
whose own qualifying pair is absent. The reviewed residual carrier remains
a candidate beyond the narrow selected lineage policy.

Thus a theorem interpreting a store as bare subtype inequalities can be
conditionally true while omitting these required source clauses. Conversely,
once the complete contextual clauses are furnished and transport is proved
to preserve their interpretations, the flat substitution argument has no
additional scalar polarity objection. No effect-source counterexample or
complete effect-congruence theorem was derived here.

## Evidence, resources and next action

Commands used: bounded `cat`/`sed`/`rg` authority and artifact reads; direct
reference `Typer.scala` constructor/cutoff inspection; read-only
`git rev-parse HEAD` and `git status --short`; `sha256sum` dependency snapshots;
final dependency and document-integrity recheck. Git mutations: zero.

Coverage: handwritten flat-clause substitution, Function variance, positive
high-to-low extrusion/cutoff discriminator, existing authentic two-use source
witness inspection, source publication/allocation classification, and residual
lineage boundary. No enumeration, random seed/range, executable mutation,
tests, builds, performance samples or compiler edits. Some initial combined
reads were truncated; decisive artifact/authority windows were reread. Full
historical task/lab bodies and unlocated discovery filenames are not claimed
as inspected.

The mathematical characterization and native cutoff inspect different
premises but share supplied equality and native source inputs. Neither is an
independent empirical oracle for Yulang source inference. No checker assuming
transition rules was executed. At most one lightweight process ran after
initial independent read batching; zero heavyweight processes. CPU/RSS and
exact reasoning elapsed time are unmeasured. Configured/requested researcher
Sol/high was supplied by the primary; observed effective runtime is unknown.

Unverified: complete Yulang source admission, actual event/early-graph producer,
store-to-scoped-program interpretation, publication records for the intrusive
copy, allocation/freshening bridge, all histories and lawful schedules,
Effect/Call/contextual clause interpretation, abnormal paths and original
soundness/principality/progress/termination/F5 parent gates.

**One next action:** obtain the construction-owned publication classification
and allocated equality clause for the already recorded correlated helper;
use it to apply or reject that existing witness. Another flat solver or
equivalent cutoff probe leaves this precise premise untouched.

## Dependency snapshot and commit packet

| Direct dependency | SHA-256 |
| --- | --- |
| Fixed Q construction | `7ed3086921c18bb823b622977a73bc4c1d867c30b64116658194af28ef0582a9` |
| Fixed Q dependency census | `05bb046e66b51eb0b091c68723fb46d8f4897b2702d14a5e842c629621373674` |
| Top-level principles | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| Parent-copy SCC decision | `6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b` |
| Value/type association | `28a0c2aa196912e59e9adb9e62e30d171a03fc485d36314db02c5e13b74f6775` |
| Copied-row ownership | `7c170c346eeeabca50afe254425eba0c83995cb5e61bf257290ce2757c78bfbd` |
| Residual lineage selection | `d5c46b74d678028046bdfa0f7fd2b71bb2abfb112987000fe43e0fa5875d5d98` |
| Source Generalize definition | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| Source Generalize construction | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| Existing correlated helper search | `ef308b68e967d916278b2d6e106731c723368f0477ecc947a12eb99c7f17a956` |
| Reference Typer.scala | `f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9` |

- Exact leased/changed path:
  `notes/progress/2026-10-12-quotient-solution-correspondence-falsification.md`.
- Baseline: `d12c80b0bf5ea1c55eb24b27fc1de0dfe9b6706a`.
- Changed dependency hashes: none caused by this lane; snapshots rechecked.
- Review status: frozen research-only characterization and precise
  source-allocation obstruction; a fresh `compiler_referee` passed with no
  blocking, major, or minor findings. Review covered the flat assignment
  correspondence, Value-SCC versus source-component distinction, the repeated
  freshening discriminator, residual-lineage boundary and recorded dependency
  hashes. It found no new source-qualified counterexample and does not certify
  source admission, a lawful complete allocation, operational replay or parent
  theorem closure.
- Checks already run: static authority/source/artifact inspection, handwritten
  conditional clause-transport calculation, duplicate-attack identification,
  publication/allocation owner audit, dependency and whitespace checks;
  no tests/builds/executable experiments.
- Proposed one-line checkpoint message:
  `research: separate flat quotient solutions from source allocation obligations`.
- Shared-record deltas left for primary/curator: retain the distinction between
  Value SCC and validating source component; record the exact publication and
  equality-allocation premise. Reuse the existing helper witness without
  counting it twice. Keep source/lifecycle/effect and parent gates OPEN.
  No shared records, authority, compiler, questions or another worker's files
  were edited. Writes stopped before submission for frozen review.
