# Fresh termination analysis: an acyclic accumulator pump

Status: **Draft mathematical counterexample (B); kernel-checked algebraic core,
not a kernel-checked infinite Step trace.** Date: 2026-11-13.
Scope: `GeneralNominalValueSteps.Step`, hence also its downstream/support
superrelations. No guard or language rule is changed.

Authority: [spec §6.3 and K2](../../spec/06-roles.md), including the decisions
of 2026-11-07 through 2026-11-13, and the
[approved B4 draft, addenda 1–6](2026-11-08-b4-main-statement-draft.md).
The earlier [plan](2026-11-13-termination-proof-plan.md),
[downstream support](2026-11-13-general-nominal-downstream-support.md),
[budget](2026-11-13-general-nominal-budget.md),
[value provenance](2026-11-13-general-nominal-value-provenance.md), and
[checkpoint](2026-11-13-general-nominal-provenance-checkpoint.md) are evidence,
not additional semantic restrictions.

## Conclusion

Cycle exclusion is insufficient. A pending producer can supply two constructors
of fresh input, while its own blocked child depends on a separate accumulator.
Each round consumes two constructors, adds one to that accumulator, and obtains
two more from a different pending output. Dependencies point backwards in stage
number; they never form a cycle. All finite prefixes have finite type models.
The accumulator values are pairwise inequivalent, so same-input merging does
not stop generation. The finite signature basis required by L5–L7 therefore
cannot be justified by cycle exclusion and Paterson descent alone.

This is a **semantic gap**, unlike the previous omitted captured-value edge.
Section 7 states the owner question, with the lazy option first. The complete
operational construction below is a paper argument; section 8 specifies exactly
which parts have been translated to Lean.

## 1. What an infinite trace must contain

Write `s → t` for the value-guarded Step, with registry and initial root fixed.
Let `s : Nat → Tracked roles`, `SourceFormed (s 0)`, and `s n → s (n+1)` for
every n. Formation persists. Every step is administrative or an enabled,
guarded installation of a packet that is not `Committed`.

For every cutoff N there is such an installation at an index n ≥ N. Otherwise
the suffix starting at N is an infinite chain of `Passive` steps, contradicting
`GeneralNominalValueSteps.passive_accessible`. This exact statement, including
the full guard and noncommitment premises, is proved in
[GeneralNominalInfiniteInstallations](../../lean/Yulang/GeneralNominalInfiniteInstallations.lean).
Neither Checked nor fairness is needed for this reduction.

“Fresh” needs care: a novel installation can revisit an occurrence with a new
capture or new children. The theorem above does not say that every installation
uses a new identity, nor that all semantic input signatures are distinct.
There is also a paper reduction from finitely many installed invocation IDs to
finitely many installations:

1. If the installed IDs belong to a fixed finite I, the possible source IDs
   belong to the initial finite `sources` plus the union of
   `GeneralNominalAllocation.keys registry i`, i ∈ I, mapped through the fixed
   seed. This includes row IDs and ordinary-atom free IDs. Refresh's `support`
   condition cannot add IDs; reobservation fixes the basis.
2. Each declaration has a fixed finite translated query tree. Successful
   reports have bounded length and origin depth. Two endpoint traversals can
   duplicate a subtree, but recursion still consumes query syntax. Labels are
   from the finite source universe and the fixed queries. The constructor
   catalogue itself need not have finite range; an arbitrary observed layout
   either passes a fixed query or produces no successful installation.
3. Thus captures, input/output schemas, and emitted demands have finitely many
   signatures. Named requests originate in the one initial demand or in a
   finite declaration clause. Child identities are fixed by invocation,
   declaration, and clause. Slot renamings are erased in favor of source IDs.
4. `packet_exact` separates the cached context from Inputs and Outputs. Old
   constraints remain entailed, so the context is not a new delta. Every novel
   installation either makes one previously unentailed delta true or supplies
   a missing emitted edge. Each such fact persists. Finitely many signatures
   give finitely many such first events, a contradiction.

Consequently an infinite trace must install unboundedly many occurrence IDs.
This is a finiteness argument **conditional on finite I**, not a derivation of
finite I from the source. It does not identify diagnostic IDs with semantic
demands. In the example below the stronger claim also holds: the P, W, and C
inputs are pairwise inequivalent across rounds.

## 2. Program and checked initial input

Here `list` is the invariant nominal list constructor; its body is never opened.
Repeated `where` lines are conjunctions. The method body is irrelevant to
saturation of its declaration's requirements.
This uses the specification's surface spelling, including its provisional
named associated-output equations. The current parser reports recovery on this
block; the exact checked formal input below is not claimed to have been produced
by the current frontend. The parser result is recorded in section 8.

```yulang
role P 'a 'b 'm:
    our a.pump: 'b -> 'm -> int

role W 'a 'b 'm:
    type out
    type middle

role C 'q 'm:
    type item

role Extract 'a:
    type item

impl Extract (list 'x):
    type item = 'x

impl C 'q (list int):
    type item = int

impl W (list 'x) 'y 'm:
    where 'y: C('m, item = 'u)
    type out = list (list 'u)
    type middle = list 'u

impl P (list (list (list 'a))) 'b 'm:
    where (list 'a): Extract(item = 'z)
    where (list 'a): W('b, 'm, out = 'z, middle = 't)
    where (list 'a): P(list 'b, 'm)
    our xs.pump ys ms = 0

my trigger(x: 'a, b: 'b, u: 'u) = [[[x]]].pump [b] [u]
```

The relevant inference input is `P(L³ A₀, L B, L U)`, where L denotes list and
A₀, B, U are independent unknowns. No later use constrains U. The formal input
uses eight point sources:

```text
0 = L 1; 1 = L 2; 2 = L 3; 3 = A₀ unknown
4 = L 5; 5 = B unknown
6 = L 7; 7 = U unknown
root = P((0,0), (4,4), (6,6)); seed = 7
```

[FreshPump.initial_source](../../lean/Yulang/GeneralNominalFreshPump.lean)
constructs the actual `InitialSource`; `formed` constructs value-Step
`SourceFormed` with empty journal. `source_models a b u` permits *every* choice
of all three leaves. This is not an inference implementation theorem.

[FreshPumpDeclarations.checked](../../lean/Yulang/GeneralNominalFreshPumpDeclarations.lean)
checks the entire four-declaration registry. P's syntactic input size is 6;
its children have sizes 2, 4, and 5. W's size is 4 and C's child size is 2.
Variable occurrences never increase. For any normalized capture, the recursive
P child has exactly one fewer constructor than the parent and the same variable
multiplicities. W discards its x capture and a constructor. Extract and C have
no children. Thus strict descent survives every capture, as the Lean
`captureStable` proofs check. There are no shadowed fields or tag mergers.

z and t are output-only P binders, produced respectively by Extract.item and
W.middle. u is W's output-only binder, produced by C.item. None occurs in an
unnamed child input. The actual emitter sends Extract.item and W.out to the
*same* `capture.outputs 3`; W.middle goes to `capture.outputs 4`.
`shared_outputs` proves this without assuming a parent-output equality.

The extra `middle` output is deliberate. It names the intermediate L u in the
existing source basis. Without it, a proof that a nested output can always be
made into nominal descriptors would need an additional representation argument.

## 3. Inductive schedule

Let bₙ = Lⁿ⁺¹ B and m = L U. At the start of round n the next generated request
is `Pₙ = P(L³ Aₙ, bₙ, m)`; its three inspected list constructors are recorded.
Use the actual invocation/declaration/clause origin allocator throughout.
Installing Pₙ emits precisely:

```text
Eₙ = Extract(L Aₙ, item = zₙ)
Wₙ = W(L Aₙ, bₙ, m, out = zₙ, middle = tₙ)
Pₙ₊₁ = P(L Aₙ, L bₙ, m)
```

Materialize and observe the fresh compound-input endpoints. Install Eₙ; it has
no children and discharges, adding zₙ = Aₙ. Install Wₙ; it emits

```text
Cₙ = C(bₙ, m, item = Aₙ₊₁)
zₙ = L(L Aₙ₊₁),       tₙ = L Aₙ₊₁.
```

Here Aₙ₊₁ is Wₙ's fresh output-only source, not a guessed input or a new
unconstrained input binder in the declaration. Therefore Aₙ = L tₙ = L² Aₙ₊₁.
Observe tₙ and the equal zₙ/Aₙ endpoints. Pₙ₊₁ now has input
`(L³ Aₙ₊₁, bₙ₊₁, m)`, establishing the induction hypothesis.
`pump_round` checks this recurrence using the existing declaration substitution
and the actual recursive child's patterns.

Cₙ's first input is known. Its second is L U, also known, but its candidate
needs the head of U to compare with int. U stays unknown. The unique visible
candidate is never used to choose U=int. Thus every Cₙ remains inspection
pending and no C packet is installed. No final error is emitted during this
schedule. Each round is finite and performs three installations, so concatenating
the rounds gives a countably infinite trace if their guards hold.

## 4. Why the support guards allow every round

Put Sₙ = {E₀,W₀,…,Eₙ₋₁,Wₙ₋₁}; S₀ is empty. All Eᵢ in this set are discharged.
Pₙ and Eₙ can use Sₙ, and Wₙ can use Sₙ together with Eₙ. A larger support may
be restricted to the dependency pool using `slice_restrict`; the existing
alternative enumeration retains the resulting explanation.

Inductively the required input and inspection heads follow from source facts,
earlier W outputs, discharged Extract outputs, and packet *input* facts. Input
facts carry the support used for installation, not the installed producer itself
(`Fact.dependencies`). Consequently using Pₙ's materialized `L Aₙ` does not make
Pₙ a necessary provisional producer for Wₙ. P's where-output uses of z and t
are self-links of output-only binders; they assert no Aₙ=zₙ equation. That
equation comes from the discharged Eₙ.

The generation graph consists of the P spine, Pᵢ→Eᵢ, Pᵢ→Wᵢ, and Wᵢ→Cᵢ.
There are no cross-round aliases (section 5). Wᵢ cannot generate Pₙ, Eₙ, or Wₙ
for n>i; it only generates Cᵢ. Thus all chosen producers satisfy `Admissible`:
each is discharged or external to the focus's ancestry.

For the stronger `Grounded` condition, induct on i. Wᵢ's unresolved waiting
cone consists exactly of Wᵢ and Cᵢ. At Wᵢ itself, required heads are the three
input roots and the outer list read of its first input. They have explanations
using Sᵢ. The proper child path reaches only Cᵢ; its entire input values are
`(Lⁱ⁺¹ B, L U)`. Their known heads are list wrappers; their terminal B and U
remain independent unknowns. They have explanations using Sᵢ and input facts,
and do not require Wᵢ's output, any later output, or any Aⱼ value. The induction
hypothesis grounds those explanations, so `Grounded Wᵢ` follows.

This checks value-subterm and retained-origin needs, not just the current read
list. It also covers *every certified View*: views preserve the full model set.
Independently varying B, U, and the terminal A leaf prevents a certified view
from exposing a head at B/U or making either input reach an Aⱼ-dependent value.
Any exposed alias of a known accumulator/waiting-input wrapper has the same
earlier-stage explanation. Finite nominal depth bounds these paths. Discharged
Eᵢ provide leaves of the grounding derivation. No preservation of arbitrary
old grounding certificates is assumed; this particular certificate is rebuilt
by induction at each finite prefix.

Hence support edges go to strictly earlier W stages or discharged E leaves.
There is no unresolved output-support cycle, upstream or downstream. The prior
P/W/G/C/D/Extract example's mutual dependency is absent: here the accumulator
does not contain the replenished A tail.

## 5. Consistency, merging, K2, and exact transition bookkeeping

For a prefix after N W installations, choose arbitrary finite a, b, u and set

```text
Aᵢ = L^(2(N−i)) a                  (0 ≤ i ≤ N)
tᵢ = L^(2(N−i−1)+1) a, zᵢ = Aᵢ   (0 ≤ i < N)
bᵢ = L^(i+1) b, m = L u.
```

These satisfy every displayed equation. In each emitted frame assign *both*
endpoints of a compound input to its instantiated nominal value. Assign merged
captures to the same captured value; lower unions and upper intersections of
equal values remain equivalent to that value. Assign each output-only source
as displayed, all unused reserved values arbitrarily, and rows the empty row.
This extends the fixed eight-source assignment to every reserved identity.
Injective allocation prevents conflicting assignments. Every retained origin
observes the indicated value; input Fits, repeated-capture checks, materialized
tests, named equations, and site conditions all hold. No equation from the
uninstalled C body is included. This also works immediately before each proposed
installation by choosing the longer prefix's assignment.

Specialize a=b=u=int. Every source denotes a finite list tower. A journal-entailed
nominal argument edge strictly decreases its tower height (the argument in
`GeneralNominalOutputGrowthModels.observation_decreases`). Structural edges
are absent in the chosen views. Thus both raw and journal K2 cycles are absent
at every required root and inspection. A cycle in an infinite limit is not a
cycle entailed by any finite prefix.

For i≠j, bᵢ and bⱼ are inequivalent in this model. Hence two P, W, or C requests
from different rounds cannot have SameInputs in the journal. Eᵢ inputs are also
separated: their heights are 2(N−i)+1. Nonpoint endpoint *syntax* does not change
the argument: retained actual origins denote these values, and
`different_inputs_prevent_merge` applies. All alias classes remain singletons.
The new `distinct_pending_inputs` is the general-carrier form of this argument,
with its actual-origin `Denotes` premises explicit.

The remaining operational details are finite constructions, rather than new
semantic premises:

| Step obligation | Construction for this schedule |
|---|---|
| Actual emitted sites | Use `GeneralNominalFeedbackSites.emitted`, including retained origins and distinct lower/upper IDs; never replace it with point sites. |
| Source-fresh allocation | Initial IDs are ≤7; canonical invocation-origin encoding is injective and `source_above_invocation` makes each child ID exceed its parent. P/E/W IDs are distinct. Old reservations remain owned; all later IDs are old or reserved. |
| Compound-frame equality | The preceding assignment construction works for arbitrary leaves. Input materialization forces both endpoint values to equal the same captured nominal value in every journal model. Repeated captures of this value retain that equality. |
| Certified refresh | Extend the finite slot table only with already reserved IDs. Copy old observations. For each needed emitted `L v`, record a descriptor with the existing point representative of v; name the inner W output with tₙ. Record tₙ=L Aₙ₊₁ and Aₙ=L tₙ. All are full-journal entailments, so `exact` holds; the old slots and atoms give `Refines`, and reserved membership gives `support`. Keep unknown Aₙ₊₁/B/U slots unresolved. |
| Refresh progress | Each batch adds a previously unknown compound endpoint or tₙ/Aₙ head. If already recorded, omit that batch. This is finitely many ordinary refresh steps, not unguarded reobservation. |
| Prepared and Local selection | Finite nominal/variable queries finish for P/E/W; all unnamed lower roots are known. Catalogue and interpretation are fixed, captures are consistent, schemas are supported, and there is exactly one candidate of each role. |
| Both merge-closure premises and Joint | SameInputs has no other occurrence in the role's class by the separating models. The singleton class and the prospective packet model give Joint and choice compatibility. |
| Novelty | P and W add a fresh child edge. Before E installs, its fresh z is still independent of Aₙ; a separating assignment refutes commitment to z=Aₙ. |
| Formation | Start with the proved InitialSource; each installation and refresh has the premises just listed. Apply SourceFormed.update finitely often per round. |

These observations establish the round construction on paper for the current
Step, including its stronger value guard. The Lean files do **not** contain
this entire installation/refresh construction; its formalization is an explicit
remaining task, not an implicit premise of an advertised Lean theorem.

## 6. Why a finite signature basis fails

The finite source supplies the *alphabet* L, A₀, B, U. It does not bound the
length of Lⁿ⁺¹ B. Already with B=int, the existing carrier's `tower_equivalent`
says Lⁱ int ≈ Lʲ int iff i=j. The new `no_finite_accumulator_basis` proves there
is no finite list of arbitrary carrier values covering all bₙ even modulo that
equivalence. Each bₙ occurs in an installed P/W input and a newly pending C
input. Thus the failure concerns demands actually used by the paper schedule,
not arbitrary tall denotations of an untouched unknown source.

If “needed input heads” means just the outer constructor tag, the tags are
indeed finite. That quotient is too coarse: it identifies distinct C inputs
whose outputs must not merge, and cannot determine the next P materialization.
If a signature retains the normalized captured input structure needed for those
operations, it contains Lⁿ⁺¹ B and is infinite. Including support cannot make
an already infinite input projection finite. Supports also accumulate distinct
earlier W producers. Every snapshot's support proof is finite; there is no
source-fixed bound on their combined input-generation budget.

This does not contradict checked Paterson descent. It compares parent and child
under one capture. The associated equations refine that capture before the next
round; `pump_round` exhibits exactly the replenishment. A fixed missing-fact
measure cannot be constructed from the proposed finite basis for this relation.
No natural-valued or other well-founded rank can decrease along the infinite
paper trace.

## 7. Classification and owner question

All exclusion decisions have been respected: wait until needed heads are known,
output-only binders, stable Paterson descent, equal-input merging, reached/inspected
K2 through nominal arguments, and downstream deferral of unresolved output
*cycles*. The pending C requests are pairwise distinct and their inputs have no
output-cycle dependence. Extending the old provenance guard with yet more
captured-value paths therefore does not address this example.

**Owner question:** may an undischarged, acyclic producer's output justify new
input inspection/generation without a separately established finite budget?

1. **Lazy option (recommended):** defer such use when every explanation needs
   an undischarged associated output; source and discharged explanations may
   resume it. Keep equations for ordinary constraints, merging, and K2. Here
   W₀ may install, but the recursive P cannot inspect the newly exposed A₀
   constructors until the producing requirement is discharged. This is stronger
   than cycle-only deferral and needs owner approval. Its general termination
   theorem would still have to be proved.
2. Retain acyclic provisional use and add a declaration-side or generation-side
   non-amplification condition that accounts for associated outputs and all
   unnamed arguments together. A sufficient condition and its exact rejection
   scope remain to be designed and proved.

No local repair is made. No depth limit, role-level acyclicity requirement,
early diagnostic, or scheduler fairness assumption is introduced.

## 8. Lean scope, audit, and remaining work

Added modules, all imported by appended lines in `Yulang.lean`:

- `GeneralNominalFreshPumpDeclarations`: full Checked registry, shared emitted
  outputs including the intermediate source, exact recursive input requests.
- `GeneralNominalFreshPump`: actual InitialSource/SourceFormed, arbitrary source
  models, exact pattern recurrence, arbitrary finite output-prefix solutions,
  semantic accumulator separation, a same-input exclusion lemma on retained
  origins, and impossibility of a finite extensional accumulator basis.
- `GeneralNominalInfiniteInstallations`: every infinite source-formed value-Step
  trace has novel guarded installations beyond every cutoff.

The load-bearing translated lemma is the combination `finite_prefix` /
`accumulators_distinct` / `no_finite_accumulator_basis`: finite consistent output
prefixes coexist with unbounded semantic input signatures. The Checked and
emitter lemmas tie its recurrence to the existing declarations. It is **not**
a replacement Step, an assumed InstallationOrder, or a Lean proof of
`¬ Acc Step start`. In particular the explicit `Denotes` premises of
`distinct_pending_inputs` have not been instantiated along an actual infinite
trace. No B4/V5 field is newly closed.

The separate audit file is
[Audit/GeneralNominalFreshAnalysis.lean](../../lean/Audit/GeneralNominalFreshAnalysis.lean).
The registered prover role/configuration is absent in this worktree. The primary
constructed these bounded results; a separate read-only reviewer checked the
counterexample, stronger guard, intermediate-source repair, finite-I argument,
and theorem scopes. No registered prover run is claimed.

Final checks:

| Exact command (from repository root) | Exit | Result |
|---|---:|---|
| `cd lean && lake build Yulang.GeneralNominalFreshPumpDeclarations Yulang.GeneralNominalFreshPump Yulang.GeneralNominalInfiniteInstallations` | 0 | All three modules; 651 build jobs |
| `cd lean && lake build Yulang` | 0 | Aggregate build; 1883 jobs |
| `cd lean && lake env lean Audit/GeneralNominalFreshAnalysis.lean` | 0 | All 18 new public theorems; dependencies only propext, Classical.choice, Quot.sound |
| `cargo run -p yu-syntax --example syntax_guide_check -- notes/design/2026-11-13-termination-fresh-analysis.md --quiet` | 1 | The one specification-spelling program block reports 32 recovery/diagnostic entries, including named-output `=` and grouped applications. A second invocation without `--quiet` also exited 1 and located those entries. |
| `git diff --check` | 0 | Whitespace check |

A Python scope check exited 0: the previous `Yulang.lean` is an unchanged byte
prefix, followed by exactly three imports; the only other tracked edit is the
design INDEX entry; all 18 public theorems have audit entries; prohibited proof
constructs are absent; local note links resolve. No existing Lean line, frozen
file, specification, plan, lake configuration, or git ref was changed.

Development elaboration checks for `Yulang.GeneralNominalFreshPump` and
`Yulang.GeneralNominalInfiniteInstallations` initially exited 1 (a shadowed name,
a beta-reduction rewrite, and dependent elimination). Those errors were fixed
in the new files; the final commands above passed. The parser recovery was not
fixed, and its expected result was not changed. No full legacy audit or broad
Rust suite was run.

Remaining: owner choice; full Lean installation/refresh induction for the pump;
source-inference-to-InitialSource bridge; and a new termination argument after
any approved change. None is silently supplied by the finite-prefix model lemma.
