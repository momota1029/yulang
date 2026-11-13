# Point sources, actual inspected positions, and K2

Date: 2026-11-13. Base: `f22c75e5779bf23cc3116e5201119d55bb1ad3a1`,
branch `astra/point-class`.
Status: **Implementation obstruction and additive defensive repair. Class P
accessibility and the general SourceBudget remain open.**

Authority: spec/06-roles.md §6, especially the 2026-11-08 rejection-priority and
2026-11-12 cycle-position decisions, and the B4 draft through addendum 7.
This continues [Source frontier](2026-11-13-source-frontier.md). No owner decision
is requested: the existing K2 decision already excludes the behavior below.

## 1. What pointness actually buys

Class P is a restriction on the **initial** intervals. It does not require every
later certified observation to use identical endpoint IDs. A refresh may retain
an exact source equality and expose a nominal argument through wider cached
bounds. Its model set is unchanged. The actual argument still has its original
shared identity.

This distinction defeats the proposed shortcut from point initial sources to
point-only inspection reports. More seriously, the current K2 consumer checks
`report.inspected` lower endpoint IDs, although `report.tests` retains the actual
origins at those positions. An actual cyclic argument can have acyclic bounds.
The shared-provenance repair correctly retains that argument; K2 then reads the
wrong representation of the inspected position.

The finite frontier proof from the previous note is still correct for its
certified direct walks. Extracting such a safe walk from the current enabled
inspection is the failing bridge. This is not a failure of the pigeonhole
argument or a need to choose an interval center.

## 2. A checked point source

Let `V a` be the structural variant `:{tick a}` and `N a` the nominal `list a`.
There is one unary role P and one implementation:

```
P(N(V a)) requires P(N a).
```

There are no associated equations, named demands, or output-only binders in this
example. Head size is three, child size two, and a occurs once in each. After
every finite normalized pattern substitution, the head still has the additional
V constructor. The existing `DeclarationChecked`, including `StableSmaller`, is
proved for this declaration; it is not merely assumed Paterson admissible.

Use these seven source IDs:

| ID | Ordinary equation / nominal observation initially |
| --- | --- |
| 0 | `x = y`; its observation is still unknown |
| 1 | `y = N μ`, nominal parameter `(2,2)` |
| 2 | `μ = V μ`, with its structural self-edge recorded |
| 3 | `l = V bottom` |
| 4 | `u = V top` |
| 5 | `bottom` |
| 6 | `top` |

The root is occurrence 7 with demand `P(0,0)`. The initial source has no listed
strict intervals and its only nominal type parameter is `(2,2)`. All unnamed
root inputs are literal point pairs. `initial_point` quantifies all three
collections, not just the root. `initial_source` proves the actual existing
InitialSource predicate, including metadata, linkage and the seed bound.
The regular full-carrier solution of `μ ≈ V μ` supplies an inhabited model.

Now refresh x to the descriptor `N[(l,u)]`, keeping y's point descriptor and all
ordinary equations. This is legal: for every model of the source,

```
V bottom ≤ V μ ≈ μ ≤ V top,
x ≈ y ≈ N μ.
```

Consequently the new descriptor holds in every old model. `refinement` and
`certificate` prove the actual refresh premises, and `refresh_step` is an actual
SharedSteps.Step. It is also an administrative Step of the added relation.
This establishes source reachability of the refreshed carrier, rather than
assuming a favorable intermediate state.

## 3. Exact inspection and the missed rejection

For the sole candidate at the refreshed root, the old recursive report is:

```
inspected = [(0,0), (3,4)]
capture a = ((5,6), structural(nominal(source 0,N,0),V,0))
tests     = [(nominal(source 0,N,0), V)]
```

The inherited report additionally records the root nominal test at `source 0`.
These lists are computed from the existing inspection functions in Lean.
The report is Finished. Neither inspected lower slot is 2.

The actual position tested by V is `nominal(source 0,N,0)`. Source aliasing to y
and y's point parameter prove that **every** observation at this origin is
equivalent to source 2, in every journal model. Source 2 has an inhabited
structural self-cycle. Thus this is exactly an inspected-position K2 rejection
under the owner decision.

It is not enough to say the numeric report omits 2: some other semantic graph
edge could still make 0 or 3 cyclic. `GeneralNominalPointCycleBounds` rules that
out. In the exhibited model, structural edge targets are equivalent to μ,
bottom, or top, and actual nominal edge targets are equivalent to μ. None is
equivalent to `N μ` or `V bottom`. Consequently no journal edge targets 0 or 3;
neither can lie on a cycle. Raw cycles embed into the same journal graph.
`not_rootK2` and `not_candidateK2` prove the **full existing predicates**
false at this refreshed state. They do not by themselves prove Installable.

## 4. Repeating schedule on paper

The following is a mathematical execution schema for the old SharedSteps
relation. The full sequence of install/refresh/merge certificates has **not**
been encoded as an infinite Lean trace. The independently reviewed guard audit
and the kernel-checked source/refresh/K2 prefix are distinguished below.

After n installations and the intervening administrative work, maintain S_n:

1. Occurrences P_0 through P_n are registered; installed packets belong to
   P_0 through P_(n−1), with literal edges P_i → P_(i+1).
2. Every unnamed input denotes `N μ`; every occurrence is aliased to P_0.
3. Every exposed wrapper endpoint has descriptor `N[(l,u)]`. The original
   point descriptor of y and μ's structural self-edge remain available.
4. Each packet's input fact has empty output support. A trusted ledger consists
   of these input facts; there are no associated-output facts needed by a head.

S_0 is the refreshed state above. To extend S_n:

**Prepare P_n.** Its root wrapper is off-cycle. Inspection of V uses the fixed
lower slot l, also off-cycle. For n=0 the root is a literal point and there is
one a-capture. Subsequently compound materialization has two distinct endpoint
IDs, so inspection visits both wrapper descriptions and captures a twice. Both
captures have bounds `[bottom,top]`. Their actual origins denote μ. Hence
capture compatibility and shared actual-origin coherence hold. The repeated
capture lower join is bottom and upper meet is top. The recursive declaration
is the unique visible candidate; its only compound request is `N a`, and all
its variables are captured. Legacy inspection-pending adds no obstruction:
the branch is Prepared. Its older recurrence test also considers observations
bisimilar to a visible cycle, so off-cycle status alone would not suffice.
Here wrapper views are nominal/deferred, and l has an unresolved tail at depth
two, whereas the sole structural cycle μ still has V there. Thus l is not
observationally bisimilar to μ. Newly exposed wrapper slots are also nominal,
so they introduce no further structural cycle. There is no named request that
can fail RequestReady.

**Install.** The compound child request materializes `N a` using actual-mode
substitution at the nominal argument. Thus its two new endpoints both denote
`N μ`, rather than `N bottom` and `N top`. This fact is precisely why shared
provenance does not by itself repair this example. The recorded-origin
cross-constraints give InputCoherence. They also give InputExplanation using
source constraints and earlier Inputs alone; no unfinished output is used.
The ordinary support guard, value-support guard, and shared head guard can
therefore use empty output support. A common model assigns every wrapper
endpoint `N μ`, every merged lower/upper capture key bottom/top, and every unused
reservation bottom. It satisfies all previous packets and the new
branch simultaneously, including Joint. ChoiceCompatible holds because every
choice uses the same declaration. All old sites have already been merged, so
MergesClosed holds.

This model also proves graph safety uniformly at every stage: wrapper values
are the only values with nominal arguments; the structural observations still
give only μ → μ, l → bottom and u → top. Equality transport can identify IDs
within these value classes but cannot create an edge targeting a wrapper or l.

The allocator encodes invocation identity in the child key. Its injectivity and
`source_above_invocation` make the new child occurrence different from every
prior child. The literal edge from P_n to this child is absent. Consequently
Committed is false even if some or all of the semantic constraints are already
entailed: Committed also requires that exact edge. Installable contains no
Representative premise excluding an occurrence aliased to an earlier parent.

**Expose and merge the child.** Extend the finite slot table to represent its
allocated endpoint IDs, retain the previous slots, and refresh their unknown
observations to `N[(l,u)]`. The newly installed Inputs entail these descriptors;
the same inequalities used at S_0 justify the refresh. No strengthening of the
model set is needed. Endpoint equality allows `recover` to expose the child's
actual root origin. Every old and new root denotes `N μ`, so SameInputs and its
empty-output-support MergeGuard hold. Merge the new occurrence with P_0 (and
use alias transitivity for the other sites). This establishes S_(n+1).

Each stage is finite and contains a novel installation. The schema produces
infinitely many literal occurrences and child edges even though there is only
one semantic role/input demand. Administrative accessibility does not exclude
it: every finite administrative segment is separated by an installation.
The output-settlement guard never intervenes, since the rule has no associated
outputs. The demands themselves remain unsettled as their children stay pending.

This identifies a second accounting problem: same-input aliases currently
record sharing without preventing repeated expansion of the alias class.
The finite-signature interface includes literal parents and children, so a
finite set of semantic role/input pairs alone cannot establish SignatureCover.
A future invocation bound must prove sharing of expansion work or account for
these literal identities. This note does not change the existing alias policy.

## 5. Yulang source shape and classification

The small source program is:

```yulang
role P 'a:
    our a.p: () -> int

impl P (list(:{tick 'a})):
    where (list 'a): P
    our xs.p () = 0

my loop(n) = :tick (loop n)
my result = ([loop 0]).p ()
```

The existing parser accepts this syntax. The recursive value has the intended
type equation μ ≈ V μ; the requested role input has shape `N μ`. The auxiliary
bottom/top observations and delayed alias are finite permissible solver-view
data, not added language declarations. No inference-to-this-seven-slot-view
theorem is claimed. In particular, this is not a demonstrated compiler hang.
The formal source predicate used by the requested Acc theorem does permit the
view, as proved above.

Classification: **implementation gap**, not a new semantic gap. The spec already
requires rejecting the inspection of μ. There is no owner question. The paper
schedule explains why proving the proposed universal theorem for the unchanged
relation is the wrong next obligation; the formal result isolates the missed
K2 check without claiming a complete infinite-trace theorem.

## 6. Additive repair and its exact scope

`GeneralNominalActualInspectionSteps` defines a new At/Step and SourceFormed.
Existing definitions and existing Lean lines are unchanged. Administrative and
merge constructors are retained; installation has an additional certificate.

For a prospective inspection, recover inherited input origins using the existing
`FeedbackSites.recover`. This uses already proved endpoint equality, never
overlap, arbitrary endpoint equality across different intervals, or a chosen
center. Run the actual recursive inspector with those origins. Require:

- Every visited constructor position has a retained test origin. The concrete
  certificate compares inspected/test counts; the inspector adds one visit and
  at most one test at each constructor position, and no tests elsewhere.
- Each tested origin has a uniform SameOrigin readback to a listed journal
  source ID (`Located`). Missing representation leaves expansion pending.
- No tested origin is uniformly equivalent to any inhabited cyclic source ID
  (`¬ Cyclic`). Thus choosing an acyclic-looking alternate ID cannot hide a
  known cyclic representative.
- These conditions hold for the selected packet **and every visible HeadReady
  alternative** of the same role, before selection/materialization filtering.
  This retains the owner rule that rejection precedes ambiguity or selection.

These are semantic proof certificates, not a claimed decidable implementation
of their synthesis. A cycle is sufficient to block installation; a full
terminal-frontier classifier reporting K2 rejection is not added here. Without
a certificate the added relation is lazy. It leaves the source equations and
ordinary journal available for constraints, merging and K2.

`point_argument_readback` proves the general point-nominal label readback over
the existing carrier. `nominal_alias_readback` transports it through a journal
alias. `safe_test` excludes an actual cycle at every represented tested
position. `first_round_blocked` applies this to the source-formed witness, with
no old-installability premise or unproved source-reachability premise.

Positive evidence is concrete: Display(list int) and Wrap(list int)'s existing
packets retain the entire new guard, including all visible alternatives.
`display_step` is a real installation under the added Step with the existing
emission unchanged. This is not a proof of their whole-program termination.
The same-input, output-only binder and settled-output checks are still present
because every new Step is an old shared Step (`step_shared`). Previously blocked
old steps stay blocked. Existing Len examples distinguish capturing an opaque
μ under an off-cycle list from inspecting a cyclic root; §6 explicitly permits
the former and rejects the latter. This note does not reverse that distinction.
No new Len or pump completion theorem is claimed.

## 7. Consequence for the requested chain

| Link | Result in this change |
| --- | --- |
| (a) Point label/capture readback | General point-nominal and alias readback proved; the computed candidate actually retains the cyclic origin. Universal point-report extraction is false as a literal-descriptor invariant. |
| (b) Producer over H | This witness uses the same original μ identity throughout. General non-leaf/output-only producer closure remains open. |
| (c) Eliminations vs observations | The proved refresh preserves all models and does not eliminate an initial hole. The paper loop needs no source-hole elimination. |
| (d) Instantiated Paterson/tree bound | Finite-pattern stability is proved for this rule. Applying finite-tree size to the actually inspected μ is invalid; actual-position K2 must intervene. |
| (e) Invocation/cover/Acc | Literal child-edge novelty can survive same-input aliasing. No SourceBudget or unconditional Class P Acc is derived. |

For the repaired relation, the initial frontier, all producer paths,
elimination extraction, finite-tree growth, and literal invocation/report cover
still require proofs. The existing finite-signature reduction remains available
for the old relation, and `accessible_of_shared` transfers any established old
Acc result to the added subrelation. Neither is an unconditional solution of
Class P. Work stops at this implementation obstruction rather than packaging
the missing chain as an assumed source budget.

Strict initial intervals need the same actual-position checks and additionally
the unresolved facet/provenance producer bridges; point initial data already
expose the present bug, so extending to strict sources cannot repair it.

## 8. Validation scope

The yulang-proofs workflow was used. The configured prover launch role was
unavailable; no prover agent ran. The primary constructed the bounded proofs;
a separate read-only reviewer audited the execution schema, actual source
prefix, guard quantification, and claimed scope. The alternative-candidate
condition was added after that review.

The Lean results are the source/refresh/K2 witness, the added relation and its
first-round block, readback lemmas, and positive guard/installation examples.
The infinite schema and the source-language-to-view explanation remain paper
arguments, not kernel-checked execution theorems.

From `lean/`, each final command returned exit code **0**:

```sh
lake build Yulang.GeneralNominalActualInspectionSteps Yulang.GeneralNominalPointCycleSource Yulang.GeneralNominalPointCycleInspection Yulang.GeneralNominalPointCycleBounds Yulang.GeneralNominalActualInspectionExamples
lake build Yulang
lake env lean Audit/GeneralNominalPointClass.lean > /tmp/yulang-point-class-audit.log
```

The audit covers all 63 new public theorems. A parsed allowlist check returned
exit code **0**, with dependency union exactly `propext`, `Classical.choice`,
and `Quot.sound`. The five new modules have appended imports in `Yulang.lean`.
The existing Lean byte-prefix, tracked frozen paths, branch and HEAD checks
returned exit code **0**. `git diff --check` returned exit code **0**.
Development elaboration failures were corrected before these final checks.

The parser check uses the Markdown note's fenced Yulang program; it checks
syntax only. It does not validate inferred types or solver-view production.
From the repository root, this command returned exit code **0**, with one block
accepted and no recovery:

```sh
target/debug/examples/syntax_guide_check notes/design/2026-11-13-point-class-inspected-cycle.md --quiet
```
