# R269-r4 — source need and qualification before canonical coverage

Revision 1. **Candidate source-native evidence; R269 INCOMPLETE.**
Author: `/root/sol_r269_source_need_r4`; no descendants or coauthors.
Contract: `tasks/agent-loop/sprints/slot-family-lineage-cover-r269-r4.md`,
SHA-256 `a5f3bd1f3bc701ce75191ec234b72264d0dd9e73d7dfd31b88f0b8da0c6009ec`.
Baseline supplied by Luna: `8d646ac2ed171e13a529e25e035fc75f91678b0b`.
Independent review: pending; this producer does not certify the result.

## 1. Original source requirement and unchanged parent

The application edge remains inference soundness → R70 copy correspondence →
`R71-RAW-CANONICAL-FIBER-COVERAGE-1`. Full accepted source domain, original
parent quantifiers, Simple-sub A/B, independent satisfying assignments, shared
witnesses, F1/FK1 and foreign continuations remain unchanged. Parent/A/B delta:
**0→0**. No stronger or weaker replacement parent theorem is introduced.

The original approved clauses, read before the producer results, require:

1. Construct and retain source constraints, including all contributing branches;
   perform ordinary constraint accumulation/propagation and level-based copying
   (top-level principles §1.1).
2. For each actual extrusion occurrence, retain its origin and receiving Values
   and its actual produced polar type parent/copy pairs. Fresh use alone creates
   no extrusion occurrence (value-association decision, approved qualification).
3. Compare those Values in the approved source Value-reference SCC graph. When
   they share a component, equate the occurrence's actual retained type pairs;
   preserve added constraints and propagate equality through actual consumers
   (top-level principles §1.1(3), parent-copy selected operation).
4. Determine adjacency from actual source Name references. Parent metadata,
   comparison direction and type-copy row identity do not establish adjacency.
   The parent-copy decision's definition-root section explicitly says lexical
   nesting/inference levels do not filter or rank Value-reference edges.

The quantification in these operational clauses is over **actual source
occurrences and actual produced pairs**, and over the corresponding actual
consumers. The clauses supply neither a permanent type-row Value owner nor an
additional universal quantifier requiring every canonical-bucket RelationId as
a separate copy parent. The association decision's final paragraph explicitly
declines an additional arbitrary pre-intrusion assignment/client-fiber theorem
without an independently established source contract. This observation does
not retire R71, weaken its original quantifiers, or establish that a particular
canonical fiber is dispensable: a fiber may carry indispensable evidence for
one of the actual source obligations.

Here `Need_D(Ω,j,s,c)` remains the **unproved judgment** that the unchanged
source requirement for an independently justified derivation D requires the
specific canonical candidate c at actual occurrence Ω, Parent index j and slot
s. No definition of that judgment is asserted as a theorem or imported as an
interface. In particular, bucket membership, successful helper execution and
the desired cover conclusion cannot establish it. A constructor-to-source
evidence interpretation must justify a named instance before INC268 can apply.

## 2. A source-constructor qualification boundary

During the permitted Stage-2 source trace, the following distinction appeared
before an authentic earlier-equality/later-copy history was established.
Luna directed the lane to retain it as a source-need input observation and then
freeze its equations. It is neither a completed accepted-source counterexample
nor an adjudicated approved-clause violation.

Let λ(v) be `Graph.planning_levels[v]` after a successful `seal`. The raw
adjacency is `Graph.edges`; source constructors populate it independently of
solver rows. `seal` (`candidate_value_graph.rs:354–393`) validates complete
levels and helper-entry level preservation. Its forward DFS follows an edge
v→w only if λ(v)=λ(w), at line 376. Its reverse component DFS has the same
guard, at line 389. `qualifies(e)` at lines 395–397 compares those stored
component labels for the event's actual origin and receiver.

Consequently, for a successful seal:

```text
component_native(v) = component_native(w)  ==>  λ(v) = λ(w).     (LEVEL269)
λ(origin(e)) != λ(receiver(e))            ==>  !qualifies(e).
```

Proof of the first implication: each reverse traversal starts at one root and
only pushes an adjacent vertex of equal λ. Induction on pushes gives equal λ
for every vertex assigned that root label. Each root label is its own unique
vertex ordinal, so two equal component labels arose in the same traversal.
The second implication follows from the comparison in `qualifies`. This is a
bounded source-body argument, pending independent review; no checker or test
was run.

Cross-level raw references remain present: `seal`'s own comment distinguishes
raw Ref from the helper-entry guard. Collection invokes this seal at
`lib.rs:1551`; session construction invokes it again at `lib.rs:10466`.
Thus the inspected partition is consumed by actual qualification, rather than
being merely an unused observation. This does **not** by itself demonstrate
an accepted-source cross-level SCC or a selected qualifying Parent.

## 3. Concrete source shape and exact conditional construction equations

Use the existing source spelling in `candidate_source.rs:2530` only as a
construction input candidate:

```text
my outer = {
  my loop x = {
    my direct = loop x;
    my helper y = loop y;
    helper x
  };
  loop
}
```

The enclosing unexecuted test checks recursive action planning and successful
rebuild. Neither that assertion nor the spelling authenticates a reached
R71 consumer. No test was run, and no parser path outside the whitelist was
opened. The following equations concern the **successfully retained LocalSource
shape** with these resolved local Names and nested bindings. Authentication of
that premise and an actual successful native prefix remains open here.

Write L, D, H for the semantic `Value::Local` vertices for loop, direct and
helper; use aD, aH, aL for the three Apply occurrences in their respective
initializers/bodies. These are HIR/source identities, not solver row IDs.

`emit_candidate_source` starts the module body at level 1 (line 1208).
A Block/StatementBlock visits local initializers at its own level plus one
(lines 1355–1380). Lambda body visitation preserves the current level
(line 1349). Each Initializer records its binding's immutable birth at that
initializer level (lines 1546–1557); `Graph.record_level` rejects a conflicting
record rather than replacing the birth (lines 75–87). Therefore:

```text
λ(outer) = 1;     λ(L) = 2;     λ(D) = 3;     λ(H) = 3.       (BIRTH269)
```

`Graph.retain_source` switches owner at each nested initializer (lines
230–253), while Lambda/body traversal retains the owner (lines 221–228).
A resolved Name adds owner→resolved-local incidence (lines 137–141).
The Apply association uses `owners[index]` and the resolved callee Value
(lines 329–344), with the exact checking identity `(Apply occurrence,0)`.
Thus the three conditional constructor instances are:

| Apply | Actual source owner | Resolved callee | Event endpoints | Native qualification |
|---|---|---|---|---|
| aD = loop x in direct | D | L | eD = (D,L) | false, since 3 ≠ 2 |
| aH = loop y in helper | H | L | eH = (H,L) | false, since 3 ≠ 2 |
| aL = helper x in loop | L | H | eL = (L,H) | false, since 2 ≠ 3 |

In the raw definition-root graph, aL's Name gives L→H and aH's Name gives
H→L. Hence this conditional source shape has the raw ownership cycle
L→H→L; D→L is additional raw incidence. No body endpoint, Apply result or
Lambda row is identified with these local roots. LEVEL269 yields the table's
native qualification results without assuming anything about extra helper
paths: distinct levels prevent a common native component regardless of them.

This is a discriminating **conditional source-construction trace**. It does
not establish the accepted-source history demanded by R269, a semantic
contradiction, or absence of every equality/copy route. In particular, it does
not promote an unexecuted fixture into a source-qualified R71 falsifier.

## 4. Why this does not yet select a Parent or canonical candidate

The actual source spine retains these distinct objects:

```text
Apply a / checking(a,0) / event e / source call index i
  → retained Apply recipe and Action::Candidate
  → native callee and negative Function demand U
  → source-seeded relation and its actual later processing ancestry
  → reached production extrusion Ω
  → actual Parent append j and visit-time selected slot s
  → named r:k → c:C(k), then the later selected raw copy and consumer.
```

`candidate_source.rs:1869–1924,2492` retains/executes the recipe.
`shadow_apply.rs:4302–4399` builds the demand and its registration before
admitting the actual callee/demand pair. `candidate_context_seed:3793–3838`
uses the exact checking event; an Apply seed with a matched event has singleton
source set `{e}`. A scoped demand additionally needs its actual introduction;
it is not supplied by the event alone.

Source action planning preserves recursive-link identity: an active recursive
Name emits `Action::Link` with the active initializer endpoint
(`candidate_source.rs:1795–1802`); execution admits a constraint at slot 30
(`:2482–2486`). It does not equate the Name row with that initializer. The
candidate spelling's planning test at `:2541–2581` asserts two recursive Links
before loop installation and one fresh Local use afterwards; those assertions
were inspected, not executed. No equality or stale-row slot is obtained by
silently replacing a Link with row identity.

At a reached production branch, `lib.rs:14814–14843` calls extrusion with the
actual nonrow endpoint/sign and the opposite row's actual level. At each
deep-row Visit, `candidate_extrusion.rs:110–180` retains a Parent before
scheduling every selected physical slot. For Parent j:

```text
Parent[j].sources = S(actual processing relation);
pending-at-creation(j)
  iff exists e' in S(actual processing relation), qualifies(e').  (PARENT269)
```

This is read directly from `retain_extrusion_parent:305–365`. The comparison
field is the actual processing TypedPairKey; it is not the processing
RelationId or physical-slot identity. Transformed-output recapture has its
own group/source set and the same existential qualification test
(`candidate_intrusion.rs:390–421`).

**Important remaining premise:** a table entry `!qualifies(eD/eH/eL)` does not
by itself prove that an arbitrary selected Parent is unqualified, that its
processing source set is singleton, or that no earlier merge occurs. Replay
unions its actual parents' sources; FreshUse, recapture and other actual
history paths must be traced at their real identities. This packet has not
authenticated the complete source inventory, all processing ancestry, or the
selected Parent instance, so no global absence claim follows.

The first unresolved input for this candidate route is:

```text
independently accepted/resolved source derivation D
  → authenticated native prefix with a named processing relation,
     its complete S, actual reached Ω/Parent j/slot s,
     earlier EqualityCanonicalization r:k → c:C(k),
     and independent source necessity Need_D(Ω,j,s,c).          (AUTH269)
```

The raw ownership cycle cannot discharge AUTH269: it supplies neither the
native qualification predicate in PARENT269 nor a concrete Parent, slot or c.
Conversely, LEVEL269 does not refute AUTH269 for the full source domain.
Owners of its first seams are `emit_candidate_source` / authentic HIR
LocalSource retention, `Graph::retain_source` / `seal` / `qualifies`, the
source action driver, `retain_extrusion_parent` / recapture, and the unchanged
R70/R71 source-to-copy evidence interpretation. No independent Need instance
for a specific c was established.

## 5. Equality/copy square and parent application

Once AUTH269 and the need judgment are proved for an actual history, the
retained native owners provide the two different legs:

- `candidate_context_canonicalize_bounds:4649–4669` transports the actual r
  from k to C(k) with EqualityCanonicalization, preserving its original
  attachment and retaining the equality-derived dependency.
- `Work::Bound:399–417` later uses the selected physical slot's saved raw k,
  while the child Visit uses its canonical endpoint. The transfer loop
  `candidate_transfer_bound_origins:1045–1058` enumerates exactly the captured
  raw prefix and transports each actual parent with its own witness.
- `candidate_context_transport_witness_with_evidence:4737–4751` samples the
  antecedent snapshot, actual post-check context, source set and transported
  scoped flow, then retains dependency, FiberTransform and attachment.
- `candidate_context_begin_replay:4411–4497` preserves the ordered actual
  lower/upper parents and keys, source union and composed scoped transformer;
  the upper supplies the demand and the lower must have no demand. Equal
  endpoints cannot replace these actual opposite inputs.

These equations do not prove a witnessed commuting square or all relevant
slot/history coverage. Need must precede any attempted substitution of r's
copy continuation for c's equality-bearing continuation. As AUTH269 remains
open, no such substitution or universal cover is asserted here.

R268's INC268 is therefore still inapplicable at unchanged R71. R70's exact
raw-prefix transport remains reusable under its successful stable local
envelope; R267-r6's reviewed selected exact Function-slot case remains usable
only under its actual slot premise. Neither supplies direct-row ancestry,
canonical necessity or source reachability. The new result locates a concrete
qualification-authentication obstruction for the candidate source input, not
a discharged parent edge.

ENTRY-WF, drain/eventual Diagnostics, Q262-EPISODE, permitted history/rollback,
Effect TEMP265/Z265 temporal simulation, diagnostic adequacy, helper coverage,
full soundness, A/B, F1/FK1 and foreign continuations remain OPEN.
`NO_SAFE_CODE_SLICE` remains the existing disposition: no fully authenticated
approved-clause violation or production repair was demonstrated.

## 6. Mutual TODOs, provenance and freeze boundary

`R269-QUALIFICATION-AUTHENTICATION-1` to Luna, same parent: authenticate the
specific source/HIR shape and its complete source inventory, then derive its
actual processing source set and selected Parent history. Preserve raw Ref,
native sealed partition and Parent qualification as three separate facts.
The discriminating evidence is the actual checking/event/Value-level tuple,
native component result, complete processing ancestry and selected Parent,
rather than another presumed SCC graph. A separate authority question about
partition correspondence requires Luna's adjudication; this result grants no
new semantics, reads, code edits or tests.

`R269-SOURCE-NEED-CARRIER-1` to Luna, same parent: from the unchanged source
typing/occurrence requirement, justify the exact c-bearing obligation for an
authenticated `(D,Ω,j,s,r,k,c,C(k))` before proving the square. The falsifier
of a proposed square is loss of the required equality/scoped/source evidence
or disagreement at an actual ordered opposite-input consumer, after complete
competing slot/history accounting. Neither an empty raw bucket nor differing
ContextIds alone is that falsifier. A source-qualified R71 refutation still
requires a fully accepted reached consumer and complete competing paths.

Prior work reused only within reviewed limits: R70 by
`/root/r70_ordinary_extrusion_proof` with `/root/r70_extrusion_countertrace`;
R71 by `/root/r71_raw_canonical_proof`; R267-r6 by
`/root/sol_r267_source_input_join`; R268 by
`/root/sol_r268_source_occurrence_incidence`. R268's approved-owner audit was
reused, not rerun or certified by this author. No R261/R262 theorem, R255
theory, R230 record, quarantined R263/R264/R266 output or R269-r2 was read or
assumed. Historical source-shaped sketches were not accepted as reached paths.

Read authority and dependency bytes are exactly the R269-r4 direct manifest,
R268/R267-r6 inherited direct manifests and 36-entry R255 manifest. Initial
`sha256sum -c` gates matched every extracted direct pin and all 36/36 R255
entries before source bodies; only the fourteen authorized source paths were
eligible, with targeted reads in the owners cited above. Operational output
truncation was repaired by rereading the omitted agent and Git rules. Some
large historical proof output was truncated; no exhaustive reading or all-case
proof of that material is claimed. Final pins and artifact hash are recorded
in the frozen handoff/terminal receipt.

Requested registered prover, Sol/high; current assignment records
`gpt-6-sol/high`, configured default `gpt-6.1-sol/high`; observed effective
model/effort UNKNOWN. Exact runtime identity matched before Luna GO in session
`01a1873a-a93b-7dc3-a8ce-028a7b543a80`. Maximum 1,200 seconds, no reset or
extension; full grant charged, exact active seconds/CPU/RSS UNKNOWN. Observed
clock cuts: 12:15:07, 12:17:32 and 12:18:49 UTC on 2026-11-02.

No Lean theorem types or axiom audit apply: this is non-Lean source-native
work, with no checker run. No tests, builds, probes, Cargo, Git, production or
expectation edits, descendants, scratch/cache outputs, nested CLI or external
contact. Only this theory and the single leased R269-r4 inbox are new paths.
Luna directed freeze of this concrete state; after final pins and the handoff
hash this writer stops all reads and writes. Review, status synchronization
and integration belong to Luna; no worker is claimed to remain running.
