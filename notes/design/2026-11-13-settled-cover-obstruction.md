# Settled-cover obstruction: repeated nonpoint captures lose sharing

Status: **Draft paper counterexecution; bounded Lean checks listed below.**
Date: 2026-11-13. Integration base: `70461874b`, branch `astra/settled-cover`.
Scope: the unchanged `GeneralNominalSettledSteps.Step` and its general interval
carrier. No new guard or declaration rule is proposed as an implemented change.

Authority: [spec §6](../../spec/06-roles.md), especially associated determination,
same-source input sharing, centerless intervals, K2, and the settled-output
decision; [B4 draft addendum 7](2026-11-08-b4-main-statement-draft.md).
This revisits the four open bridges in
[the settled-output note, §5](2026-11-13-unsettled-output-deferral.md).

## 1. The source-refinement argument fails at readback

The proposed induction would eliminate every settled output into a finite term
over shared input leaves. The present carrier does not provide that elimination.
For a top-level variable query, the recursive report starts with `origin=none`.
Its capture retains an interval, but no relation to a shared actual input.
For an actual-mode occurrence of such a head variable, `VariableHolds` requires
only that its value fits the captured interval. Output materialization relates
repeated uses of that variable **within one packet**, but does not relate the
choices made by different packets. Settlement does not add that missing relation.

Thus a settled leaf can introduce an independently varying interior value, not
an expression determined by its input endpoints. This is not the old use of an
unfinished output: the producer below has no where-children. The source's finite
leaf set is not preserved under the actual output semantics. A proof of the
source-refinement bound cannot start by assuming that preservation.

## 2. Two-role example

Write V(t) for the structural variant type `:{tick t}`. It is covariant;
**do not replace it with invariant nominal list**. In the general carrier the
strict interval B = [V never, V any] contains V t for every t, including every
positive finite V tower. Its two endpoints are different in every model below.

The following is specification-spelling Yulang. Named associated equations use
the same spelling as the governing role examples. It describes the declarations
and a triggering family; no frontend-to-InitialSource theorem is available.

```yulang
role P 'a 'b:
    our a.pump: 'b -> int

role W 'a 'b:
    type anchor
    type out
    type tail

impl W (:{tick 'a}) 'b:
    type anchor = 'a
    type out = :{tick 'b}
    type tail = 'b

impl P (:{tick :{tick 'a}}) 'b:
    where (:{tick 'a}): W('b, anchor = 'z, out = 'z, tail = 'u)
    where (:{tick 'a}): P('b)
    our x.pump y = 0

my trigger(x: 'a, b: :{tick 't}) = (:tick (:tick x)).pump b
```

The precise inference input used in the argument is
`P((V² A0,V² A0), B)`, with A0 unknown and B the strict interval above.
The triggering annotation illustrates why a known variant head can coexist
with an unknown payload. It is **not** a claim that the current frontend emits
exactly this endpoint representation. The counterexecution concerns the
explicit `InitialSource` contract quantified by `SourceBudget`.

The formal registry has two declarations. P's head is `[V² a,b]`; both child
input lists are `[V a,b]`, a strict decrease by one constructor under every
capture, with the same variable multiplicities. W has no children. P's z and u
are output-only binders: z is produced by W.anchor and reused for W.out; u is
produced by W.tail. Neither appears in an unnamed child argument. Repeated
output uses are not repeated declaration IDs or associated names.

There are no nominal declarations, nominal bodies, recursive source types,
unsettled producer outputs, or growing declaration-side input templates in
this example. The two-role version avoids a separate Extract declaration:
W's own anchor equation supplies the input/output connection after W settles.

## 3. Round construction

At round n the next P request has input `(V² A_n,B)`. Installing it emits

```text
W_n = W(V A_n, B, anchor=z_n, out=z_n, tail=u_n)
P_(n+1) = P(V A_n, B).
```

P's input materialization gives both endpoints of each compound first input the
value V A_n. Its b capture keeps the strict interval B. The emitter therefore
retains no point origin for b, including when that interval is passed unchanged.

W_n selects its unique leaf implementation. Its a capture is point and gives
`z_n = A_n`. Its b capture has no actual origin. Its out and tail equations give

```text
z_n = V u_n,       V never ≤ u_n ≤ V any.
```

All repeated b occurrences in this W packet share u_n, as required by
`GeneralNominalMaterialization.Models`. There is no equation `u_n=u_m` for
different W packets. W_n immediately settles. P's output equations are not
used in this explanation: its shared output-only requests already name the
same z_n target, and the two equalities above are W_n's own associated equations.

Refresh z_n/A_n and the materialized compound inputs using the full journal.
The named tail u_n supplies an existing reserved identity for the payload.
Consequently P_(n+1)'s first input is V² u_n. Put A_(n+1)=u_n and repeat.
Every round has two novel installations and finitely many observation updates.

## 4. Models, guards, cycles, and merging

For a prefix through W_(h−1), choose finite values

```text
A_i = V^(h-i+1) int                 (0 ≤ i ≤ h)
z_i = A_i,  u_i = A_(i+1)           (0 ≤ i < h).
```

Every A_(i+1) is a positive V tower, so it lies in B. Assign compound first-input
endpoints their displayed values; assign each b lower/upper pair V never and
V any; merged captures of duplicate point observations have the same value.
The ordinary allocation equations, projection interval checks, and actual-mode
schema equations all hold. Source and emitted identities are assigned using the
existing injective allocator, so different reservations do not collide.

For clarity, the initial finite source graph can use

```text
0 = V 1; 1 = V 2; 2 = A0 unknown;
3 = V 4; 4 = never; 5 = V 6; 6 = any;
root P = ((0,0),(3,5)).
```

Ordinary equations record these expressions; the checked normalized view exposes
V at 0,1,3,5. The leaves at 4 and 6 need no ready head. Additional unused unknown
slots are harmless. Intervals satisfy lower≤upper, metadata is fixed, all source
IDs are below the seed, and the initial journal and allocation set are empty.

Each transition obligation has a finite construction:

| Obligation | Reason for this schedule |
|---|---|
| Root readiness | Both first-input endpoints have the required V heads; B's lower endpoint is source-known V never. Variable heads do not inspect B's payload. |
| Candidate selection | Exactly one visible declaration per role; its finite query finishes. The displayed model supplies private consistency and the joint witness. |
| Exact readback | P's inspected V observations follow from the source, previous P input materializations, and previous settled W outputs. W reads only the first V position. Its b query has no reads. No unfinished P output is promoted to a trusted input fact. |
| New support | Add the P input fact after its exact readback, then W's input fact after its exact readback. W is a leaf, so its exact output packet is settled and its output fact can be added to `Trusted`. These explain the next P input heads. |
| Old value guard | Supports consist only of earlier W packets, all discharged. Hence the old support and value-grounding conditions hold; no provisional grounding derivation is needed. Input facts retain the corresponding installation supports. |
| Full-journal K2 | In the displayed finite model every structural edge, including edges transported by journal equality, decreases finite V depth. V never, V any, and V^k int are distinguished by the carrier's finite probes. There is no nominal-argument edge. A finite graph cycle would contradict strict depth decrease. The same argument covers raw and journal K2, roots and inspected positions. |
| Same-input merges | Each occurrence has a b input with missing actual origin and strictly unequal endpoints. Recovery cannot turn it into a point. Therefore the current `SameInputs` relation cannot merge these sites. In addition, the first inputs of different W rounds are different finite towers in the separating model, so adding an equal-interval merge rule alone would not repair this two-role example. |
| Freshness and commitment | Canonical invocation/clause allocation gives fresh child and output IDs. P adds a child edge. Before each W installation its new u_n remains independent of A_n; a separating model shows that W's output constraints are not committed. |
| Observation progress | Only already reserved IDs are added as slots. Each needed new V head is a full-journal consequence; old observations are preserved. Omit an observation step if its head is already recorded. |

This defines the schedule by induction, using the same source at every horizon.
The model for a longer horizon can refine A0 to a taller finite tower; the
ordinary source does not bound that height. No single infinite semantic type
or limit state is used. The source graph gets an ever longer finite chain of
new independently varying interior values; no finite stage contains a cycle.
Concatenating the finite rounds gives an infinite guarded trace on paper.

The displayed declarations, finite source model family, and local schema
phenomenon are suitable for small Lean checks. A complete Lean induction of all
`Installable`/refresh transitions is a separate statement and is not silently
supplied by a finite-prefix model lemma.

## 5. Classification and repair boundary

This is an **implementation gap in the general interval/source bridge**, not a
new permission to use unsettled outputs. The authoritative semantics keeps a
shared actual argument when the same source variable is reused and says that
associated equations are determined by the head. The current capture/schema
interface only enforces interval fit independently in each packet. Its
`DeclarationChecked` determination theorem requires agreement of actual captures;
the execution has not established that agreement for the repeated b input.

Preserving the identity of b would force all these uses of b to share one actual
input relation. Then W gives A_n=V b; the next W would require b=V b, a K2 cycle,
and the pump stops. Do not implement this by equating all overlapping intervals,
or all unrelated intervals that happen to have equal endpoints: that is expressly
not the same-input rule. The repair belongs in retention and substitution of
actual input provenance through nonpoint variable captures and associated
materialization. Until that bridge exists, the lazy implementation option is to
leave output-based expansion pending when its head-variable substitution has no
shared provenance certificate. No declaration-time rejection is needed.

No semantic owner question is raised: the diagnosed loss of shared identity
already conflicts with the stated carrier/source contract. No guard repair is
made in this task. Under the current Step, the paper counterexecution prevents
constructing `SourceBudget` and unconditional Acc by the proposed four bridges.
In particular, merely proving a bound on individual finite dictionary trees
would not fix it: every W tree here has exactly one node.

## 6. Four bridges and the failed measure

| Bridge from the previous note | Outcome on this carrier |
|---|---|
| Settled readback | A finite dictionary tree alone is insufficient. W is a leaf, but its output uses a fresh actual-mode value fitting B. Readback must retain the shared substitution, not just the input endpoints. |
| Source refinement budget | The source hole A0 can be refined to an arbitrarily long chain A0=V A1, A1=V A2, …; the extra leaves are independently chosen interval interiors. Paterson bounds each fixed-input dictionary, while K2 excludes a finite cycle; neither bounds this evolving acyclic chain. |
| Invocation sharing | The emitted b interval has no actual origin. The current same-input relation cannot recover that missing sharing from strict endpoints. |
| Finite report enumeration | Finite declarations and finite query shapes do not bound reports with fresh captured identities. A finite source refinement bound would still be needed. |

The existing missing-signature measure remains a correct **conditional** measure:
it counts cover entries whose packet facts or child edges are not yet entailed.
No finite cover is constructed here. An infinite family of semantic values by
itself would not refute that cover; the claimed obstruction uses the operational
round construction in §3–4 as well as the finite-prefix model family. Conversely,
accessibility alone would not produce a uniform finite cover without a suitable
finite-branching argument modulo signatures.

## 7. Formal scope and checks

The four new modules use the existing general carriers without changing Step:

- `GeneralNominalSettledIntervalDeclarations`: actual `Checked registry`,
  checked P/W declarations, output-only target sharing, and the recursive
  substitution identity.
- `GeneralNominalSettledIntervalSource`: a finite `InitialSource`, initial
  `SourceFormed` under the settled relation, and source/initial models for
  arbitrary full-carrier A0.
- `GeneralNominalSettledIntervalOutputs`: exact recursive report and generated
  named schema for a W request, exact packet captures, and its materialized
  output models.
- `GeneralNominalSettledIntervalObstruction`: the full `packet.Holds` branch
  family, empty child list, separation of finite variant towers, and
  `fixed_inputs_unbounded_tails`: for a fixed first input and fixed second-input
  endpoints, this one W packet has models with arbitrarily many pairwise
  inequivalent positive-tower tails. `finite_horizon` proves the recurrence and
  interval membership used in §4.

The local W request deliberately gives anchor and out separate source targets;
it isolates the lost sharing even before the P emission ties those targets.
It is not asserted to be the exact W occurrence generated by P. Its branch-model
theorem is not an `Installable`, `PacketSettled`, or `Step` theorem. The actual
P emitter's equal anchor/out targets are checked separately by `shared_anchor`.

The source-program-to-InitialSource producer, the complete finite-prefix journal
model construction with allocation, and a kernel-checked infinite Step trace
remain unproved. No new `SignatureCover`, `SourceBudget`, or Acc theorem is
claimed. The formal evidence checks the local semantic obstruction; the complete
counterexecution and its guard construction remain the paper argument above.

The configured prover role is unavailable in this environment. The primary
constructed these bounded derivations and obtained a separate review; no prover
agent ran. The skill's referenced older policy files are absent; the current
`rules/INDEX.md` and workflow/compiler/testing rules govern this checkout.

Independent read-only review found no blocking defect in the paper schedule or
formal scope. It separately checked exact readback, joint applicability, fresh
allocation, noncommitment, the two guards, and K2; it did not independently rerun
the build.

Final validation (all three Lean commands ran with cwd `lean/`):

```text
lake build Yulang.GeneralNominalSettledIntervalDeclarations Yulang.GeneralNominalSettledIntervalSource Yulang.GeneralNominalSettledIntervalOutputs Yulang.GeneralNominalSettledIntervalObstruction
exit 0 — 656 jobs

lake build Yulang
exit 0 — 2054 jobs

lake env lean Audit/GeneralNominalSettledCover.lean
exit 0 — 27 public theorems; dependencies only propext, Classical.choice, Quot.sound
```

Repository checks, from the root:

```text
python3 /tmp/yulang-settled-cover-scope.py
exit 0 — unchanged HEAD/branch, existing Lean bytes preserved, four appended imports,
         exact new-file set, forbidden-proof-token scan, all 27 public audit entries

git diff --check
exit 0
```

Intermediate focused builds of `Yulang.GeneralNominalSettledIntervalSource`,
`Yulang.GeneralNominalSettledIntervalOutputs`, and
`Yulang.GeneralNominalSettledIntervalObstruction` returned exit 1 while the new
proof scripts were being corrected. The final commands above passed on the
resulting files. The surface example was not parser-checked; no frontend inference
or runtime test is claimed. No existing Lean definition, guard, spec, frozen
file, commit, or ref was changed.


