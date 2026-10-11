# Apply Name incidence: construction and transport audit

Status: frozen, unreviewed research-only static characterization; parent gates OPEN
Baseline: `a18d70f209a7145ebe27ba646ff8dc7e8663c28f`, `research/simple-sub-intrusion`
Lease: this file only; leaf, no delegation, no compiler/test changes
Method/budget: one static source audit, 30-minute ceiling; no executable probes

## Objective and governing premises

Audit whether the selected Apply Name edge is jointly retained through original
result construction, polar extrusion, one fresh use, and SCC consumption. Stop
at the first concrete divergence, rather than repeat the generic transport
lemma in the frozen incidence note.

Authority is the committed approved answer
`questions/2026-10-12-apply-result-value-reference-owner/approved-answer.md`,
**Proposed decision and authorized scope**, and the pinned parent-copy decision,
**Selected operation and compiler responsibility**, **Value-reference SCC
clarification**, **Retained boundary**; top-level inference principles §§1–5
and **Evaluation**. The approved answer selects:

> Every resolved Name in an Apply source fragment contributes an edge from its
> result Value row to the actual binder Value row, before and after Call dispatch.

This is source-computation incidence. In particular, `konst 1` requires
`R → K`, even when `konst` returns literal `0`. Neither returned-provider
identity nor a Function port supplies that edge. Comparisons, bound storage,
levels, and parent metadata are not edge authorities.

Dependencies: frozen
`notes/theory/2026-10-11-value-reference-incidence-construction.md`, especially
§§3–4 and 6, and
`notes/theory/2026-10-12-odd-even-parent-copy-scc-derivation.md`, §§2, 4–5.
Their earlier unresolved Apply-result meaning is now decided by A. Their
conditional copy/frame premises and all-source theorem are not discharged by
that decision. This audit does not choose fresh provider roots as substitutes
for actual binder targets.

## Original coordinates are available; the edge is not installed

The relevant authentic source coordinates survive collection:

| Owner | Retained coordinates | Source locator |
| --- | --- | --- |
| HIR Apply | occurrence, scope, separate callee and argument indices | `local_source.rs:100–125,529–581` |
| Apply recipe | those operand endpoints, result component, source expression, checking/cause, native interface | `candidate_source.rs:394–411`; `candidate_call.rs:31–62` |
| Formal callee Name | resolved parameter ID, formal registration, actual parameter recipe/root; its endpoint aliases that formal row | `candidate_source.rs:187–217,235–245,543–558` |
| Module callee Name | occurrence, target definition/root component, separate use component | `candidate_source.rs:375–378`; `lib.rs:1273–1325` |
| Local callee Name | resolved local ID and forming initializer endpoint, or published local root and that use's route | `candidate_source.rs:300–305,381–385`; `candidate_scheme.rs:1316–1335,1362–1385` |

`candidate_call::observe` reopens the same HIR LocalSource, validates the Apply
and operand identities, and validates all four native demand ports
(`candidate_call.rs:282–374`). These records provide the join needed for a
direct original Apply/Name/binder incidence; they do not make it an SCC edge.
Module/local occurrence facades and fresh provider roots remain distinct from
the resolved binder coordinate. Aliased parameter/local roots need no invented
injective binder-to-row map.

The first missing implementation step is original edge installation:
`Finish(Apply)` retains a recipe and schedules `Action::Candidate`; that action
calls `admit_candidate_fact` (`candidate_source.rs:394–411,660–684`). Admission
constructs `callee <: Function⁻(argument, argument_effect, invocation_effect,
result)` and retains the native interface (`shadow_apply.rs:1308–1400`). No
Apply/Name/binder incidence is passed to the intrusion state. Its state and
consumer instead retain parents and obtain adjacency from bounds and structural
ports (`candidate_intrusion.rs:10–28,358–468`). This is an installation and
consumer correspondence gap, not an information-loss or representation
impossibility theorem.

## Smallest discriminator and its explicit hypotheses

Use the source shape `my invoke f = f 1`. Its sole Apply-fragment Name is `f`.
Let `F` be the actual formal row, `A` the integer expression row, `R` the
distinct Apply result row, and `D` its negative four-port demand.

Hypotheses: the expected recovery-free LocalSource has successfully formed;
checked allocation and normal source actions succeed; there are no annotations,
foreign Value constraints, intervening equalities, or prior bounds on `F` or
`R`; these source endpoints and demand ports have the same traversal level.
Consider the cut after the Apply Value admission and before the enclosing
Lambda introduction. These are bounded operational guards, not a recorded run
or a claim that every source history succeeds.

1. Parameter Name realization gives `F`; it introduces no Value constraint
   for that Name (`candidate_source.rs:209–216,375–390`). Literal introduction
   constrains `A` to Integer and does not mention `F` or `R` (`:336–350`).
2. Apply admission gives `F <: D`, where the Value ports of `D` are `A` and
   `R`. The callee `F` is retained outside `D` (`shadow_apply.rs:1331–1383`).
3. Same-level extrusion shares the ports (`candidate_extrusion.rs:73–94`).
   Variable/structure admission inserts `D` in `U(F)`; opposite-bound replay
   has no lower `F` bound to consume (`:768–841`). Thus `R`'s Value bounds
   remain empty at this cut.
4. The actual consumer's adjacency recipe has `F → D → R` and `D → A`,
   whereas `R` has no outgoing adjacency (`candidate_intrusion.rs:386–409,
   438–468`). The selected A edge is `R → F`. It is absent from that recipe.

This conditionally derived adjacency mismatch is the smallest discriminator
used here. It is not an executed source-qualified counterexample or a claim
about an actual intrusion merge: with no retained parents, `settle_candidate_intrusion`
can return before scanning (`:368–376`). It exposes the original edge gap even
before a copied owner exists. Later successful dispatch cannot establish the
required before-dispatch edge retroactively.

The companion shape `my konst x = 0; my use = konst 1` distinguishes the selected
source target `K` from the literal provider. Its original target/root and use
coordinates are retained by the module route above. No runtime result or
complete post-dispatch graph was derived for this shape.

## Bounded transport consequences

Because the original edge is not installed, a joint retention claim through all
four stages already fails to follow from the current constructors. The following
static boundaries identify the next obligations; they are not another transport
proof or an executed copied-edge counterexample.

* Polar extrusion visits the actual four Function ports and selected bounds,
  then rebuilds those ports (`candidate_extrusion.rs:224–249,308–352`). Its
  source-bound evidence transfer is bound evidence, not the selected Apply
  incidence. There is no callee slot in a negative demand. Installing `R → F`
  first still leaves the copied result's inherited callee incidence and its
  jointly scoped target transport to the constructive lane.
* Fresh-use capture expands native payloads/bounds, and preparation maps each
  canonical captured row once (`candidate_scheme.rs:36–88,289–325,458–513,
  567–572,981–1019`). The local-use route retains its own graph/map and admits
  its mapped root (`:1362–1385,1516–1518`). It does not capture a selected Apply
  incidence as a separate contribution. A row encountered incidentally through
  the type interface cannot authorize transporting a Name edge.
* The frozen odd/even analogue
  `my odd n = { my even n = odd(n); even(n) }` fixes inner callee target `O`,
  inner argument/formal `B`, inner result `R`, and retained positive `C/B` and
  negative `D/R` extrusion pairs. A now requires the inner original edges
  `R → O` and `R → B`. The negative demand maps `B` and `R`, not its outside
  callee Name. This audit does not determine whether either retained pair
  qualifies or what additional legitimate references its values contain.
* The SCC consumer scans both bound sides, structural Function ports, and
  Effect nodes, then compares retained parent/copy representatives
  (`candidate_intrusion.rs:358–488`). Neither its mixed paths nor parent
  metadata establish the approved Value adjacency.

## Admission, evidence limits, and next action

The three shapes use constructors present in LocalSource: Name, Integer,
Lambda, single-argument Apply, and brace Block. Apply accepts `MlArgument`,
`CallTail`, and inline `ColonApplicationTail`; comma-separated/multiple argument
tails are rejected (`local_source.rs:529–581`). Local resolution precedes module
resolution (`:635–656`), and local initializers preserve distinct parameter
scopes (`:329–365`). Static representability assumes the expected recovery-free
syntax tree; parser/HIR admission was not executed. The literal conditional,
infix arithmetic, and indentation form of the earlier odd/even example is not
established by these constructors. Candidate preflight also rejects unresolved
or ambiguous Names and unsupported annotations/operations
(`candidate_source.rs:85–118`). Complete Call suppliers remain explicitly
pending (`candidate_call.rs:81–109`); this audit neither supplies nor bypasses
them.

There is no executable oracle, random seed/range, mutation, or independent
source validator. The static derivation shares the admitted-carrier and
successful-prefix assumptions of the frozen notes, but reads the actual
constructor/consumer branches rather than assuming checker transitions.
No all-source ownership completeness, copied-edge target law, SCC qualification,
equality soundness/principality, Call/effect semantics, or F5 closure is claimed.
All those gates stay OPEN.

One next action: hand the exact original Apply-edge installation and consumer
gap to the primary's construction owner, using `invoke` as the smallest
before-dispatch discriminator and preserving the prover's separate copied-owner
and target-transport obligation. Any compiler change requires its own explicit
implementation lease.

## Checks, resource accounting, and dependencies

Checks were static `cat`, `rg`, narrow `sed`, SHA-256 capture, and leased-note
integrity inspection. Early combined captures truncated; decisive source windows
were reread narrowly. Startup used read-only Git status/HEAD/branch queries and
`git diff --quiet <baseline> -- <direct paths>` before noticing the packet's
literal no-Git-operations boundary. That was a process deviation; no Git
mutation occurred, and no later Git query was used. The initial comparison found
the answer, frozen notes, and audited source paths equal to the pinned baseline.
Dirty live design drafts were not used as authority; the parent-copy sections
were read from the pinned committed content plus the approved answer.

At most three lightweight read processes ran concurrently; zero build/test,
Oracle, probe, performance sample, compiler/test write, or delegated process.
The single audit stopped at its first concrete installation gap. CPU/RSS and
exact reasoning wall time were not measured. Requested policy route is the
normal complementary researcher lane; effective runtime model/effort metadata
is unavailable. No independent review of this artifact occurred.

No dependency was edited by this leaf. Direct SHA-256 snapshot:

| Dependency | SHA-256 |
| --- | --- |
| approved answer | `91c1dedc3cb4cffa9051c65f12b1813eab912da925b2ef950c01771fc72276ec` |
| frozen incidence construction | `f323fab5dd37a6358dcbd88393ab83176218bcea73caf5d66ae8903dfe572139` |
| frozen odd/even derivation | `3ddd46a2045dee5b9ff1ac99f7d9717d22b82ede1625aedeea815a456b84c12a` |
| top-level inference principles | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `crates/yu-hir/src/module/local_source.rs` | `906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed` |
| `crates/yu-solver/src/candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `crates/yu-solver/src/candidate_call.rs` | `79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35` |
| `crates/yu-solver/src/candidate_scheme.rs` | `9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `crates/yu-solver/src/shadow_apply.rs` | `cbd2e0c49a3f1fbe3c5fc78a06d469faedf4aa261525b24a0c9584e9956c2411` |
| `crates/yu-solver/src/lib.rs` | `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94` |

The audited `shadow_apply.rs` matches the current pinned baseline but differs
from the historical `230ed70…` snapshot printed in the two frozen notes. Its
Apply admission window was therefore read directly. Other audited source
hashes match those notes' snapshots. Integration revalidation stays with the
primary.

## Commit packet

Exact leased/changed path:
`notes/progress/2026-10-12-apply-reference-transport-audit.md`.
Baseline: `a18d70f209a7145ebe27ba646ff8dc7e8663c28f`.
Changed dependency hashes: none caused by this leaf; historical
`shadow_apply.rs` snapshot drift is disclosed above.
Claim/review: unreviewed conditional static prefix discriminator and source
correspondence gap; no theorem, implementation, or parent-gate closure.
Checks: static constructor/consumer reads, baseline equality inspection,
SHA-256 snapshot and note integrity; no builds/tests/Oracle/probes.
Proposed checkpoint message:
`research: audit Apply Name incidence installation and transport gaps`.
Shared-record deltas left for the primary/curator: record A as the original
Apply-edge authority, replace the earlier undecided original Apply ownership
premise with the concrete installation gap, retain copied-owner/target transport,
SCC qualification, equality, complete Call/effects and F5 as OPEN. No shared
record was edited. Writes stop before submission for frozen review.
