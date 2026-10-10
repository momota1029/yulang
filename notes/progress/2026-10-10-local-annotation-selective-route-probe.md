# Local computation annotation: exact selective-owner source probe

Date: 2026-10-10
Status: frozen, unreviewed research-only executable characterization.
Claim class: one authentic source root and a bounded missing-key result; no
source-impossibility theorem, R closure, defect, or production authority.
Producer: `/root/local_annotation_selective_route_probe`.
Assigned baseline: `bed730d1b`, branch `research/simple-sub-intrusion`.
Exclusive tracked lease: this note. No compiler/test/spec/fixture edits,
solver-transition injection, artificial rows, manual expected edges or delegation.

## Exact input and result

The single candidate is the assigned ordinary local computation annotation
rewrite. It contains no root expression `as [E, 'x] int`:

```yulang
act E
my left (f:int -> ['r] int) g = { my bridge (consume:(int -> [E, 't] int) -> ['x] int) = { my cb z = { my old = f 1; consume cb }; my feed = g bridge; my checked:[E, 'x] int = consume cb; checked }; bridge }
```

This exact input parses with empty structural recovery, lowers, constructs the
candidate schedule, and completes the normal `left` source root. The terminal
observer is `candidate_effect.rs:1879`, immediately after
`execute_candidate_source_root(&owner).unwrap()` and before the host fixture's
original assertions/manual follow-up operations. Solver errors are 0. There
are 108 Effect rows, seven retained views and 41 actual Effect parent/copy
records (12 Positive, 29 Negative). None qualifies in the same final physical
SCC snapshot. Intrusion generation is 0 and dirty is false.

The original consume result X really reaches original checking S through the
self-recursive callback. The missing fact is the copied route: neither
negative copied X61 nor positive copied owner C73 reaches original S26. This
candidate therefore does not establish selective owner SCC or later unchanged
owner restoration. Stop here; no second source candidate was attempted.

## Actual source actions and levels

The trace reads normal dispatcher actions at `candidate_source.rs:551`.
Occurrence numbers belong to this actual parsed/lowered HIR root; component
ordinals below are the dispatcher operands, not fabricated solver row IDs.

| Source/action | Retained occurrence / operand | Level or boundary | Observed order |
| --- | --- | --- | --- |
| Formal annotation for f | occurrence2, parameter0, Definition(left) | 1 | first formal action; allocates symbolic r22 |
| Formal annotation for consume | occurrence5, parameter2, Local(bridge ordinal0) | 2 | before bridge body; allocates t24 and x28 |
| `f 1` / old install | Candidate0; initializer occurrence9; Install slot4, Component25 | boundary3 | before callback's `consume cb` |
| forming cb lookup | Link occurrence14, Component15 to target33 | body level3 | before callback Lambda0; uses actual forming initializer |
| callback Lambda | Lambda0; initializer occurrence7 | initializer level3 | before cb Install slot1 at boundary2 |
| forming bridge lookup in `g bridge` | Link occurrence17, Component9 to target37; Candidate3 | body level3 | before feed Install slot2 at boundary2 |
| `consume cb` used by checked | Local slot1 occurrence20, value41, level3; Candidate4 | initializer level3 | before local annotation |
| checked annotation | LocalAnnotation slot3, occurrence18, Component19, computation_effect20 | level3, boundary2 | before final checked lookup and bridge Lambda |
| checked lookup | Local slot3, occurrence21, value13 | 2 | after annotation |
| bridge Lambda | Lambda1; initializer occurrence5 | initializer level2 | after `g bridge` and checked annotation; causes delayed extrusion |
| bridge install / final lookup | Install slot0 Component9 boundary1; Local slot0 occurrence22 value7 level1 | 1 | after bridge Lambda; normal capture/freshening completes |
| root completion | Candidate6; Lambda2; Lambda3; Link occurrence2 Component1 to target0 | root level1 | completes root |

LocalAnnotation runs after the real initializer one-shot computation Fact
occurrence18/slot20. Planner ordering is `candidate_source.rs:280–300`; its
computation carrier is installed before the binding's annotation action. The
forming bridge link exists before its positive Lambda lower becomes available.
No debugger observer adds a constraint or changes that order.

## Actual ports, copies and physical keys

All row and view IDs below are from the completed root's one physical snapshot.
Levels did not merge; each displayed row remains its own representative.

| Identity | Row / level | Actual retained bounds or role |
| --- | --- | --- |
| formal symbolic old r | 22 / 1 | upper row31; f's written singleton result tail |
| older lower R from f1 | 31 / 1 | S26 has direct positive lower31; C73 also has lower31; R has Allowance0,4,5 (5 occurs twice), no exact positive Support |
| original formal tail T | 24 / 2 | view0 tail; negative Allowance0; negative copy67 and positive copy72 are distinct records |
| original mixed positive formal P | 25 / 2 | positive Support0; upper26; separate from S |
| original checking owner S | 26 / 2 | positive Support0 and Bottom; negative Allowance0; direct lowers31,66; upper73 |
| original consume result X | 28 / 2 | written x in bridge scope; lowers61; uppers34,50 |
| annotation's independent x | 54 / 3 | written x in checked scope; negative copy71, later fresh use95 |
| negative copied X | 61 / 1 | parent28, Negative, target1; uppers65,69,89,88; no original S return |
| negative copied S | 66 / 1 | parent26, Negative, target1; Allowance2 and5; upper73 |
| negative copied T | 67 / 1 | parent24, Negative, target1; Allowance2,5,4; upper72 |
| positive copied T' | 72 / 1 | parent24, Positive, target1; lower67; Allowance4 |
| positive copied C | 73 / 1 | parent26, Positive, target1; lowers31,66; Support4,5 and Bottom; Allowance4 |

The annotation occurrence has view0 at source byte66, tail24. checked's root
row has a different retained view1 at byte168, tail54. Negative extrusion
views2/3 retain tails67/71; delayed positive extrusion view4 retains tail72;
ordinary later bridge freshening yields views5/6 with tails90/95. All preserve
their actual owning definition and source-node positions. The concrete E in
Support0/4/5 comes from the annotation, not an effect operation: `act E` has no
operation, and `f 1` provides an older symbolic lower without a concrete E
Support. Thus the source realizes the distinct older lower but does not add an
operation-origin concrete Support on R31.

Incoming-Allowance extrusion is actually observed during bridge Lambda1 on
owners31,72,73, all with Allowance4 and tail72. R31 retains original
Allowance0[24] and later Allowance4[72]/Allowance5[90]. None of these has the
independent consume result tail28 or checked's tail54. In particular the
intended distinct-result-tail key `R31 - Allowance(w[X28])` is absent.

## Scope identity and why original X return does not return its copy

`candidate_local_annotation` at `candidate_effect.rs:987` selects
`AnnotationScope::Local(batch.candidate_source.locals[slot])`. It uses the
annotated binding's own retained HirLocalId. Formal consume's annotation uses
Local(bridge ordinal0); checked's local annotation uses Local(checked ordinal3).
`candidate_formal_effect_variable` at :844–864 keys reuse by exact
`(AnnotationScope,name)` and retains the first allocation's level.

The actual allocation observer confirms:

```text
(Definition(left), 'r)            -> row22, level1
(Local(bridge ordinal0), 't)      -> row24, level2
(Local(bridge ordinal0), 'x)      -> row28, level2
(Local(checked ordinal3), 'x)     -> row54, level3
```

The local annotation therefore does not reuse parameter X's identity. It does
admit a directed comparison of the actual result to its independently scoped
row: original X28 has upper50, and row50 has negative Allowance1 with tail54.
This is the actual `X28 -> invocation50 -> Allowance1 -> checked-x54` route,
not equality or a direct scoped-name edge. It is also a real ascending view-tail
edge (row50 at level2 to tail54 at level3). Older R31 and C73 do not reach it.

Original X28 reaches original S26 by ordinary retained row bounds:

```text
X28 --direct upper--> 34 --direct upper--> S26
```

Negative extrusion at target1 copies that outgoing checking route:

```text
X61 --direct upper--> 65 --direct upper--> 66 --direct upper--> C73
```

The actual parents are `(61,28,Negative,1)`, `(65,34,Negative,1)` and
`(66,26,Negative,1)`. Original34 stores lower65 and original26 stores lower66.
A parent record is not a reverse edge. Reaching negative S-copy66 supplies no
`66 -> original26` edge, so the original X28 return cannot be substituted for
copied X61 return. This is observed identity separation in this root, not a
universal claim excluding every source continuation.

## Exact same-snapshot SCC calculation and restoration boundary

The observer constructs physical outgoing edges from each row's actual direct
lower and upper lists, and from each retained Support/Allowance bound through
its actual view tail. It follows current representatives; here no merger
changed any representative. Effect-row outgoing paths have no Function port
edge to omit. Capture incidence and parent provenance are excluded from
physical adjacency.

```text
reach(C73)  = {24,31,66,67,72,73,90,91}
reach(T'72) = {67,72,90}
reach(X61)  = {24,31,42,61,63,64,65,66,67,68,69,70,71,72,73,82,88,89,90,91,95,96,97}
reach(S26)  = {24,26,31,66,67,72,73,90,91}
reach(T24)  = {24,67,72,90}
```

| Actual recorded pair | Polarity / target | Copy reaches original? | Original reaches copy? | Same SCC? |
| --- | --- | --- | --- | --- |
| C73 / S26 | Positive / 1 | no | yes | no |
| T'72 / T24 | Positive / 1 | no | yes | no |
| negative S66 / S26 | Negative / 1 | no | yes | no |
| negative T67 / T24 | Negative / 1 | no | yes | no |
| negative X61 / X28 | Negative / 1 | no | yes | no |

The observer was attached to the real merge entrypoint; no earlier qualifying
snapshot was printed, and the final generation remains0. The complete
root naturally includes bridge capture and its later local use; captured S26
and T24 freshen to91 and90, while C73, T'72, R31 and negative X61 remain
shared. Negative checked-tail copy71 is shared and checked-tail54 freshens to95.
No qualifying C/S merger occurred, so a restoration on an unchanged original
S through this claimed selective merger is unavailable. No exact omitted
fiber, diagnostic failure or complete replay/rescue failure is established.
The probe stops at this missing source key; R stays OPEN.

## Reproduction, resources and coverage

Existing binary only:
`/tmp/yulang-source-hir-selective-scc-20261010/debug/deps/yu_solver-12ea9c1c0f03380a`.
Existing observer runner was the prior audit's frozen `run.py` (hash below).
A unique scratch copy changes its base directory and embeds only the exact
source above, lowers the CPU limit to55s, adds scope output to normal actions,
observes newly allocated annotation tails at `candidate_effect.rs:861`, and
prints terminal route row maps/diagnostics. It is retained at
`/tmp/yulang-local-annotation-selective-route-20261010/run.py`.

```sh
python3 /tmp/yulang-local-annotation-selective-route-20261010/run.py source
```

That runner uses the existing make_session breakpoint to replace its input
slice and prepared rdi/rsi before Arc construction, then continues ordinary
parse/lower/solve. Its only inferior writes replace parser input. It never
executes the host fixture's post-root manual constraints or semantic assertions.
The observer decoder and graph calculation reuse the prior frozen helper.
No build, Cargo freshness check, host fixture completion, suite, performance
measurement, syntax repair or second source root ran.

| GDB launch of same source | Outcome | Wall seconds | Peak KiB | User/system seconds |
| --- | --- | --- | --- | --- |
| initial observer | early stop: line861 also matches a closure lacking scope | 1.169111 | 304372 | 1.019994 / 0.132178 |
| corrected observer | complete root; scope-less closure locations ignored | 1.621329 | 334676 | 1.377115 / 0.239912 |

The initial observer stop is instrumentation failure, not a compiler/source
failure. Both launches ran sequentially with one CPU affinity shared by GDB
and inferior, 1.5GiB address-space limit, CPU limit55s, timeout45s and outer
Python timeout50s. Two launches, one distinct source, one complete source
schedule, zero builds, zero broad tests, zero performance samples, zero
resource kills. Static reads and log analysis were unmeasured.

## Frozen dependencies and commit packet

All prior audit's solver/HIR/design source hashes and the prior witness's
context-test/lockfile hashes match before execution and at artifact freeze.
No dependency changed. Assigned baseline remains bed730d1b; one startup
read-only Git status/HEAD inspection observed unrelated branch advancement to
7984bd084c1ab9f049353664a139066ba8151ec5. No Git mutation occurred.

```text
8adc289142dd78a625184dd661fb162e49f24532a19c7c4f9e114e604c0966a0  crates/yu-solver/src/candidate_source.rs
2599ad4412c7fc51841a4fcc4139f3b4d117ad6fa40a78a41a709ebe5ad1600e  crates/yu-solver/src/candidate_effect.rs
3fd1c7234c38013343e1c2e72bfed06c4eecdf7173e27d7581e11d6df84f0b3a  crates/yu-solver/src/candidate_extrusion.rs
aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0  crates/yu-solver/src/candidate_intrusion.rs
582bfb741315534dacf7290bb5618452bb55d9949a8aac691d8d01b93720de11  crates/yu-solver/src/candidate_scheme.rs
3b219b51ed8aba6ffc85675fd1d500b901a6f63b31325a85a586d688eee3515a  crates/yu-solver/src/candidate_context.rs
2635a036a520001ecf6387ee8e1edabcb463e2f1f8d82ab1482797c24bb37f30  crates/yu-solver/src/candidate_context_tests.rs
6bea8808153b8b71a57e4a8583284e49284ec9aa35118a61f44a3a387a8a32f6  crates/yu-solver/src/shadow_apply.rs
9c16200d5982efb6c20e19b969a289368954579113d2b166041abc7741ab0fa1  crates/yu-solver/src/lib.rs
906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed  crates/yu-hir/src/module/local_source.rs
a348a47530e57c2b3475a4c0d9f020e24ba04ea58a06292847892640567e61cb  crates/yu-hir/src/module/source_annotation.rs
24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8  crates/yu-syntax/src/full_parse.rs
a3f39b574e343b2065897e6df3b04ccf525a31df5fea1ed69ecc0bf07611e41a  Cargo.lock
717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc  notes/design/2026-10-10-contextual-attachment-admission-design.md
bc1f0effd53a49d07bcb8d68ca8a0adefe4a3563f4874e88827090cf0a2421f1  notes/progress/2026-10-10-source-selective-scc-impossibility-audit.md
17936a4926135bf04bedb52a2640073227ee17f8f971ba549095b227e56b8e81  notes/progress/2026-10-10-source-hir-selective-scc-witness.md
7aee4053118d02e626d70695433018c356105e8e7663e3f9776b5d922c4a4ec3  /tmp/yulang-source-hir-selective-scc-20261010/debug/deps/yu_solver-12ea9c1c0f03380a
c40c727ed223e9093fd70320834436e85843cccce6b2e416a5181a69dfbf4f49  /tmp/yulang-source-selective-scc-audit-20261010/run.py
8ca3132a580d920f3bfe9b7ff3d2947bd4e2256dbc5e2e83cafa2c810efdc451  /tmp/yulang-local-annotation-selective-route-20261010/run.py
5c01e476dbe2cf1f98810d9608159265216a30d5322ec424b4690ca5ee172d6c  /tmp/yulang-local-annotation-selective-route-20261010/source.yu
6751b01ad7f68946c4ac48d65830bc52a87e58f569be50087d4f4785ee23eb08  /tmp/yulang-local-annotation-selective-route-20261010/source.log
```

Commit packet: sole leased path
`notes/progress/2026-10-10-local-annotation-selective-route-probe.md`;
baseline bed730d1b; changed dependency hashes: none; status frozen,
unreviewed research-only; checks already run: dependency/binary/helper hash
rechecks, static owning-source reads, two bounded GDB launches of one input,
complete root/action/tail/route observation and same-snapshot physical graph
calculation. No independent review or prover execution is claimed.

Proposed checkpoint message:
`research: characterize local annotation selective owner route`.

Shared record deltas left for primary/curator: record successful local-annotation
syntax and actual original X28→S26 admission, while preserving the scoped
identity distinction, absent copied X61→S26/C73→S26 return and OPEN R. Keep all
later restoration/fiber/rescue and universal source induction gates open.
No shared task/theory/design/index/question-board file was edited.
