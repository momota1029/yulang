# Bridge binding annotation: exact shared-tail selective-route probe

Date: 2026-10-10
Status: frozen, unreviewed research-only executable characterization.
Claim class: one parsed/lowered source root with an explicit solver diagnostic;
no global impossibility, compiler defect, R closure, or production authority.
Producer: `/root/bridge_return_annotation_selective_route`.
Assigned baseline: `f4be57bff` or newer record-only commits, branch
`research/simple-sub-intrusion`; no Git operation was used to inspect or alter it.
Exclusive tracked lease: this note. Dependencies are pinned by the previous
local-annotation note's exact hashes and rechecked before launch and at freeze.

## Input and decisive result

The primary assigned exactly this source, describing the colon as a function
return annotation:

```yulang
act E
my left (f:int -> ['r] int) g = { my bridge (consume:(int -> [E, 't] int) -> ['x] int): [E, 'x] int = { my cb z = { my old = f 1; consume cb }; my feed = g bridge; consume cb }; bridge }
```

The exact source parses with empty structural recovery, lowers, constructs the
normal candidate schedule, and reaches `candidate_effect.rs:1879`, immediately
after `execute_candidate_source_root(&owner).unwrap()`. Both annotations really
use `Local(bridge ordinal0)` and the written `'x` is authentic shared row27.
That fixes the previous probe's scoped-name distinction.

The current lowered colon annotation is nevertheless a **whole local binding
annotation**. It compares the bridge Lambda value with `Int`, rather than
checking the bridge body's result. The one solver error is
`IncompatibleValue { lower: Function, upper: Int }`, occurrence5/local_slot40;
the cause has the same occurrence and slot. The observer stops before the
host fixture's original assertions and manual constraints. Completing this
root with a recorded error is not successful accepted-source inference or a
selective-SCC witness.

At the completed root there are 72 Effect rows, four retained views and 29
actual Effect parent/copy records (9 Positive, 20 Negative). No recorded
Effect copy returns to its parent in this snapshot; every row is still its own
representative, intrusion generation is0, and dirty is false. The exact key
`R30 - Allowance(w[X27])` is absent. Owner `(C62,S25)` and tail `(T'61,T23)`
both fail the same-snapshot SCC membership tests. R remains OPEN.

## Exact owner of the failed premise

`yu-hir/module/source_annotation.rs:307–329` retains the
`PatternTypeAnnotation` directly as the binding's SourceAnnotation.
`local_source.rs:732–805` places it on `LocalSourceBinding.annotation`, while
`:329–369` creates the Lambda initializer from the local's parameters. It
neither moves this annotation onto the Lambda body nor synthesizes an outer
Function type around it.

`candidate_source.rs:280–300` schedules LocalAnnotation on the whole
initializer endpoint after that Lambda finishes.
`candidate_effect.rs:987–1027` selects
`AnnotationScope::Local(batch.candidate_source.locals[slot])`, constructs the
negative annotated Value, and admits the whole initializer to it at slot40.
For this source that lower is Function and that upper is Int. This is the exact
current HIR/planner/checking ownership of the observed diagnostic. No language
contract is changed or defect inferred from the task's proposed spelling.

`candidate_formal_effect_variable` at `candidate_effect.rs:844–864` reuses exact
`(AnnotationScope,name)` identity. The actual formal action and local action
both print the same HirLocalId: artifact Arc pointer `0x7ffff0005460`, definition
Arc pointer `0x7ffff00090f0`, ordinal0. First allocation prints
`(Local(ordinal0), 'x) -> row27, level2`; annotation view3 at byte94 has tail27.
No second `'x` allocation occurs. These are actual scope/row identities, rather
than an inference from matching names.

## Normal source action order

The observer reads the dispatcher at `candidate_source.rs:551`. Component
operands are planner components, not fabricated live Effect rows.

| Source/action | Actual occurrence / operand | Level or boundary | Order |
| --- | --- | --- | --- |
| f formal annotation | occurrence2, parameter0, Definition(left) | 1 | allocates r21 |
| consume formal annotation | occurrence5, parameter2, Local(bridge ordinal0) | 2 | allocates t23 and x27 before body |
| f1 / old install | Candidate0; Fact occurrence9/slot20; Install slot3, Component23 | boundary3 | before callback consume/cb |
| forming cb lookup | Link occurrence14, Component15 to target31 | body3 | before Candidate1/2 and Lambda0 |
| callback Lambda / install | Lambda0; Fact occurrence7/slot20; Install slot1, Component15 | boundary2 | before g bridge |
| forming bridge lookup / feed | Link occurrence17, Component9 to target35; Candidate3; Install slot2, Component17 | boundary2 | before final consume cb |
| final consume cb | Local slot1 occurrence20, value39, level2; Candidate4/5 | 2 | before bridge Lambda |
| bridge Lambda | Lambda1, initializer occurrence5 | initializer2 | delayed positive extrusion runs here |
| bridge annotation | Fact occurrence5/slot20; LocalAnnotation slot0, Component9, computation_effect10, occurrence5 | level2, boundary1 | **after** Lambda1; compares Function with Int |
| final bridge lookup | Local slot0 occurrence21, value7, level1 | 1 | after annotation |
| root completion | Candidate6; Lambda2; Lambda3; Link occurrence2, Component1 to target0 | root1 | all ordinary actions complete |

Compared with the prior checked-local probe, the annotation no longer runs
between `g bridge` and bridge Lambda. It runs on bridge installation after
Lambda/extrusion. The debugger does not add a constraint or change action order.

## Physical rows, bounds, views and parent identities

DL/DU below are actual physical direct lower/upper lists. Both are outgoing
owner-to-bound edges for SCC calculation. Support/Allowance outgoing edges go
to their retained view's tail. All rows remain unmerged.

| Role | Row / level | Physical bounds or actual parent |
| --- | --- | --- |
| formal old r | 21 /1 | DU30 |
| older lower R from f1 | 30 /1 | negative parent28 at target1; Allowance0[23], Allowance2[61]; no exact positive Support |
| original formal tail T | 23 /2 | DL56, DU61; Allowance0[23] |
| positive formal P | 24 /2 | DU25,48; Support0[23] |
| original checking S | 25 /2 | DL30,55; DU62; Support0[23], Bottom; Allowance0[23] |
| original consume result X | 27 /2 | DL50; DU33,44 |
| negative copied X | 50 /1 | parent27, Negative,target1; DU54,58 |
| negative checking copy | 55 /1 | parent25, Negative,target1; Allowance1[56] |
| negative copied T | 56 /1 | parent23, Negative,target1; Allowance1[56] |
| positive copied T' | 61 /1 | parent23, Positive,target1; DL56; Allowance2[61] |
| positive copied C | 62 /1 | parent25, Positive,target1; DL30,55; Support2[61], Bottom; Allowance2[61] |
| whole-binding computation annotation receiver | 67 /2 | Bottom; Allowance3[27]; no direct row bounds |

The four views are `(view0,tail23,byte66)`, `(view1,tail56,byte66)`,
`(view2,tail61,byte66)`, and `(view3,tail27,byte94)`, all owned by the same
retained left definition. They correspond to the original formal E/t row,
negative copy, positive copy, and whole bridge binding E/x annotation.

The authentic incoming-Allowance extrusion observer runs during Lambda1 on
owners30,61,62 with view2/tail61. R30 retains view0 and view2 Allowances. The
only actual Allowance using X27 is view3 on row67; row67 is the one-shot
Lambda initializer computation carrier's annotation receiver, not the bridge
body's result or R30. Thus scoped `'x` sharing does not establish the required
older-row replay key. Act E has no operation; no operation-origin concrete
Support is claimed.

The original callback return is real:

```text
X27 --direct upper--> 33 --direct upper--> S25
```

The negative copy follows different actual rows:

```text
X50 --direct upper--> 54 --direct upper--> 55
```

Their parents are `(50,27,Negative,1)`, `(54,33,Negative,1)` and
`(55,25,Negative,1)`. No parent record is treated as a reverse edge. The copied
route does not return to original S25. Here negative S-copy55 also has no
edge to C62: C62 owns the lower55 edge in the opposite direction.

## Same physical snapshot: both SCC tests

The frozen helper traverses actual direct row lists and actual Support/Allowance
view tails, canonicalizing through the current representative forest. No
capture-incidence or parent-provenance edge is added. This end-root physical
snapshot has identity representatives.

```text
reach(C62) = {23,30,55,56,61,62}
reach(S25) = {23,25,30,55,56,61,62}
reach(T'61) = {56,61}
reach(T23) = {23,56,61}
reach(R30) = {23,30,56,61}
reach(X50) = {41,50,52,53,54,55,56,57,58,59,60}
```

| Actual recorded pair | Copy reaches original | Original reaches copy | Same SCC |
| --- | --- | --- | --- |
| C62 / S25, Positive,target1 | no | yes | no |
| T'61 / T23, Positive,target1 | no | yes | no |
| 55 / S25, Negative,target1 | no | yes | no |
| 56 / T23, Negative,target1 | no | yes | no |
| X50 / X27, Negative,target1 | no | yes | no |

The real merge-entry observer emitted no earlier qualifying snapshot. The
final generation is0. All 29 recorded Effect parent/copy pairs also fail the
copy-return test at the end-root snapshot. This is bounded evidence for this
error-producing program only; it is not induction over all source programs or
all continuations.

## Reproduction, resource budget and omitted verification

The existing host binary and frozen observer are reused; there is no build,
Cargo freshness check, host assertion completion, extra source candidate,
source/compiler/spec edit, solver mutation, or artificial row/edge. The sole
inferior writes replace the make_session parser input and its already-prepared
rdi/rsi. The frozen runner differs from the prior runner only in its unique
scratch directory and the exact assigned source bytes.

```sh
python3 /tmp/yulang-bridge-return-annotation-selective-route-20261010/run.py source
```

One GDB launch completed with returncode0; wall1.369640184s, peak333792KiB,
user1.156843s and system0.224428s. GDB and inferior share one CPU affinity,
1.5GiB address-space limit, CPU55s, timeout45s, outer Python timeout50s. There
was no observer retry, timeout or resource kill. One earlier Python runner
invocation failed while constructing a quoted newline (`SyntaxError`) before
subprocess/GDB launch; the scratch quoting was corrected without changing the
source bytes. It consumed no source-root or observer-retry budget.

Artifact mode is M0 research-record handling, with the primary's separately
bounded executable packet; zero reviewers/certification, zero performance
samples, one distinct source/root and one stopped-root process. This is an
executable characterization. The yulang-proofs skill was read; proof
construction, delegation and independent review remain primary-owned. No
prover execution is claimed. Requested/observed model/effort metadata are
unknown. Static reads and offline graph/log analysis were unmeasured.

Unverified: a successful source computation annotation on the actual bridge
result in the same scope; the missing R30→X27 and copied-return producer;
selective owner intrusion; later unchanged-owner restore; exact omitted omega
fiber pair; every replay/diagnostic rescue; source induction, publication,
rollback/retry and full restoration R. No later restore/omega/rescue theorem
is supplied, and R stays OPEN.

## Frozen hashes and commit packet

All 21 prior note dependency/artifact hashes matched before the sole GDB launch
and at freeze. No changed dependency was found. Historical superseded hashes
inside the older witness are not substituted for its later frozen source set.
The exact matched list is:

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

Scratch evidence hashes:

```text
2356c6c1f165e030dd03e19729b41da17c640bf7ef5d6b28918a4e99c24e54b4  /tmp/yulang-bridge-return-annotation-selective-route-20261010/graph-summary.json
02135a9533f33c0f877456595741ce05b07ea1d37510f3debea8931c513ebe99  /tmp/yulang-bridge-return-annotation-selective-route-20261010/run.py
3c33a354f8398770aaaf4081444640613b74ed1ff85048e76fcabc2cb4d915b5  /tmp/yulang-bridge-return-annotation-selective-route-20261010/source.log
a93c100e35dfc533e1ce2e2e85cb1b994546592ec7f1ff8fd1a33b0ca34a3849  /tmp/yulang-bridge-return-annotation-selective-route-20261010/source.yu
aa7b6b3ed2f7d016de8513c20f5dff50cafacfef506ae7c338a43cd595734af4  /tmp/yulang-bridge-return-annotation-selective-route-20261010/verified-dependencies.json
```

Commit packet: sole leased tracked path
`notes/progress/2026-10-10-bridge-return-annotation-selective-route.md`;
baseline `f4be57bff` or newer record-only commits; changed dependency hashes:
none; frozen, unreviewed research-only. Checks: exact prior dependency/binary/
helper/artifact hash checks before launch and freeze, static annotation/HIR/
planner/checking reads, one bounded GDB normal stopped-root observation,
offline same-snapshot physical reachability and diagnostic inventory. No Git
operation or delegation. Proposed checkpoint message:
`research: characterize shared bridge annotation selective route blocker`.

Shared-record deltas deferred to primary/curator: record authentic shared
Local(bridge)/X27 identity, the whole-binding Function/Int diagnostic and
post-Lambda annotation order, absent R30-Allowance(X27), both failed SCC tests,
and OPEN R. `tasks/current.md`, theory/design/index and other shared records
were not edited. Next useful action is authority/owner adjudication of the
intended annotation target before another source-construction assignment;
this note does not authorize an annotation-semantics change or another probe.
