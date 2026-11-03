# R333 actual goal-kernel transport — frozen handoff r1

Assignment: `R333-GOAL-KERNEL-TRANSPORT`; revision **1**. Worker/author:
`/root/r333_goal_kernel`; no descendants. Baseline supplied by Luna:
`0d5c7dfb0`. Current source bytes, rather than baseline shorthand, identify
all inputs. Requested/observed model metadata is not exposed to this worker
and remains UNKNOWN here; primary owns runtime metadata and review assignment.

Contract: `tasks/agent-loop/sprints/source-kernel-transport-r333.md`, SHA-256
`3fb294a21d49e3b432ef3662e95b6535eb72216546116ff73f184c83aa35ed9a`. This is a bounded leaf repair,
not a semantic or production-authority change.

## Original claim and correction

The authoritative selection is
`notes/design/2026-10-08-source-generalize-definition.md` §2
(SHA-256 `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38`),
selecting SG `notes/theory/2026-10-08-source-generalize-definition-and-proof.md`
§§3.1–3.3 and source/program correspondence SRC §6
(SHA-256 `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`).
SG §3.2(4) requires the Function observation for **each checked challenge**,
with the same actual callable and whole joint tuple. SRC retains the same
source operands, endpoints, choices, scopes and witnesses.

Actual corrected definitions read:
`YulangClosure.OriginalCheckingAdmission.GoalDataAdmitted`, `.GoalAdmitted`,
`.goalAdmissionKernel`, `.goalFunctionKernel`, and `.registeredKernel`.
The inspected source SHA-256 is
`77a8dd74f5913814d3628f0aed189be24b4aafc4780839eaa57237676a157da7`.
`goalFunctionKernel` first installs original source admission and genuine
`OriginalSourceEnvironment.FunctionShape`, then overrides checking admission
with current-goal `GoalAdmitted`. The existing legacy transport did not prove
this case. The two checked discriminators
`OriginalCheckingAdmission.Discriminator.broad_source_narrow_goal` and
`.narrow_source_broad_goal` show that source and goal domains can differ in
both directions. This repair never assumes their equality or descriptor
alignment.

The unchanged parent edge is R159's original App admission/continuation,
R311's formation split, specialized to R315's actual context/callee/argument,
and applied at R332's actual registered prefix. The new module reproves the
parent inversion and R332 application using the actual goal kernel throughout.
It does not reinterpret a legacy-kernel source proof as a goal-kernel proof.

## Construction and applied parent edge

Namespace: `YulangClosure.OriginalSourceGoalKernelTransportR333`.

`transportedKernel g base gen ro adm old` is exactly
`goalFunctionKernel (inputs base gen) (readout g ro) (admissions g adm)
  (OriginalSourceKernelTransportR333.primitiveKernel g old)`.
An independently checked audit example proves by `rfl` that its fields are
actual extended `Admitted`, actual extended `GoalAdmitted`, and actual extended
`OriginalSourceEnvironment.FunctionShape`.

`function_shape_preserved` constructs genuine extended FunctionShape from the
original FunctionShape using `decode_commutes`; all eleven incidence equations,
the original registered call owner, and both descriptor form guards are kept.
It does not transport arbitrary `old.functionShape` and label that native
incidence. All other primitive fields are the existing conservative images
of independent original evidence.

For arbitrary `s`, `View`, `G`, `g`, original Inputs/readout/admissions/kernel,
original environment and goal/tree/source, the central theorem types are:

```lean
checking_transport :
  Checking (goalFunctionKernel base ro adm old) env goal →
  Checking (transportedKernel g base gen ro adm old) (environment g env) goal
local_transport :
  Local (goalFunctionKernel base ro adm old) env premise →
  Local (transportedKernel g base gen ro adm old) (environment g env) premise
judgment_transport :
  Judgment (goalFunctionKernel base ro adm old) env tree →
  Judgment (transportedKernel g base gen ro adm old) (environment g env) tree
source_transport :
  SourceJudgment (goalFunctionKernel base ro adm old) env context source →
  SourceJudgment (transportedKernel g base gen ro adm old)
    (environment g env) context source
```

These are type excerpts with module-local variables; the complete fully
qualified printed types of every delivered theorem are preserved in the audit
logs below. `checking_transport` uses the checked sibling
`OriginalSourceAdmittedImageR333.goal_admitted_image_iff` at the
**current goal** in the Function branch. Thus every target checked candidate
has its proven old preimage, and the observation child uses exactly the
commuting extension. Ordinary source quantifiers and open executions use
`admitted_image_iff` instead. No target candidate is assumed to be an image.

`app_parent_formation_iff` reproves R159/R311/R315 inversion from generic
`SourceAppAdmissionR159.app_source_iff`, `.app_continuation_iff`, and actual
`.admitted_view_iff`. It retains both annotation alternatives, optional
singleton-formal origins, independent logical admission, formation, all
remaining locals, and both children at one original candidate extension.

`register_actual_parent` applies that inversion, then R332's actual
`RegisteredAt` prefix/registration with the extracted **same** occurrence and
logical data. `registered_parent_transport` and
`register_actual_parent_transport` construct target formation, all locals,
both children and the selected App source judgment at the same
`scopeCandidate before occurrence (definedPayload data definition)` extension.
No target child/source judgment is an assumption.

`original_source_parent_registered_alternatives` and
`original_source_parent_transported_alternatives` apply the goal-kernel source
root inversion through the actual description, outer view, invocation,
receipt, return, shared anchor and EventProof prefix. Invocation and open-return
quantifiers remain universal; fixed replay retains the genuine execution
lookup. Vacuous invocation domains do not manufacture reachable environments.

## Coverage and remaining premises

Checking covers identity, primitive, composition, structural and Function,
plus the mutual list cases. Boundary preserves proof-only finite checking and
actual conversion. Local covers atom/checking/boundary. Judgment covers rule,
exists/forall, initializer, open/fixed execution, shared anchor, all three
publication operations, both source choices and both list cases. Source
transport is generic in Category and the complete existing sourceRules;
no record, optional field, method, effect or source constructor is removed.
Publication success/failure, duplicate/ordered histories and lookup use the
checked sibling commutation results, with unchanged source/environment data.

**Status: kernel-accepted conditional transport, applied to the original parent
edge; whole source/native parent OPEN.** The root theorem's explicit source
hypothesis is an actual original
`SourceJudgment (goalFunctionKernel base ro adm old) initial externalContext root`.
That hypothesis was already the source-side input to the R332 parent edge;
this packet does not construct it from native solver success. Given it and
initial decode, this packet removes the old-to-extended Local/Checking/child
transport gap without adding target proofs as premises.

First remaining native/application obligation, owner Luna/source-semantic lane:
authenticate the original goal-kernel source derivation/primitive relations and
identify the conservative extended Inputs/readout/admissions/kernel with the
intended actual native interpretation. A legacy R332 source proof alone does
not supply the new goal-kernel input. In particular,
`OriginalCheckingAdmission.registeredKernel` additionally installs
`OriginalSourceChecking.FunctionShape` with registry/declarations/port semantics;
this repair does **not** transport that additional wrapper or its native laws.
Genuine bare Function incidence preservation does not close registered semantic
checking, licensed Call/result/field correspondence, whole-language soundness,
original A/B, or production promotion. Fresh independent review remains owned
by Luna; this producer makes no independent-acceptance claim.

Mutual TODO `R333-GOAL-NATIVE-1`: supply a source/native authentication theorem
for the exact original goal-kernel root and concrete old primitive fields,
plus a separate registeredKernel naturality/correspondence packet if that is
the chosen actual consumer. Falsifier: a concrete native local/registered
Function guard not preserved by this image, or a target admitted nonimage
candidate contradicting the sibling image theorem under its exact Inputs.

## Files, immutable inputs and checks

Only repository writes:

- `notes/theory/lean/YulangClosure/OriginalSourceGoalKernelTransportR333.lean`
- `tasks/agent-loop/inbox/original-source-goal-kernel-transport-r333.md`

All scratch/build/audit output is owned under
`/tmp/yulang-r333-goal-kernel`, including isolated `project/`, frozen sources,
`rebuild.py`, `rebuild-commands.json`, 59 `rebuild-*.log` files,
`GoalKernelAudit.lean`/`.log`, `GoalKernelCensus.lean`/`.log`,
`audit-commands.json`, `axiom-results.json`, `source-audit.txt`,
`verified-dependency-hashes.json`, `input-hashes.json`, and
`dependency-order.json`. No compiler, root imports, configurations, manifests,
lockfiles, shared task/status files or Git state were edited.

Frozen Lean SHA-256: `801ce238d78c2c94bdaf36b43c1a6b6a609b5758a1518ca46a51378de6d1314d`.
Fresh built olean SHA-256:
`770044ce79fd460fc362665272122015b7faf2957cf8213636e755035b358814`.

Direct frozen dependency source hashes:

| Module | SHA-256 |
| --- | --- |
| `YulangClosure.OriginalSourceKernelTransportR333` | `aea7032224a7c2d55c7f12e03fc9f150bc123f12d9b30b56906597b881b65bcf` |
| `YulangClosure.OriginalSourceAdmittedImageR333` | `a902c15f2960231478ad7800f2354b1c136941e695a06fdfd1e3683292fc7bf1` |
| `YulangClosure.OriginalSourcePublicationTransportR333` | `a6c9e70a159bf60a72bda0fcc873986564ae5358dd042bccfad166df877e7c22` |
| `YulangClosure.OriginalSourcePrefixBridgeR332` | `52396832fcbae8044adb331a6a4c9fb803f81ac8450587006c347f2eb754e199` |
| `YulangClosure.OriginalSourceEnvironmentTransportR331` | `d21945af4a0230a70b1670682f818530fe21460649a3b3b66c787da52109a97c` |
| `YulangClosure.OriginalModuleContextBindingR315` | `7adcf88c1ff98c5c4cf23aa788bf5713ddcb949dd09775fb0bd542fe1e2ac577` |

Every source and freshly rebuilt olean in the 59-module cone has an exact
SHA-256 in `verified-dependency-hashes.json`. All 58 inherited dependency source
hashes matched the previous kernel receipt, and they were then rebuilt serially;
no stale olean freshness claim is needed.

Pinned native executable:
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`.
Read-only `elan which lake` resolved it; no installation/dependency changes.
Actual versions: Lake `5.0.0-src+eb6cafb (Lean version 4.35.0)`;
Lean `4.35.0`, `x86_64-unknown-linux-gnu`, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Release.

Actual commands from the isolated project:

```sh
python3 /tmp/yulang-r333-goal-kernel/rebuild.py
# For every dependency in topological order, then the new module:
LAKE --no-cache env lean -j1 -M2048 -o .lake/build/lib/lean/MODULE.olean MODULE.lean
LAKE --no-cache env lean -j1 -M2048 --root=/tmp/yulang-r333-goal-kernel /tmp/yulang-r333-goal-kernel/GoalKernelAudit.lean
LAKE --no-cache env lean -j1 -M2048 --root=/tmp/yulang-r333-goal-kernel /tmp/yulang-r333-goal-kernel/GoalKernelCensus.lean
```

`LAKE` above abbreviates the absolute executable already specified; all literal
command argument arrays, individual exits and elapsed times are recorded in
`rebuild-commands.json` and `audit-commands.json`. All 59 fresh compiles and
both audits exited **0**. Initial focused compile also exited 0 with an empty
`check1.log`; no failed construction/repair attempt was hidden. New module and
audits have no diagnostics. The fresh cone retained one pre-existing warning
in read-only `SourceLogicalOccurrencesR104.lean:152:70` (`Prod.exists` is an
unused simp argument); its exact log is retained and belongs to the R104 owner.

The bundled skill checker's unchanged `audit_source` generated the named audit,
and its unchanged `validate_audit` accepted both named and census output.
The automatic helper build/default `-M1024` audit was not invoked: the granted
local `-M2048` serial build/audit was used for the known R315 memory constraint
without modifying project configuration. This is manual pinned kernel checking
plus the same theorem-kind/axiom/complete-output validation, not a claimed run
of the helper CLI or a changed whitelist. Default root/full build remains the
primary's integration check; root imports were outside this lease.

There are **18 authored theorem declarations** and **20 originating-module
theorem constants**. The two generated equations are
`ReturnParentRegistered.eq_1` and `ReturnParentTransported.eq_1` in the new
namespace. Each of all 20 has a printed complete type and `#print axioms` result
in `GoalKernelCensus.log`; each result is exactly
`[propext, Classical.choice, Quot.sound]`. No sorryAx, project axiom or other
axiom occurs. `axiom-results.json` preserves the full per-name list. The source
search of the entire 59-module cone returned only comments and existing audit
error strings; no proof holes, axiom declaration, native_decide or checker bypass
was found (`source-audit.txt`).

Measured verification: 59 serial compiles in **127.874 s**, peak child RSS
**1,421,092 KiB**; named audit **1.117 s**, complete census **0.716 s**.
One Lean process at a time, `LEAN_NUM_THREADS=1`, `-j1 -M2048`; rebuild aggregate
timeout 1200 s, audit limit 120 s each, within the assigned 2700 s envelope.
No full/default build, native runtime test or production correspondence receipt
is claimed. All verification processes have exited; heavy slot released to Luna.

## Stop receipt

Lean source writes stopped at the previously announced frozen hash. Handoff r1
is now frozen; all writes for this assignment have stopped, including scratch.
No descendants or unresolved generated-output writers exist. Pending independent
review/integration is primary-owned. Any repair requires an explicit thaw/new
handoff revision; the current artifact is not self-certified.
