# R36 leaf handoff r1 — first build failed, writes stopped

Sprint `PAPER-CORE-CONTROL-20261026/r36`, contract SHA-256
`e3427e6f06bc49e20d9f43a40c2dacbc764337acfe0ee98f0377845c0f0be784`.
Baseline `ccc8ad9ce`; committed RUNNING/cache acknowledgement `a1b8e5503`.
Worker `/root/r36_registered_lean_prover`; runtime thread
`01a17472-58e6-75b3-88ac-279c1d314849`, environment session
`01a172ef-fec1-72e3-bd47-bc4d7f51d6aa`. Fresh receipt 2026-10-25 19:03:52 UTC.
Requested registered `lean_prover` / role default; observed model/effort UNKNOWN.
No descendants or contributing authors introduced by this worker.

Outcome class: **candidate, build rejected**. No theorem is delivered as proved,
no fresh printed theorem types or axiom results exist, and no independent review
or source/native/production acceptance is claimed. First failed command stopped
this revision immediately; source has not been repaired after that failure.

## Source and original parent

Read root AGENTS/base operating map, goal-driven rules, Lean skill source/execution
references, selected contract, actual paper grammar/typing, R28 substitution,
R35 source/handoff/review, and the separate Original bridge boundary.
Governing manuscript `docs/yulang-operational-type-safety-ja.tex`: opening source-owner
resume correction; typing :203–240; ordinary reductions :305–316; active child
:331–334; frame typing/inversion :1014–1026; precise one-step preservation/display
simulation parent :1860–1875. This is bounded mathematics for the paper judgment;
the research manuscript/drafts are not compiler semantic approval. The opening
correction leaves full source correspondence open.

Candidate namespace: `YulangClosure.PaperTypes.PaperCoreControl` (`PCC` below).
`PCC.State` contains actual `Computation` plus finite actual let bodies.
`PCC.StackTyped d g e bodies intermediate result` composes each body typed under
`intermediate :: e` through its result to one fixed final `result`. `PCC.StateTyped`
existentially supplies only the head intermediate type, keeping arbitrary common
`d/g/e` and final result unchanged. `plug` uses the first body as the innermost
pending frame. `controlStep` prioritizes let descent/push, then nonempty return/pop
with actual R28 `termSubstituteComputation (PaperCoreStep.singleReplacement value)`,
then partial R35 head stepping. `ControlStepEvidence` is auxiliary sound evidence;
its converse and priority completeness are not claimed. `PaperLetContextStep` is
R35 principal reduction closed solely under ordinary let active-child contexts.

Candidate principal types, **source statements only, not printed checker receipts**:

```lean
PCC.preservation : PCC.StateTyped d g e s result →
  PCC.controlStep s = some s' → PCC.StateTyped d g e s' result
PCC.erasure : PCC.controlStep s = some s' →
  PCC.erase s = PCC.erase s' ∨ PCC.PaperLetContextStep (PCC.erase s) (PCC.erase s')
```

The generated audit lists all eight candidate declarations:
`PCC.controlStep_evidence`, `PCC.plug_typed`, `PCC.erase_typed`,
`PCC.evidence_preservation`, `PCC.preservation`, `PCC.plug_step`,
`PCC.evidence_erasure`, `PCC.erasure`. Their audit was **NOT RUN**.

## Actual failure and exact handoff

Native call 3, `lake build +YulangClosure.PaperCoreControl`, exited 1.
First diagnostic at `PaperCoreControl.lean:76:6`:

```text
'change' tactic failed, pattern
  Option.map (fun next => { head := next, stack := stack })
    (PaperCoreStep.step ?m.335) = some s'
is not definitionally equal to target
  controlStep { head := Computation.call function✝ thunk✝, stack := stack } = some s'
```

The same source line fails for 19 unsupported-head branches: call, resume, split,
switch, choose, absurd, primitive, perform, handle, mapOperation, recursive,
template, fail, request, scope, expose, enter, tryArms, waitArm. Full diagnostics,
actual goals and dependency warnings are preserved in the log (226478 bytes),
not replaced by this excerpt. The generic fallback `change (PaperCoreStep.step _)`
leaves its head metavariable unconstrained where the actual partial R35 step is
`none`. This is elaboration failure; no mathematical counterexample was obtained.

First remaining local obligation/owner: Luna must authorize any later revision
that discharges `PCC.controlStep_evidence` for those no-successor cases from
`controlStep s = some s'`. A later revision can explicitly simplify impossible
branches or retain the actual head in the map equation; this is an unexecuted
repair suggestion, not checked evidence. The remaining candidate theorems cannot
be certified through an invalid upstream proof. No retry, repair, audit or further
native command occurred under r1.

Parent application: none established by R36. If repaired and independently
accepted, the candidate would supply only typed finite ordinary let control and
erasure stuttering for R35-supported principal steps. Current-port diagram
inclusion, residual-graph transport and full state/control correspondence remain
the first manuscript-parent bridge, owned by Luna's source/control proof lane.
No compiler source/constraint/propagation/consumer correspondence was investigated
or asserted; this packet authorizes no compiler implementation.

Represented candidates: actual arbitrary paper computation heads, finite ordinary
let frames, head type distinct from final result, capture-avoiding R28 pop, R35
let/return, force/delay, both union injections, unroll/roll, field/record and
lookup/record, with every stored frame retained in order. Omitted transitions:
scope/expose/handle/mapop/wait frames; requests, full calls/wrap, handlers/effects,
recursive allocation, heap graph and administrative steps, full evaluation and
termination. `none` has no termination/Fail/Bad meaning. Source/native, inference
A/B and production gates remain OPEN.

## Exact files and frozen dependencies

All writes were within these leased paths:

- Source `notes/theory/lean/YulangClosure/PaperCoreControl.lean`, 6749 bytes,
  SHA-256 `7ce8fb1c4a3cafe2738723af3dea6e6df11b4d227f1151761941fdb38df7ca95`.
- Scratch `notes/theory/lean/.lake/R36Audit.lean`, 6559 bytes,
  SHA-256 `1a100c49eb1907b0c41de6655711dfa005058e1efd82961b1496f4c4eaec76f2`.
- Complete log `tasks/agent-loop/inbox/paper-core-control-r36-worker-checks.txt`,
  SHA-256 `45338650e035a7b61b82b8de363e53f51c0e53074ee2f4d6ac06dd5a6ce8a397`.
- Generated outputs under exclusive `.lake/build`; no R36 `.olean` or `.ilean`
  was produced. The R36 setup JSON exists, SHA-256
  `26b86d650e8a62192081e14a5576320b6e68bbd5cbd82ed113f152bea9943292`.
- This exact handoff path. Final handoff byte hash is sent to Luna separately.

Frozen hashes verified before work, with source/toolchain/config dependencies
reverified unchanged after the failed build:

| Input | SHA-256 |
| --- | --- |
| manuscript | a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b |
| PaperExecutionSyntax | e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932 |
| PaperExecutionTypingSubstitution | 3b1588bff2d28a3db7aa241c930495b84f090e880ad49ac8fb2d593d54943d41 |
| PaperTermSubstitution R28 | a4f87f9604c03beefdc44de5d45fcd9f5924ca9580c75edf353cf267e69a0d4f |
| PaperCoreStep R35 | 503f81c162f7b9ceb0f7d27aa9796b8d7010345653267c675267ce14214c57e9 |
| CoreControlBridge boundary | 30a0007aea313eccc42531bf346891c010dbed7b4b34cea1aebe7043a9a6d99a |
| R35 r3 handoff | 05cacac3b1536ff53eea589e71536cac2b5d34bbd1b71ef48e195a1aeb0eb128 |
| R35 r3 review | 5212dd2f014f5868d13aee909dfa794e530fedd872a8dc137081aa8d675364a5 |
| lean-toolchain | ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c |
| lakefile.toml | 2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194 |
| lake-manifest.json | 058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3 |

R35 imported artifact hash before work:
`9cd98cdcbd39f312e94a9981f5449cc12847160162ce4975b5d617111a537057`.
Read-only source traversal found no sorry/admit/project axiom/bypass matches in
the ten local dependency modules; this is not an indirect axiom audit.

## Actual commands, resources, cessation

Read-only `elan which lake` exited 0. All native calls used
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`,
cwd `notes/theory/lean`, `LEAN_NUM_THREADS=1`, one serial build at a time:

1. `lake --version`: exit 0, Lake `5.0.0-src+eb6cafb` / Lean `4.35.0`,
   0.032071335 seconds.
2. `lake env lean --version`: exit 0, Lean `4.35.0`, x86_64-unknown-linux-gnu,
   release commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`,
   0.058020976 seconds.
3. `lake build +YulangClosure.PaperCoreControl`: exit 1,
   0.434279427 seconds through the failure receipt.

Used 3/10 worker native calls and 0.524371738/120 worker checker seconds.
R1 cannot spend its nominal remainder after first failure. Primary owns aggregate
sprint accounting (14 calls/180 checker seconds/1800 active seconds, no reset).
Fresh worker receipt 19:03:52Z; final process scan 19:06:37Z found no native
Lean/Lake/checker process. Final handoff follows within this same finite interval.
The skill's `audit_source` generated scratch via `python3 -B`/`runpy`; validation
was not reached. Bytecode writes disabled; no new out-of-lease pycache introduced.
No Git, tests, Rust, network, installations, dependency/config/root-import changes,
shared-record writes or reviewer appointments.

Source/cache/checker work STOPPED at first failure. After this frozen handoff,
**ALL WORKER WRITES STOPPED**; no descendants or unaccounted worker leases.
Luna may reclaim cache ownership after consuming this receipt. Next action requires
primary adjudication of the failed revision; no self-certification or review of a
successful proof is available.
