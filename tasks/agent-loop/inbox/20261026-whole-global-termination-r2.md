# Whole original inference termination r2 — frozen handoff

Status: **constructed and checker accepted; independent review pending; original `SourceProblem.InferenceTermination` OPEN.**

Frozen baseline: `45d307a0aa01722b5aac289b07d71953630abca7` (`yulang3` assignment). Generic leaf fallback for `.codex/agents/lean-prover.toml`; used `.agents/skills/yulang-lean-proofs/SKILL.md` and its source/execution references. Read the original principles, birth-level correction and actual contract. No Git mutation, compiler/configuration edit, package installation, shared status edit, root import edit or child-agent delegation occurred.

## Delivered paths

- `notes/theory/lean/YulangClosure/NativeInferenceProgress.lean`
- `notes/theory/2026-10-26-native-inference-progress.md`
- This handoff.

The proof is a source-constructor closure result through the complete Context consume segment, preserving lawful negative annotation `PrefixLeft(weight, Identity)` bootstrap bounds. It is not another scanner accessibility claim and not a whole-drain progress theorem. The accompanying note gives the exact native source map, every constructor case, original target and first unresolved parent premises.

## Principal exact theorem and parent application

`YulangClosure.NativeInferenceProgress.native_expand_context_closure` is universally quantified over the existing tables, availability, levels, representatives, finite-parser parameter and complete parent key. From `Shallow t parent.context` and the **actual existing** `NativeContextExpansion.expand t a levels q fuel parent = some body`, it derives zero `body.postContext`, zero Context on every emitted bound fiber, and source-local Context atoms on every emitted operand child. Entry/current-pair/parser/relation/publication gates, all filter leaves and the optional continuation remain in `expand`/`decompose`. `expand_consumes` connects that existing computation to the total-parser segment. Success is not fabricated for a rejected input and no runtime or native source behavior is changed.

`growing_context_closure` permits actual append-only table extensions between source, signature, Context, Replay, transport and atomic FreshUse constructor steps. It neither assumes a fixed finite universe nor supplies a global rank. `Step` is an explicitly labeled constructor projection, **not** the original `inferStep`. It stores historical objects and can have arbitrarily long construction histories. The full source/native execution extraction is unconstructed, including all bound lanes, Value-context entry, callback scheduling, rollback, captures and generation invalidation. The FreshUse atomic shape relation is a source-mapped successful branch, not a proof of the entire Rust renamer implementation.

The concrete remaining global obstruction is repeated extrusion siblings: `candidate_extrusion.rs:28–160` resets its memo each invocation and can freshly allocate the same source/polarity/target copy again. Strict descent down each parent/copy edge does not bound this sibling count. Context callbacks run before Dispatch (`lib.rs:14344–14363`), and complete relation memoization is current-generation and full-key sensitive (`lib.rs:13507` onward). Intrusion then creates new generations while row births replenish the representative supply. Source Name scheduling is finite and monomorphic on active recursive initializers, but each FreshUse captures the current live graph, so its graph size is not bounded by source Name count alone. The next required construction is an original-demand/copy descriptor supply with actual birth ancestry, scope-map formation and complete-key/generation accounting, followed by a combined nested-drain rank. No original divergent program was established.

The contract itself explicitly excludes runtime evaluation termination (`Contracts.lean:151–154`). No strong normalization or runtime divergence result is delivered.

## Frozen environment, checks and failures

Isolated project/cache and all intermediate logs: `/workspace/scratch/e3678bef96db/global-termination-r2`.

Installed native Lake: `/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake`.

Reported versions: Lake `5.0.0-src+eb6cafb` (Lean `4.35.0`); Lean `4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Release. Default sandbox toolchain lookup is unavailable; calls used the approved `require_escalated` path. No toolchain installation or manifest change was made.

| Check | Exit / evidence | Result and repair |
|---|---|---|
| 01 | 0, `check-01-dependencies.log` | Built frozen `+YulangClosure.OriginalInferenceTermination` and `+YulangClosure.NativeValuePorts`. **Resource incident:** initial Lake invocation omitted `LEAN_NUM_THREADS=1`; although each Lean process had project `-j1 -M1024`, Lake briefly scheduled dependencies concurrently. A default-sandbox `kill -TERM` attempt found no process in that namespace. Build completed normally. All following checks used one direct Lean invocation or explicitly single-threaded Lake scheduling. |
| 02 | nonzero, `check-02.log` | Fixed source-availability conjunction projection and reduction of a local let before splitting. |
| 03 | nonzero, `check-03.log` | Recursive simplification of total scan reached recursion-depth failure. Replaced it by explicit native step equations and `total_bind`; no resource limit was raised. |
| 04 | nonzero, `check-04.log` | Repaired dependent match simplification with explicit step helpers. |
| 05 | 0, `check-05.log` | Atomic scan and source/filter/complete-body/Value-port owner lemmas passed. |
| 06 | nonzero, `check-06.log` | Added the actual positive-ID facts needed for Replay child guards. |
| 07 | 0, `check-07.log` | All shallow Replay cases passed; harmless unused-simp warnings remained. |
| 08 | nonzero, `check-08.log` | Fixed inductive Step case syntax and removed reliance on an unavailable Boolean/propositional helper. |
| 09 | 0, `check-09.log` | Constructor history invariant passed. |
| 10 | nonzero, `check-10.log` | FreshUse constructor case used reserved `prefix`; renamed it `sourcePrefix`. |
| 11 | 0, `check-11.log` | Added `expand_consumes`, `native_expand_context_closure`, FreshUse and growing-table closure; passed. |
| 12 | 0, `check-12-audit.log` | Removed unused simp arguments. Required helper rebuilt final module and audited all 28 authored theorem roots with complete printed types and axioms. No warnings. |
| 13 | 0, `check-13-origin-audit.log` | Full origin-module census: 117 declarations / 50 theorem constants / all 28 required roots. No warnings. |

Checks 02–11 used `env LEAN_NUM_THREADS=1 timeout 120 <lake> env lean -j1 -M1024 YulangClosure/NativeInferenceProgress.lean`, from the isolated project. Check 12 used the unmodified skill helper `check_lean.py`, `--project` the isolated project, `--lake` the native executable, `--module YulangClosure.NativeInferenceProgress`, all 28 `--theorem` arguments and `--timeout 120`; exact argument vector is `check-12-argv.json`. Its orchestration wrapper had `timeout 125`; the helper imposed a shared 120-second budget on its sequential subprocesses. Check 13 used `env LEAN_NUM_THREADS=1 timeout 120 <lake> --no-cache env lean -j1 -M1024 NativeProgressOriginAudit.lean`. No additional full-project build was run in this leaf; root integration owns that gate. Thirteen focused checker calls were used, below the maximum twenty.

Two semantic approaches were rejected before freezing. First, identity-only original bounds are false for the actual negative annotation bootstrap. Second, finite source Name actions plus strictly level-decreasing copy edges are insufficient: FreshUse captures a graph grown by preceding drains, and separate extrusion invocations can produce arbitrarily many siblings without contradicting edge descent. Neither failure was converted into a source-language restriction or a new assumed finite final store.

## Static scan and complete census

All 178 frozen input SHA-256 entries in `freeze.json` matched on final revalidation. `dependency-cone.json` records the 14-file transitive import cone and hashes. `static-cone-scan.log` records 31 matches, all ordinary native `admit` function/constructor identifiers or prose. There is no `sorry`, tactic hole, project axiom, `debug.skipKernelTC`, `native_decide`, `implemented_by`, unsafe declaration or increased heartbeats/recursion depth in the changed dependency cone.

The module-origin auditor selects declarations by `env.getModuleIdxFor? name == some moduleIndex`, rejects project axioms, prints each originating declaration's actual complete type and transitive axiom list, and rejects axioms outside `propext`, `Classical.choice`, `Quot.sound`. It includes generated/private constants, not just the authored namespace roots. The 50 theorem constants have axiom distribution: 16 none; 8 `propext`; 21 `propext, Quot.sound`; 5 `propext, Classical.choice, Quot.sound`. The auditor source is below, and exact paths and hashes locate the complete actual output in scratch; this is checker evidence, not independent semantic review.

## File hashes and frozen source owners

| Artifact | SHA-256 |
|---|---|
| `NativeInferenceProgress.lean` | `d22167d330ce1bb000677e2915a85beddb0e7a483600ac8c6a92cfdf37c79b12` |
| `2026-10-26-native-inference-progress.md` | `1814465a05140e772bd4affd0c801c324d14e1d8d44a80028252687d0f8bb4ab` |
| `check-12-audit.log` | `b40b54f5ea1264309cec1e3652534ebe3ec88b862d08029879be8763cce1736c` |
| `check-13-origin-audit.log` | `7d5e6045c7b67a317a4c9422f5d5ba019fb151a91fa6d2480191ede272cd668e` |
| `NativeProgressOriginAudit.lean` | `9f4be3dc13b375998aa9d41b6eee5413e99254bd835eae11afa9371b05b8df38` |
| `freeze.json` | `58bde3ffdc5c2b3236b9cf52bea20577e1ef3638319897481a7e3579f6168068` |
| `dependency-cone.json` | `01fd2e64c7578c748c5f8610d3f263a0ab48967db9971ae1e244a662ad602f0e` |
| `origin-census.json` | `a29b11747557931301ad34f9d4c8fbe5b5246a8eebf91350c6a81271149f4778` |

| Frozen original source | SHA-256 |
|---|---|
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `crates/yu-solver/src/candidate_context.rs` | `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e` |
| `crates/yu-solver/src/candidate_effect.rs` | `70c42056a1041d54f88f16d7712875e3acf9ef7649b99a34bc990ff19f04936f` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `crates/yu-solver/src/candidate_scheme.rs` | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` |
| `crates/yu-solver/src/candidate_scope.rs` | `9fdb36b4bbd66d702fbd3fcfaf593bfbc5dce0c52ff3252442aeb998bbb52c2a` |
| `crates/yu-solver/src/candidate_source.rs` | `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| `notes/design/2026-10-24-birth-level-scc-intrusion.md` | `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae` |

## Complete origin-audit program

```lean
import Lean.Elab.Command
import Lean.Util.CollectAxioms
import YulangClosure.NativeInferenceProgress
set_option pp.fullNames true
set_option pp.universes false
open Lean Elab Command
run_cmd do
  let moduleName := `YulangClosure.NativeInferenceProgress
  let roots : Array Name := #[
    `YulangClosure.NativeInferenceProgress.source_context_atom,
    `YulangClosure.NativeInferenceProgress.admitted_context_atom,
    `YulangClosure.NativeInferenceProgress.filter_bound_identity,
    `YulangClosure.NativeInferenceProgress.decompose_fibers_identity,
    `YulangClosure.NativeInferenceProgress.decompose_children_atom,
    `YulangClosure.NativeInferenceProgress.value_port_context_atom,
    `YulangClosure.NativeInferenceProgress.total_next,
    `YulangClosure.NativeInferenceProgress.total_reject,
    `YulangClosure.NativeInferenceProgress.total_finish,
    `YulangClosure.NativeInferenceProgress.total_bind,
    `YulangClosure.NativeInferenceProgress.atomic_scan_clean,
    `YulangClosure.NativeInferenceProgress.replay_scan_clean,
    `YulangClosure.NativeInferenceProgress.shallow_scan_clean,
    `YulangClosure.NativeInferenceProgress.consume_context_closure,
    `YulangClosure.NativeInferenceProgress.expand_consumes,
    `YulangClosure.NativeInferenceProgress.native_expand_context_closure,
    `YulangClosure.NativeInferenceProgress.signature_fiber_atom,
    `YulangClosure.NativeInferenceProgress.post_atom,
    `YulangClosure.NativeInferenceProgress.transport_atom,
    `YulangClosure.NativeInferenceProgress.replay_context_shallow,
    `YulangClosure.NativeInferenceProgress.renamed_atom,
    `YulangClosure.NativeInferenceProgress.step_invariant,
    `YulangClosure.NativeInferenceProgress.reachable_context_closure,
    `YulangClosure.NativeInferenceProgress.atom_extension,
    `YulangClosure.NativeInferenceProgress.shallow_extension,
    `YulangClosure.NativeInferenceProgress.invariant_extension,
    `YulangClosure.NativeInferenceProgress.growing_context_closure,
    `YulangClosure.NativeInferenceProgress.fresh_prefix_constructed
  ]
  let env ← getEnv
  let some moduleIndex := env.getModuleIdx? moduleName
    | throwError "module missing: {moduleName}"
  let mut theorems : Array Name := #[]
  let mut total : Nat := 0
  for (name, info) in env.constants.toList do
    if env.getModuleIdxFor? name == some moduleIndex then
      let kind : String ← match info with
        | .thmInfo _ =>
            theorems := theorems.push name
            pure "theorem"
        | .axiomInfo _ => throwError "project axiom: {name}"
        | .defnInfo _ => pure "definition"
        | .opaqueInfo _ => pure "opaque"
        | .inductInfo _ => pure "inductive"
        | .ctorInfo _ => pure "constructor"
        | .recInfo _ => pure "recursor"
        | .quotInfo _ => pure "quotient"
      total := total + 1
      logInfo m!"NATIVE_PROGRESS_AUDIT_BEGIN {kind} {name}"
      let id := mkIdent name
      elabCommand (← `(#check @$id))
      elabCommand (← `(#print axioms $id))
      for ax in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "unapproved axiom in {name}: {ax}"
      logInfo m!"NATIVE_PROGRESS_AUDIT_END {name}"
  for root in roots do
    unless theorems.contains root do
      throwError "missing originating theorem: {root}"
  logInfo m!"NATIVE_PROGRESS_AUDIT_TOTAL declarations={total} theorems={theorems.size} required={roots.size}"
```

## Complete originating declaration/type/axiom census

The complete raw audit output remains unchanged at
`/workspace/scratch/e3678bef96db/global-termination-r2/check-13-origin-audit.log`.
Its exact SHA-256 appears in the artifact table above. It contains every actual
originating declaration's complete type and transitive axiom report. The
machine-readable census is
`/workspace/scratch/e3678bef96db/global-termination-r2/origin-census.json`.
The reproducible audit source is
`/workspace/scratch/e3678bef96db/global-termination-r2/project/NativeProgressOriginAudit.lean`.
The root owns copying that standalone audit source into the repository.

| Census category | Count |
|---|---:|
| All originating declarations | 117 |
| All originating theorem constants, including private/generated | 50 |
| Required authored theorem roots | 28 |
| Theorems with no axioms | 16 |
| Theorems using only `propext` | 8 |
| Theorems using `propext, Quot.sound` | 21 |
| Theorems using `propext, Classical.choice, Quot.sound` | 5 |
| Project or unapproved axioms | 0 |
| Final audit warnings | 0 |

Raw stdout is retained only in scratch, as required by
`rules/git-concurrency.md`. The commands, exits, failure history, complete audit
program and evidence hashes above remain part of this handoff.

## Freeze receipt

The delivered proof bytes equal the final checker-audited isolated module. Original source/dependency inputs were unchanged. The root may independently review/integrate these exact three authorized paths. This leaf has stopped all edits and checks after writing this frozen handoff; it makes no claim of independent review, root import coverage, production conformance or original parent closure. A final scratch `delivery-receipt.json` records the three delivered file hashes without a self-referential handoff hash.
