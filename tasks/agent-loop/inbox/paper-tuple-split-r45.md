# R45 tuple-split repair handoff r1 — checked leaf result; writes stopped

Sprint `PAPER-TUPLE-SPLIT-REPAIR-20261026/r45`; frozen contract SHA-256
`2579b7cd0cba6c5c5cb494a39b02b97e0c3ddebbf31f1f475b44c91f6b096175`.
Worker `/root/r45_tuple_split_proof`, registered `lean_prover`; observed model/effort
UNKNOWN. No descendants. Primary supplied detached checkout `/tmp/yulang-r45-tuple-split-prover` at baseline
`7a2e033a703854a6a9fd6011d1cb4896783a1f24`; direct `.git` metadata read verified
HEAD, without Git invocation. This worker owns the exact leased candidate, audit,
log, this handoff and dedicated `.lake/build`; other workers' paths were untouched.
R44 remains **FAILED**; its candidate/evidence bytes are unchanged.

Outcome class: **checker-accepted bounded paper theorem candidate**, pending
Luna's isolated root build/audit and fresh independent review. This worker does
not self-certify source correspondence, independent review or production.

The only source edit from the R44 seed is `prefixReplacement_tail`'s nil branch:

```lean
| nil => simp only [List.length_nil, Nat.zero_add, prefixReplacement]
```

The seed was copied to the leased module, not modified in place. Audit draft was
copied byte-for-byte; no root import, accepted-source or other theorem change.
Pre/post pins, exact one-line delta, audit identity and 27-public-theorem coverage
all verified. Focused no-cache build passed (12 jobs). Its complete dependency
and unused-simp linter warnings remain in the raw log; no warning was disabled.

## Original source, exact definitions and application

Read the pinned operational manuscript's opening source-owner correction;
syntax/value/computation typing :210–240 (tuple split :229), simultaneous split
reduction :308, finite context lemma :1012–1026, and original precise one-step
preservation/display simulation :1860–1877. The parent preserves value type A,
current-port inclusion and a residual typed derivation graph or declared
latent/reentry instance, allowing fresh immutable graph extension and uniform
renaming. The manuscript is a research construction, not blanket semantic
approval; its current source-owner correction expressly leaves whole-language
source correspondence open. Skill references `sources.md` and `execution.md`,
root/base maps, sprint rules, design authority and inference principles were read.

Exact namespace `YulangClosure.PaperTypes.PaperTupleSplitExecution` (PTS).
Actual accepted `extendTupleEnvironment types e = types.reverse ++ e`, raw
`PaperComputationTyped.split` (explicit binder/type arity), R28
`TermSubstitutionTyped`, binder lifting, simultaneous `replaceTermComputation`
and `termSubstituteComputation`, R35 `step`/`preservation`, and R36 `StateTyped`,
`StackTyped`, `controlStep`, `plug`, `erase` and evidence were inspected.
PTS builds the concrete typed replacement from typed components and typed tail;
`TermSubstitutionTyped` is not asserted as an unproved concrete instance.

Printed main types (full qualification and all 27 full types are in the raw log):

```lean
PTS.split_applicable : ∀ {d : DeclarationTable} {g : GraphEnvironment}
  {e : TypeEnvironment} {values : List Value} {binders : List TermName}
  {body : Computation} {result : Ty},
  PaperComputationTyped d g e (.split (.tuple values) binders body) result →
  ∃ next, PTS.splitStep (.split (.tuple values) binders body) = some next ∧
    PaperComputationTyped d g e next result
PTS.preservation : ∀ {d : DeclarationTable} {g : GraphEnvironment}
  {e : TypeEnvironment} {c next : Computation} {result : Ty},
  PaperComputationTyped d g e c result → PTS.step c = some next →
    PaperComputationTyped d g e next result
PTS.control_preservation : ∀ {d : DeclarationTable} {g : GraphEnvironment}
  {e : TypeEnvironment} {s next : PaperCoreControl.State} {result : Ty},
  PaperCoreControl.StateTyped d g e s result → PTS.controlStep s = some next →
    PaperCoreControl.StateTyped d g e next result
PTS.trace_preservation : ∀ {d : DeclarationTable} {g : GraphEnvironment}
  {e : TypeEnvironment} {s last : PaperCoreControl.State} {result : Ty},
  PaperCoreControl.StateTyped d g e s result → PTS.Trace s last →
    PaperCoreControl.StateTyped d g e last result
```

Application to original parent: the typed tuple-split structural-elimination
case now supplies a well-typed simultaneous replacement, and arbitrary finite
ordinary let stacks preserve the same shared D/Xi/Γ and final result. R35 priority
and R36 push/pop/delegate priority, stored body order, existing successful steps
and erasure are retained by the checked extension lemmas. Erasure is stutter or
one extended ordinary-let context step. No closed-value hypothesis was added;
open values, arbitrary shared declaration/graph/outer environments and all
R28-supported nested bodies remain quantified.

First remaining parent premise: establish a relation from the actual corrected
full-paper states/reductions to these ordinary finite-let transitions, then prove
current-port inclusion and residual derivation-graph preservation. Owner: Luna's
full-state/source/control lane. This leaf has no authority to choose R39's input
port convention. Mathematical local preservation is not full-parent closure.

Represented: tuple split, reverse binder order, decrementing outer tail,
R28 simultaneous insertion and binder transport; all existing R35 cases
(including required/optional records); R36 finite ordinary let frames and traces.
All five falsifiers are audited: heterogeneous order, empty tuple/outer variable,
external replacement under let binder, raw arity mismatch, and simultaneous
versus sequential substitution. Omitted: other split patterns, switch/choose/
type-application execution, full Call/wrap, handlers/mapop/wait and other frames,
raw requests, recursive allocation/guarded heaps, current ports, residual graphs,
source/native simulation, inference A/B, whole executor, Rust and production.
Implementation remains `NO_SAFE_CODE_SLICE`.

## Actual execution and complete axiom audit

Installed native executable:
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`.
All cwd `/tmp/yulang-r45-tuple-split-prover/notes/theory/lean`; `LEAN_NUM_THREADS=1`; unchanged project `-j1 -M1024`.
Lake `5.0.0-src+eb6cafb (Lean version 4.35.0)`; Lean `4.35.0`,
`x86_64-unknown-linux-gnu`, release commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.

| Call | Native Lake arguments | Exit | Monotonic wall seconds |
| --- | --- | --- | --- |
| 1 | `--version` | 0 | 0.408157008 |
| 2 | `env lean --version` | 0 | 0.070710254 |
| 3 | `--no-cache build +YulangClosure.PaperTupleSplitExecution` | 0 | 29.055672528 |
| 4 | `env lean -j1 -M1024 .lake/R45Audit.lean` | 0 | 3.311624558 |

Total **4/4 calls, 32.846164348/90 checker seconds**;
each <60 seconds, no retry/timeout. Exact launch command/cwd/UTC/monotonic start,
raw merged stdout/stderr, exit and duration are in the complete untruncated log.
The fixed four-call sequence precluded the helper CLI's extra calls/scratch;
its actual `validate_audit` was loaded with `python3 -B`/`runpy` and passed all
27 ordered type/complete-axiom blocks, tightened to `{propext, Quot.sound}`.
The unchanged Lean audit independently checks `.thmInfo` and `Lean.collectAxioms`
against the same strict set. Thus every public theorem has a real printed type
and complete `#print axioms` receipt; these are standard axioms, not axiom-free.

All names below have fully qualified prefix
`YulangClosure.PaperTypes.PaperTupleSplitExecution.`:

| Audited theorem | Complete axiom list |
| --- | --- |
| `prefixReplacement_tail` | `[propext]` |
| `tupleReplacement_tail` | `[propext]` |
| `values_length` | `[propext, Quot.sound]` |
| `tupleReplacement_typed` | `[propext, Quot.sound]` |
| `tupleReplacement_identity_typed` | `[propext, Quot.sound]` |
| `splitStep_eq` | `[propext, Quot.sound]` |
| `splitStep_arity_mismatch` | `[propext, Quot.sound]` |
| `split_applicable_of_components` | `[propext, Quot.sound]` |
| `split_applicable` | `[propext, Quot.sound]` |
| `split_preservation` | `[propext, Quot.sound]` |
| `step_extends` | `[propext, Quot.sound]` |
| `splitStep_to_step` | `[propext, Quot.sound]` |
| `preservation` | `[propext, Quot.sound]` |
| `controlStep_extends` | `[propext, Quot.sound]` |
| `controlStep_evidence` | `[propext, Quot.sound]` |
| `evidence_preservation` | `[propext, Quot.sound]` |
| `control_preservation` | `[propext, Quot.sound]` |
| `old_context_step` | `[propext, Quot.sound]` |
| `plug_step` | `[propext, Quot.sound]` |
| `evidence_erasure` | `[propext, Quot.sound]` |
| `erasure` | `[propext, Quot.sound]` |
| `trace_preservation` | `[propext, Quot.sound]` |
| `example_order` | `[propext, Quot.sound]` |
| `example_empty` | `[propext, Quot.sound]` |
| `example_external_under_binder` | `[propext, Quot.sound]` |
| `example_arity_mismatch` | `[propext, Quot.sound]` |
| `example_not_sequential` | `[propext, Quot.sound]` |

The actual 11-module local import cone was source-scanned for `sorry`, `admit`,
project `axiom`, `unsafe`, `skipKernelTC`, native/reduction bypasses: no matches.
Cone hashes are preserved in the log; source scan supplements the kernel audits.
No tests, network, installs, configuration/dependency changes, Git, nested CLI,
children or third-party contact occurred.

## Frozen pins and artifacts

Original source/configuration and R44 evidence hashes, unchanged pre/post:

| Path | SHA-256 |
| --- | --- |
| `docs/yulang-operational-type-safety-ja.tex` | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |
| `notes/theory/lean/YulangClosure.lean` | `b4b04a6a3b2cc0c7c330e93195539f7344612347c9b51b7f2dc8cf0be4994454` |
| `notes/theory/lean/YulangClosure/PaperCoreControl.lean` | `261d6a77438eec1a32e0299b73583899204ed7c2fe0590b819ecd3fd5b89876e` |
| `notes/theory/lean/YulangClosure/PaperCoreStep.lean` | `503f81c162f7b9ceb0f7d27aa9796b8d7010345653267c675267ce14214c57e9` |
| `notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean` | `e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932` |
| `notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean` | `3b1588bff2d28a3db7aa241c930495b84f090e880ad49ac8fb2d593d54943d41` |
| `notes/theory/lean/YulangClosure/PaperTermSubstitution.lean` | `a4f87f9604c03beefdc44de5d45fcd9f5924ca9580c75edf353cf267e69a0d4f` |
| `notes/theory/lean/lake-manifest.json` | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |
| `notes/theory/lean/lakefile.toml` | `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194` |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `tasks/agent-loop/inbox/paper-tuple-split-r44-audit-draft.lean` | `83c6a0f623d7c9a2a1761987bd6717a3dccd81e7a614b0fd5b2b3f736f559a0b` |
| `tasks/agent-loop/inbox/paper-tuple-split-r44-candidate.lean` | `17a5f6f6fb4c6f53031c0a28ab0fafed136a78bd84497c5860293d1a329e255c` |
| `tasks/agent-loop/inbox/paper-tuple-split-r44.md` | `b7b03d7bc9ff4e42a442903e8808011e7d285263155bd3074e49c20dc96fd911` |

Delivered module `notes/theory/lean/YulangClosure/PaperTupleSplitExecution.lean` SHA-256
`7bc13a41a0333d885b91291a7fbb1ef18302a94c79a34f21469dbae19d76f84d` (15073 bytes).
Audit `notes/theory/lean/.lake/R45Audit.lean` SHA-256
`83c6a0f623d7c9a2a1761987bd6717a3dccd81e7a614b0fd5b2b3f736f559a0b` (23741 bytes; byte-identical to R44 audit seed).
Complete raw log `tasks/agent-loop/inbox/paper-tuple-split-r45-worker.log` SHA-256
`1afc81552200eb4084116a2ead9aca0dda162beba2231625f13f10cba4ffb130` (261936 bytes).

Dedicated generated build: 88 files / 25824908 bytes.
Target-generated artifact hashes:

| Path | SHA-256 |
| --- | --- |
| `notes/theory/lean/.lake/build/ir/YulangClosure/PaperTupleSplitExecution.setup.json` | `d48f9dd5446f1a3324694b158c33966738947f0bf65ba276611bbf4d6ca6040f` |
| `notes/theory/lean/.lake/build/ir/YulangClosure/PaperTupleSplitExecution.c` | `4437466a04a629cb4490b49ed6df3fd216a25810c1c609316940895e54499c8a` |
| `notes/theory/lean/.lake/build/ir/YulangClosure/PaperTupleSplitExecution.c.hash` | `c12d6bd9ca4a352aecfd599c63dbb7b44f54dc6981cfc0d7c43a14379193f98a` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/PaperTupleSplitExecution.ilean.hash` | `599c4744bcd366eaace697f0b2f3b1160c5961b2c6a52b50c5c338a7f528dc86` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/PaperTupleSplitExecution.ilean` | `ff93cda5f5d0ed479b28a4ae6fb90ef5cf96d851e851f7b171ae504a5fe45649` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/PaperTupleSplitExecution.olean.hash` | `3a777c56406c2fbdb7b148225a6630ecd3ff259a3bdc8227c586c16ff54cf21d` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/PaperTupleSplitExecution.trace` | `b5d35832e89d9f379f8388077061f3aec1d66a45763d9e8f3aff4197fff1cf85` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/PaperTupleSplitExecution.olean` | `27be4f5db2276d85898d698b0e637685fefd7c8dd0b6ede3733c2b2adfaa3a34` |

## Cessation and exact handoff

All four native calls exited; final read-only `/proc` executable scan found no
Lean/Lake/Elan processes. No descendants or unresolved descendant leases.
The original source, audit and raw log are now frozen. No more checker calls or
repairs are authorized. Conservatively reserve the full **600-second active
grant**; no reset or renewal. Exact active launch receipt remains with primary.
This final handoff write is the last worker write, UTC **2026-10-25T20:36:53.605407+00:00**.
**ALL WORKER WRITES STOPPED** after this handoff write; source, audit, raw log,
handoff and generated outputs are handed to Luna as frozen bytes.

Next owner action: Luna verifies hashes/one-line diff in its separate pinned
checkout, performs only its authorized four-call root/audit sequence, then sends
the frozen component for fresh independent review. Acceptance/integration/Git
and all shared status changes remain solely with Luna.
