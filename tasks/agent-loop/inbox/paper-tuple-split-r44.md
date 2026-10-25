# R44 tuple-split leaf handoff r1 — FIRST BUILD FAILED, writes stopped

Sprint `PAPER-TUPLE-SPLIT-EXECUTION-20261026/r44`, contract r1 SHA-256
`3847c517fd19167519b7a108e0b54b996c23f5546e7286390d7c46a5a7cfb6d2`.
Contract read and hash-verified in primary checkout; absent in baseline worker checkout.
Assignment `/root/r44_tuple_split_proof`, registered `lean_prover`; exact observed
model/effort UNKNOWN, child-session ID UNKNOWN. Parent supplied isolated baseline
`82b601fe852da2bb4406783ef5cb96ea0d22ae7d` at
`/tmp/yulang-r44-tuple-split-prover`; no Git command run. Sole author this worker;
no descendants. Primary owns verification/review/integration and other paths.

Outcome class: **constructed candidate with FAILED module check**. No theorem is
delivered as proved. No printed theorem-kind/type or axiom audit receipt exists.
No source/native, whole-parent, independent-review or production closure.

## Failure and exact remaining goal

The first focused build exited 1. Its only reported Lean error was
`YulangClosure/PaperTupleSplitExecution.lean:25:11` in the nil branch of
`YulangClosure.PaperTypes.PaperTupleSplitExecution.prefixReplacement_tail`:

```lean
rho : Nat → Value
n : Nat
⊢ prefixReplacement [] rho ([].length + n) = rho n
```

`rfl` failed because `0 + n = n` is not definitional for a variable `n`.
The complete error, every dependency warning, all new-module linter warnings,
stdout/stderr, launch command and exit are preserved in the raw log. No timeout.
The checker continued elaboration and reported no further errors, but that is
not a clean module receipt or an axiom audit. No target `.olean` was produced.

At this first failure, construction and checker work stopped, as the frozen
contract requires. Primary acknowledged the failure and instructed preservation;
no suggested repair was executed. Suggested next exact change, **unexecuted and
requiring a new primary packet**, is replacing that nil branch by
`by simp only [List.length_nil, Nat.zero_add, prefixReplacement]` (or its tactic
body). All 27 public declarations still need a successful build and full audit.
The current worker has no remaining execution authority despite unused caps.

## Source correspondence and intended bounded construction

Read root AGENTS/base map, goal-driven sprint rules, Lean skill and its actual
`references/sources.md` and `references/execution.md`, manuscript opening source-owner
correction and syntax/typing :210–240, split :308, finite contexts :1012–1026,
and original precise one-step preservation/display simulation :1860–1877.
The manuscript remains a research construction, not blanket semantic approval.
Its whole source domain and shared witnesses are not replaced by this fragment.

Actual definitions read: `extendTupleEnvironment`, `lookupTypeEnvironment`, six
mutual execution typing judgments, `argsSyntax`, R28 `TermSubstitutionTyped`,
`liftTermSubstitution`, simultaneous `replaceTermComputation` and
`termSubstituteComputation`, R35 `step`/`preservation`, R36 `StateTyped`,
`StackTyped`, `plug`, `erase`, priority operator, evidence and erasure relations.
Supporting R35/r3 and R36/r2 handoffs were read. Contract's stale R28 navigation
`paper-typing-subst-r28.md` is absent; primary supplied the actual
`tasks/agent-loop/inbox/paper-term-substitution-r28.md`, read from primary checkout.
Source module hashes, rather than those handoff claims, govern this construction.

New namespace: `YulangClosure.PaperTypes.PaperTupleSplitExecution` (`PTS` below).
`prefixReplacement` consumes a vector in de Bruijn index order and then the outer
map. `tupleReplacement values rho` reverses source tuple order once. Thus index 0
selects the last tuple value; past arity it uses the decremented outer map.
Values are inserted once through R28 simultaneous substitution; no sequential
single-substitution loop implements split. The candidate proves typed reversed
component lists and constructs the actual typed replacement vector from
`ValuesTyped` plus an arbitrary typed tail, then instantiates the tail with
identity typing. D, graph environment, outer environment and result stay shared.

Intended main source signature (not printed by Lean):

```lean
PTS.preservation : ∀ {d : DeclarationTable} {g : GraphEnvironment}
  {e : TypeEnvironment} {c next : Computation} {result : Ty},
  PaperComputationTyped d g e c result → PTS.step c = some next →
  PaperComputationTyped d g e next result
PTS.control_preservation : ∀ {d : DeclarationTable} {g : GraphEnvironment}
  {e : TypeEnvironment} {s next : PaperCoreControl.State} {result : Ty},
  PaperCoreControl.StateTyped d g e s result → PTS.controlStep s = some next →
  PaperCoreControl.StateTyped d g e next result
```

`split_applicable` retains the accepted raw split judgment, its explicit
`binders.length = types.length` premise by inversion, and exact value/type arity.
Runtime `splitStep` checks binders against values and returns `none` for mismatch
or another head/value constructor. Its successful equation is exactly R28's
simultaneous replacement. `step` first consumes R35's existing result, offering
split only on `none`; `step_extends` is the conservative-extension candidate.
`controlStep` first consumes R36's existing result, retaining push/pop/delegate
priority and stored frame order, then offers split. Its evidence preservation
reuses R36 for old transitions. The new context relation lifts every extended
principal step through all ordinary finite let frames. Erasure is stutter or one
context step; `trace_preservation` targets arbitrary finite internal transitions
with one fixed final result. Typing is the accepted extrinsic judgment.

Five raw discriminators are constructed: heterogeneous integer/boolean order;
empty tuple preserving the outer variable; replacement of an external variable
beneath one let binder; runtime arity mismatch; simultaneous replacement versus
two sequential single replacements that would rewrite an inserted external
variable. Their source terms are frozen but no clean proof/audit is claimed.

Represented candidate cases: typed ordinary tuple split over all R28-supported
nested bodies and open values, arbitrary shared D/Xi/Γ/result; all existing R35
cases (including required/optional record behavior); all R36 finite ordinary let
frames and transitions. Omitted: other split patterns, switch/choose/type-application
execution, full Call/wrap, handlers/mapop/wait and other frames, raw requests,
recursive allocation/guarded heap construction, current-port diagrams, residual
graphs, native simulation, whole executor, inference A/B and production.
R39's unresolved input-port decision was neither read as authority nor used.
Rust `program.rs`/`machine.rs` bridges remain `NO_SAFE_CODE_SLICE`.

## Audit draft and actual results

The skill's `audit_source` was loaded through `python3 -B`/`runpy` (bytecode writes
disabled), with its whitelist tightened to `#[propext, Quot.sound]`.
The leased audit draft checks declaration kind, full `#check @...` type,
`#print axioms`, and `Lean.collectAxioms` for every public theorem. The CLI was
not used because it adds temporary paths and version/build calls beyond the
fixed manual sequence. `validate_audit` was not run because no audit output exists.

Every name below has kind/type/axiom status **NOT_RUN**, not an empty axiom set.
Fully qualified prefix is `YulangClosure.PaperTypes.PaperTupleSplitExecution.`:

- `prefixReplacement_tail`
- `tupleReplacement_tail`
- `values_length`
- `tupleReplacement_typed`
- `tupleReplacement_identity_typed`
- `splitStep_eq`
- `splitStep_arity_mismatch`
- `split_applicable_of_components`
- `split_applicable`
- `split_preservation`
- `step_extends`
- `splitStep_to_step`
- `preservation`
- `controlStep_extends`
- `controlStep_evidence`
- `evidence_preservation`
- `control_preservation`
- `old_context_step`
- `plug_step`
- `evidence_erasure`
- `erasure`
- `trace_preservation`
- `example_order`
- `example_empty`
- `example_external_under_binder`
- `example_arity_mismatch`
- `example_not_sequential`

Source scan of the actual local import cone inspected 11 modules and found no
`sorry`, `admit`, project `axiom`, unsafe/native checker bypass or `skipKernelTC`
source matches. That scan supplements no indirect axiom evidence here.

## Commands and resources

Read-only `elan which lake` resolved the installed native executable
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`.
Each command cwd was `/tmp/yulang-r44-tuple-split-prover/notes/theory/lean`,
with `LEAN_NUM_THREADS=1`; project compiler limits `-j1 -M1024` unchanged.

| Call | Native Lake arguments | Exit | Wall seconds |
| --- | --- | --- | --- |
| 1 | `--version` | 0 | 0.408772839 |
| 2 | `env lean --version` | 0 | 0.070939809 |
| 3 | `--no-cache build +YulangClosure.PaperTupleSplitExecution` | 1 | 33.575594611 |

Versions: Lake `5.0.0-src+eb6cafb (Lean version 4.35.0)`; Lean `4.35.0`,
`x86_64-unknown-linux-gnu`, release commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. All version pins matched.
Total **3/10** literal native invocations, **34.055307259/120** checker wall
seconds, each below 60 seconds; no retry or timeout. The actual worker launch
receipt belongs to primary. Conservatively reserve the whole 1200-second active
grant unless primary derives a tighter actual interval; no active-time reset or
renewal occurred. The raw log starts at `2026-10-25T20:25:26.191573+00:00` after
source reads, and records call 3 at `2026-10-25T20:28:05.960802+00:00`.

## Frozen inputs and outputs

All ten original source/config hashes were verified before and after the failed
build and remain unchanged:

| Path | SHA-256 |
| --- | --- |
| `docs/yulang-operational-type-safety-ja.tex` | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |
| `notes/theory/lean/YulangClosure/PaperTermSubstitution.lean` | `a4f87f9604c03beefdc44de5d45fcd9f5924ca9580c75edf353cf267e69a0d4f` |
| `notes/theory/lean/YulangClosure/PaperCoreStep.lean` | `503f81c162f7b9ceb0f7d27aa9796b8d7010345653267c675267ce14214c57e9` |
| `notes/theory/lean/YulangClosure/PaperCoreControl.lean` | `261d6a77438eec1a32e0299b73583899204ed7c2fe0590b819ecd3fd5b89876e` |
| `notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean` | `e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932` |
| `notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean` | `3b1588bff2d28a3db7aa241c930495b84f090e880ad49ac8fb2d593d54943d41` |
| `notes/theory/lean/YulangClosure.lean` | `b4b04a6a3b2cc0c7c330e93195539f7344612347c9b51b7f2dc8cf0be4994454` |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `notes/theory/lean/lakefile.toml` | `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194` |
| `notes/theory/lean/lake-manifest.json` | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |

Frozen worker outputs:

| Path | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/PaperTupleSplitExecution.lean` | `17a5f6f6fb4c6f53031c0a28ab0fafed136a78bd84497c5860293d1a329e255c` |
| `notes/theory/lean/.lake/R44Audit.lean` | `83c6a0f623d7c9a2a1761987bd6717a3dccd81e7a614b0fd5b2b3f736f559a0b` |
| `tasks/agent-loop/inbox/paper-tuple-split-r44-worker.log` | `e06c4152e5a00c7efa98262e630f3d5de9b435e0f4fa722bd9a18d49c5c521c4` |

Module: 337 lines / 15016 bytes. Audit draft: 23741 bytes. Complete raw log:
231767 bytes, untruncated on disk. Dedicated generated outputs are
under `notes/theory/lean/.lake/build`; dependencies built successfully, new module
failed. New-module setup JSON SHA-256
`855129858c0e9430ce162b30e143ffc9006fffe7d7fc63b78e52100dd8e0c7d9`.
There is no new module `.olean`/`.ilean`/C result to promote. Existing nonbuild
`.lake` scratch files were preserved; only the leased R44 audit was added there.

## Parent application, owner and cessation

The intended application is tuple-split local computation preservation plus
finite ordinary let-context typing/erasure in the manuscript parent. **That
application is not established by this FAILED module.** First remaining premise:
close `prefixReplacement_tail`'s nil goal above, rebuild and audit the frozen
candidate under a new primary-issued repair packet. Owner: Luna's next proof
packet. No mathematical counterexample or source mismatch was found.

Even after a successful bounded repair, the next parent premise belongs to Luna's
full-state/source/control lane: connect actual full-paper states and reductions
to these ordinary finite-let transitions, then establish current-port inclusion
and residual derivation-graph preservation. Omitted frames/principal cases,
source/native correspondence, inference A/B and production remain OPEN.
Independent review is not run. Integration is not authorized by this receipt.

Final read-only `/proc` executable scan found no `lean`, `lake` or `elan`
process. Construction/checker processes stopped at failure. Writes were confined
to the leased module, audit, log, this handoff and dedicated `.lake/build`.
No Git, tests/fixtures/expectations, root import, compiler/Rust, dependencies,
manifest/toolchain/config, shared task/status/index, questions, network/install,
other-worker edits, children or third-party contact. No unresolved descendant
lease. After this final handoff write at `2026-10-25T20:30:26.155018+00:00`, **ALL WORKER WRITES STOPPED**.
Primary may intake the frozen failure and arrange the next bounded packet.
