# R36/r2 leaf handoff r1 — bounded control checked, writes stopped

Worker `/root/r36_r2_registered_lean_prover`; runtime session UUID UNKNOWN.
Requested registered `lean_prover`, role default; explicit requested and observed
model/effort UNKNOWN. Admission/cache acknowledgement `eab8ee945`; source baseline
`658f69056`; r2 contract SHA-256
`84c679419e1fd4cb75f4d16e2c2b9c537f0f10e5b29ac6d5fe885e697079bfe2`.
Parent contract SHA-256
`e3427e6f06bc49e20d9f43a40c2dacbc764337acfe0ee98f0377845c0f0be784`.
Original r1 author `/root/r36_registered_lean_prover` retained; this worker repairs
only `controlStep_evidence`. No descendants or independent review appointments.

Outcome: the focused build and all eight theorem-kind/type/axiom audits passed.
This is checker acceptance of bounded paper-syntax mathematics. Fresh independent
review, full source/native correspondence and production promotion are not supplied.
No mathematical counterexample or strengthened hypothesis was introduced.

## Source, correction and unchanged parent

Governing manuscript `docs/yulang-operational-type-safety-ja.tex`: opening source-owner
resume correction :55–62; execution typing :203–240; ordinary reductions :305–316;
active-child rule :331–334; typed context decomposition :1014–1026; original precise
one-step preservation/display simulation :1860–1875. The opening correction leaves
full source correspondence unresolved; the research manuscript is no compiler semantic
approval. The original parent preserves one result type and current-port diagram
inclusion through residual derivation graphs or declared latent/reentry instances,
allowing immutable fresh graph extension and uniform binder renaming.

Read root AGENTS/base operating map, goal-driven rules, current state/README, both
contracts, Lean skill and source/execution references, current proof, actual paper
raw computation/typing constructors, R28 term substitution, R35 partial step and
its handoff/review, and the separate `Original` boundary reference. R1's 19 unsupported
head elaboration failures remain frozen in its complete log; no r1 evidence was replaced.

## Exact repair and checked declarations

Only the former generic delegate fallback changed. Explicit `force`, `unionCase`,
`unroll`, `field`, and `lookup` branches retain their actual named head in the
mapped-success equation, obtain `Option.map_eq_some_iff` evidence and construct
`ControlStepEvidence.delegate`. Every other unsupported head is contradicted by
simplifying `controlStep` and `PaperCoreStep.step` at its alleged success equation.
The existing let-push and return-pop proofs, all definitions and every theorem
statement are unchanged. No helper or new assumption was added.

Namespace: `YulangClosure.PaperTypes.PaperCoreControl`. The complete actual fully qualified printed types and
`#print axioms` output for every theorem are preserved in the worker log. Principal
printed types, with namespace aliases used only here for readability:

```lean
PCC.preservation : ∀ {d : DeclarationTable} {g : GraphEnvironment}
  {e : TypeEnvironment} {s s' : PCC.State} {result : Ty},
  PCC.StateTyped d g e s result → PCC.controlStep s = some s' →
  PCC.StateTyped d g e s' result
PCC.erasure : ∀ {s s' : PCC.State}, PCC.controlStep s = some s' →
  PCC.erase s = PCC.erase s' ∨ PCC.PaperLetContextStep (PCC.erase s) (PCC.erase s')
```

Every declaration is a theorem; every complete axiom set follows:

| Fully qualified theorem | Complete axiom set |
| --- | --- |
| `YulangClosure.PaperTypes.PaperCoreControl.controlStep_evidence` | `propext`, `Quot.sound` |
| `YulangClosure.PaperTypes.PaperCoreControl.plug_typed` | none |
| `YulangClosure.PaperTypes.PaperCoreControl.erase_typed` | none |
| `YulangClosure.PaperTypes.PaperCoreControl.evidence_preservation` | `propext`, `Quot.sound` |
| `YulangClosure.PaperTypes.PaperCoreControl.preservation` | `propext`, `Quot.sound` |
| `YulangClosure.PaperTypes.PaperCoreControl.plug_step` | `propext`, `Quot.sound` |
| `YulangClosure.PaperTypes.PaperCoreControl.evidence_erasure` | `propext`, `Quot.sound` |
| `YulangClosure.PaperTypes.PaperCoreControl.erasure` | `propext`, `Quot.sound` |

`StateTyped` existentially supplies the active head's intermediate type, keeping
arbitrary shared `D/Xi/Γ` (`d/g/e`) and one final `result`; `StackTyped` composes
actual let bodies under their corresponding binder types. It does not identify
intermediate and final types or define typing as safety. R28 capture-avoiding
substitution handles pop, R35 preservation handles delegated heads, and `plug_step`
retains every actual pending frame in innermost-first order.

Represented transitions: arbitrary actual raw paper heads conditionally on success;
finite ordinary let frames; let push; return pop; R35 force/delay, both union
injections, unroll/roll, field/record and lookup/record. Required/optional records
retain R35 behavior. Push erases identically; pop and delegated steps lift through
all pending let frames. `none` means no transition provided by the partial operator.
Omitted: scope/expose/handle/mapop/wait frames, requests, full calls/wrap, handlers,
effects, recursive allocation, heap graphs, administrative steps, full evaluation
and termination. The separate `Original` syntax is not transferred to paper syntax.

## Parent application and precise remaining owner

For any represented transition `hs` from a paper typed finite-let state `ht`,
`YulangClosure.PaperTypes.PaperCoreControl.preservation ht hs` supplies the same final state result type;
`YulangClosure.PaperTypes.PaperCoreControl.erase_typed` applied to that result supplies the ordinary erased
computation typing. `YulangClosure.PaperTypes.PaperCoreControl.erasure hs` supplies exactly stuttering or
R35 principal reduction beneath all ordinary let frames. This establishes the
manuscript's bounded ordinary-let context component using its actual computation
and typing constructors; it does not establish the full manuscript state theorem.

First remaining premise/owner: Luna's source/control proof lane must relate actual
full paper machine states/steps to these finite-let states/transitions and transport
their typing through current-port diagram inclusion and residual derivation graphs.
That full state/control/current-port/residual-graph bridge is not supplied here.
Omitted frames, whole source/native correspondence, inference A/B and production
remain OPEN. No compiler slice is authorized (`NO_SAFE_CODE_SLICE`). Next in-scope
handoff: Luna verifies/adjudicates and assigns a fresh non-author source reviewer;
this leaf has no further construction or checker action. No mutual worker TODO.

## Commands, versions and evidence

Native executable for both r2 commands:
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`.
Cwd `notes/theory/lean`, `LEAN_NUM_THREADS=1`; commands serialized:

1. `lake build +YulangClosure.PaperCoreControl`: exit 0,
   0.43902527700265637 seconds. Full 218742-byte build output retained, including
   replayed dependency deprecation/unused-variable/simp warnings.
2. `lake env lean -j1 -M1024 .lake/R36AuditR2.lean`: exit 0,
   0.6059132970040082 seconds. All eight full theorem types and axiom reports retained;
   the skill's `validate_audit` passed.

Used the skill's `audit_source` and `validate_audit` through `python3 -B`/`runpy`;
bytecode writes disabled. Its CLI would add temporary unleased paths and extra
commands outside the fixed build/audit sequence, so it was not invoked. Lean pin,
config and manifest hashes match R35/r1. Actual version receipts are inherited from
r1: Lake `5.0.0-src+eb6cafb`, Lean `4.35.0`, release
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; no fresh r2 version commands were run.
No r2 checker failed and no retry occurred. Intake's unavailable `python` shell
command exited 127; subsequent read-only `python3` calls exited 0. This was not a
Lean/checker failure. A read command printed the oversized frozen r1 log and its
terminal display was truncated; the original complete log remains unchanged.

Read-only actual-import traversal inspected 10 local modules. Source scan for
sorry/admit/project axiom/checker-bypass terms returned 1 with
no matches; this supplements, and does not replace, the indirect axiom audit.

## Frozen dependencies and artifact hashes

All frozen input/evidence hashes rechecked unchanged after both commands:

| Path | SHA-256 |
| --- | --- |
| `docs/yulang-operational-type-safety-ja.tex` | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |
| `notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean` | `e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932` |
| `notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean` | `3b1588bff2d28a3db7aa241c930495b84f090e880ad49ac8fb2d593d54943d41` |
| `notes/theory/lean/YulangClosure/PaperTermSubstitution.lean` | `a4f87f9604c03beefdc44de5d45fcd9f5924ca9580c75edf353cf267e69a0d4f` |
| `notes/theory/lean/YulangClosure/PaperCoreStep.lean` | `503f81c162f7b9ceb0f7d27aa9796b8d7010345653267c675267ce14214c57e9` |
| `notes/theory/lean/YulangClosure/CoreControlBridge.lean` | `30a0007aea313eccc42531bf346891c010dbed7b4b34cea1aebe7043a9a6d99a` |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `notes/theory/lean/lakefile.toml` | `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194` |
| `notes/theory/lean/lake-manifest.json` | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |
| `tasks/agent-loop/inbox/paper-core-step-r35-r3.md` | `05cacac3b1536ff53eea589e71536cac2b5d34bbd1b71ef48e195a1aeb0eb128` |
| `tasks/agent-loop/inbox/paper-core-step-r35-r3-review.md` | `5212dd2f014f5868d13aee909dfa794e530fedd872a8dc137081aa8d675364a5` |
| `tasks/agent-loop/inbox/paper-core-control-r36.md` | `243671c3c6cedd4e15896a20174219a56c78ec73d3b449eaa39883118c93eb3a` |
| `tasks/agent-loop/inbox/paper-core-control-r36-worker-checks.txt` | `45338650e035a7b61b82b8de363e53f51c0e53074ee2f4d6ac06dd5a6ce8a397` |
| `notes/theory/lean/.lake/R36Audit.lean` | `1a100c49eb1907b0c41de6655711dfa005058e1efd82961b1496f4c4eaec76f2` |

Changed/generated artifact hashes:

| Path | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/PaperCoreControl.lean` | `261d6a77438eec1a32e0299b73583899204ed7c2fe0590b819ecd3fd5b89876e` |
| `notes/theory/lean/.lake/R36AuditR2.lean` | `1a100c49eb1907b0c41de6655711dfa005058e1efd82961b1496f4c4eaec76f2` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/PaperCoreControl.olean` | `95a46e72e6f907893b927e26decbc9bf1d4e51f0a5eb684bb6b64c81f493cd62` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/PaperCoreControl.ilean` | `1724b66926f488fe5a34a761606f7d4f7130c8c376e36c70563d5e60d8288e4e` |
| `notes/theory/lean/.lake/build/lib/lean/YulangClosure/PaperCoreStep.olean` | `9cd98cdcbd39f312e94a9981f5449cc12847160162ce4975b5d617111a537057` |

Sole worker log `tasks/agent-loop/inbox/paper-core-control-r36-r2-worker-checks.txt`,
SHA-256 `1d9319d43cdce8808961af8b319a6d20ef02f37a58cb93526a25ff7b14bb9daa`. This is the sole worker handoff path.
R1 scratch/log/handoff hashes remain unchanged. R1 source baseline
`7ce8fb1c4a3cafe2738723af3dea6e6df11b4d227f1151761941fdb38df7ca95`
is preserved by its frozen committed snapshot, while the authorized current source
continues with the explicit r2 repair.

## Resources and cessation

R2 worker usage: 2/7 native Lake invocations, 1.0449385740066646/119.475628262 checker
seconds. R1+r2 worker checker use is 1.5693103120066647 seconds; aggregate sprint
accounting, primary verification and active-time charge remain Luna's responsibility.
No envelope reset or extension. Intake was completed before admission; primary's
actual launch evidence governs active-time accounting. Both checker timestamps and
final cessation timestamp `2026-10-25T19:14:20.541255+00:00` are in the log. No further checker work remains.

Writes were confined to the r2 leased source, audit scratch, `.lake/build`, log and
this handoff. No Git, tests, Rust, network, installs, dependencies/config/root-import
changes, shared scheduling writes, children or outside contact. Read-only final
process scan found no Lean/Lake/elan/checker process. R35 imported `.olean` remains
unchanged. Source/cache/checker work has stopped; after this handoff is written,
**ALL WORKER WRITES STOPPED**. Cache ownership returns only through Luna's handoff.
