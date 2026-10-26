# Call entry formation: direct lambda/wrapper spines

Revision: r1, frozen after kernel checks. Producer: `/root/execution_frontier`,
generic `lean_prover` fallback using `.codex/agents/lean-prover.toml`. No children.
Requested model/effort: inherited; separately observed model/effort metadata is
UNKNOWN. This is a constructive research result, not semantic approval,
independent review, native correspondence or whole-language proof closure.

## Packet and source

Packet baseline: `adfed0dbcc8875ac0c9e66c40a0b967b3e9df073` on `yulang3`, as
provided by the primary. Original obligation: the code-formation and
substitution part of corrected V5(4), applied to the finite-prefix interface in
V6. Governing source for this fragment is
`docs/yulang-operational-type-safety-ja.tex:362–395` and
`notes/theory/2026-10-24-corrected-core-value-continuation.md`, V5(4).
The unchanged whole-language claim still quantifies over all original accepted
source cases; this direct-spine lemma is an explicitly limited contribution to
that claim.

Owned outputs only:

- `notes/theory/lean/YulangClosure/PaperCallEntryFormation.lean`
- `tasks/agent-loop/inbox/20261026-proof-advance-call-entry.md`

The isolated project/cache/log lease is
`/workspace/scratch/f98087c7ac1a/call-entry/`. No existing repository source,
root import, manifest, toolchain, compiler, scheduling record or Git state was
modified.

## Constructed result and source correspondence

`DirectCallableSpine` is an independent syntactic predicate with both lambda
modes and arbitrary finite nesting of `Value.wrap`. It does not define typing,
safety or progress. It is a sufficient entry shape; normalization from an
arbitrary callable remains a distinct open obligation.

`entryCode receipt owner function thunk` deterministically constructs one
finite administrative body. A wrapper forms exactly
`Delay(let z <- Force thunk in argumentAdapter)` and keeps its result adapter
outside the recursively formed inner body. Wrapper peeling retains the same
owner and never inserts another source `call`. A Value lambda forms
`let x <- Force (View receipt thunk) in body`. A Computation lambda uses the
existing capture-avoiding substitution on that same viewed thunk. The latter's
success and typing are proved from the existing lambda derivation, not assumed.
All declaration, graph and lexical environments remain literally shared.

`ReceiptMetadata = OwnerName -> AdapterMetadata -> ViewMetadata` is merely a
selector of the literal metadata supplied to this value-type theorem. The proof
is uniform in this selector and assumes no semantic law about it. It does not
construct the actual world receipt. The exact `EnterStep` relation contains the
three manuscript administrative clauses and their active let/scope contexts.
It starts at `enter`, after the omitted fresh-owner allocation, and retains the
literal scope. It does not execute scope completion or model current-world
state.

Fully qualified namespace:
`YulangClosure.PaperTypes.PaperCallEntryFormation`.

### Main declarations and premises

1. `spine_formation`: for arbitrary `d g e function thunk argument result`, a
   direct spine, `function : callable argument result`, and
   `thunk : thunk argument`, and arbitrary receipt selector/owner, constructs
   one `code` with successful `entryCode`, its original paper computation
   typing at `result`, and a finite `EnterTrace` from the literal `enter`.
2. `call_spine_formation`: takes the existing
   `PaperComputationTyped d g e (.call function thunk) result` directly, plus
   the direct-spine premise. It gives the same three facts and a trace
   `.scope owner (.enter owner function thunk)` to `.scope owner code`.
3. `call_spine_finite_interaction`: also takes the existing independent
   `PaperTemplateExecution.BodiesTyped d` and
   `StackTyped d g e stack result finalResult`. It constructs one shared `code`
   as above, then universally quantifies over every existing
   `PaperExtendedExecution.InteractionTrace` from `{head := code, stack}` and
   its existing `ProtocolTyped` condition. Its conclusion is final state
   typing, final erased computation typing and the exact interaction erasure.
   The constructed code witness is outside the universal trace quantifier.
   These are traces of the formed code in the existing partial executor, not
   claimed executions of the retained owner scope.
4. `value_entry_view_frontier`: from an existing typed Value-lambda call and
   arbitrary typed ordinary let suffix, retains the source-shaped owner-scope
   entry trace, constructs the actual single `PaperExtendedExecution.Trace`
   let push, proves the resulting state typed, and proves its next
   `controlStep` is `none`. Its head is exactly
   `Force (View (receipt owner profile) thunk)`, with the unmodified lambda body
   on the stack. `controlStep_force_view_none` establishes that missing
   executor case for arbitrary metadata/thunk/stack.

`EnterTrace.trans`, `EnterTrace.underLet`, `EnterTrace.underScope`,
`EnterTrace.plug` and `adaptedThunk_typed` are the supporting lemmas.
`EnterTrace.plug` keeps surrounding ordinary let frames outside an existing
scope when supplied such a scoped trace.

## Before/after and application to the parent

Before this packet, Paper typing recorded lambda/wrapper premises, but there
was no direct-spine theorem constructing the manuscript's actual viewed entry
body and same-owner administrative trace from those premises. The existing
`PaperComputationTyped.callWrapped` only introduced Call typing.

After this packet, the complete finite wrapper spine, delayed argument adapters,
inner-to-outer result adapters, both lambda modes and their shared captures
produce an independently typed body without a `BodyLaws` assumption. That exact
body feeds the existing arbitrary finite-interaction theorem. The value-type
code-formation/substitution sub-obligation of V5(4) is thus discharged for an
already obtained direct spine.

The formal frontier theorem identifies the first execution seam: even this
well-typed Value-lambda body reaches `Force(View ...)`, which the current
connected executor does not reduce. This is a limitation of the partial Lean
executor, not a counterexample to corrected source progress. Removing the View
would destroy the intended receipt ordering and is not an allowed repair.

Remaining owners/premises:

- Operand observation/normalization must obtain a direct callable spine from
  the original closed graph/value judgment, including graph references,
  Views, type applications and the relevant guards.
- The corrected machine/world owner must construct the actual fresh owner and
  receipt, implement View/Force observation with the intended metadata, and
  connect enter and scope completion to current-world execution. No saved-world
  restoration, owner freshening policy or world abstraction was introduced.
- The paper typing owner still lacks full raw scope/enter/expose typing and
  the other whole-language cases. The generated ordinary code's typing does
  not by itself extend that raw judgment.
- Full progress/noBad, complete frame/source realization, source/native
  correspondence, and the original inference A/B claims remain OPEN.

## Actual verification

Native Lake:
`/workspace/scratch/e41512dd7957/toolchains/lean-4.35.0-linux/bin/lake`.
Actual version results: Lake `5.0.0-src+eb6cafb`, Lean `4.35.0`, Lean commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.

The primary-authorized read-only cache was copied to the isolated project.
Every one of the 18 imported/module targets in `call-entry/modules.txt` was
then checked in dependency order with
`lake --no-cache build +<module>`, refreshing against the actual copied input
bytes. This ensured one active Lean process at a time. All Lean processes used
`-j1 -M1024`; `LEAN_NUM_THREADS=1`. No cached olean was treated as proof of an
unrefreshed changed input.

First focused build: dependency targets passed; the new module failed with
an ambiguous dotted `.tail` and the reserved binder name `scoped`. These were
repaired to `EnterTrace.tail` and `scopePath`. Failure output is retained in
`call-entry/build-1.log`. No theorem claim relied on that failed build.

The repository helper was run against the isolated project with the actual
module, all named theorem declarations, the exact native Lake and a finite
timeout. `audit-2.log` records the eight-theorem construction pass. After the
frontier theorem was added, `audit-3.log` records the final ten-theorem pass:
exit 0, every declaration confirmed as a theorem, every complete printed type,
and every complete axiom report accepted. The final run took 2.919 seconds;
all focused checking totaled 65.787 seconds of the 120-second budget.

Command shape (exact arguments are retained at the top of `audit-3.log`):

```sh
python3 .agents/skills/yulang-lean-proofs/scripts/check_lean.py \
  --project /workspace/scratch/f98087c7ac1a/call-entry/project \
  --lake /workspace/scratch/e41512dd7957/toolchains/lean-4.35.0-linux/bin/lake \
  --module YulangClosure.PaperCallEntryFormation \
  --theorem YulangClosure.PaperTypes.PaperCallEntryFormation.call_spine_finite_interaction \
  --theorem YulangClosure.PaperTypes.PaperCallEntryFormation.value_entry_view_frontier \
  --timeout 45
```

The final command included all ten names below, not only the two shown in this
compact command. No new-module warnings. Dependency warnings were existing
unused-variable/simp and deprecated `if_pos` warnings; the leased module did
not modify those foreign inputs. Full root/default-target integration was not
run by this worker and belongs to the primary.

### Complete final axiom results

| Declaration (under the namespace above) | Axioms |
| --- | --- |
| `EnterTrace.trans` | `[propext, Quot.sound]` |
| `EnterTrace.underLet` | `[propext, Quot.sound]` |
| `EnterTrace.underScope` | `[propext, Quot.sound]` |
| `EnterTrace.plug` | `[propext, Quot.sound]` |
| `adaptedThunk_typed` | `[propext, Quot.sound]` |
| `spine_formation` | `[propext, Quot.sound]` |
| `call_spine_formation` | `[propext, Quot.sound]` |
| `call_spine_finite_interaction` | `[propext, Quot.sound]` |
| `controlStep_force_view_none` | `[propext, Quot.sound]` |
| `value_entry_view_frontier` | `[propext, Quot.sound]` |

No `sorryAx`, project axiom, native-evaluation assumption or checker bypass was
accepted. The narrow dependency-cone source scan is retained in
`call-entry/source-scan.txt`; its findings are reported below. Axiom results do
not remove the explicit theorem premises or establish source correspondence.

## Frozen hashes and scratch

Module SHA-256: `2465c5620b0b66f6029ab294134d9860cd8bf810ac25c5f30763cb709c7da31e`.

The following source and dependency SHA-256 values pin the reviewed input
surface. The isolated copied sources match the current repository bytes used
by this packet; other lanes' modules are not dependencies of this module.

| Input | SHA-256 |
| --- | --- |
| `docs/yulang-operational-type-safety-ja.tex` | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |
| `notes/theory/2026-10-24-corrected-core-value-continuation.md` | `4d8ffd63cbb65cd6917145fa31a4cb3f04656a19f7b71fd0e3fdd6cecaabfbeb` |
| `notes/theory/lean/YulangClosure/PaperTypeSubstitution.lean` | `02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861` |
| `notes/theory/lean/YulangClosure/PaperTypeFormation.lean` | `29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13` |
| `notes/theory/lean/YulangClosure/DeclSubst.lean` | `f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258` |
| `notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean` | `78f23b9e946b0259cdb63797ed226706112f71375a013e0b9cc8745ad5afe8b0` |
| `notes/theory/lean/YulangClosure/PaperExecutionBinderLaws.lean` | `568a9a5a1991bb605d85e9b58f33638fb445b1325516e10eed0f076f72346d7a` |
| `notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean` | `fae64aa9a5c37572a3f654c403b7fb8ff7eb7adccaa4e3540fff85e61ce84819` |
| `notes/theory/lean/YulangClosure/PaperExecutionGraphWeakening.lean` | `313a550a550716e235e73690d238f1040838aeebd2cc0cf0b7753979ab6fe38d` |
| `notes/theory/lean/YulangClosure/PaperTermSubstitution.lean` | `42d7f46d992e715443a7116066b51ae1748849718f6c4e716d9169ea069059d9` |
| `notes/theory/lean/YulangClosure/PaperCoreStep.lean` | `6357b14217e82421eed87da981cef8e94014dcaea634d746ad0b4bb39bff6144` |
| `notes/theory/lean/YulangClosure/PaperCoreControl.lean` | `71594dfb24af402f7b4835dc54b5383a46106faba959b687295cc0431361530e` |
| `notes/theory/lean/YulangClosure/PaperTupleSplitExecution.lean` | `7bc13a41a0333d885b91291a7fbb1ef18302a94c79a34f21469dbae19d76f84d` |
| `notes/theory/lean/YulangClosure/PaperPerformLetExecution.lean` | `2f0026049554cb870158115b4bab8d42f7cbee8b030ee3f84a904763c328cac0` |
| `notes/theory/lean/YulangClosure/PaperResumeExecution.lean` | `5ab59033b0cea347144c50a5323e4dd6cb59cc6bfbdc0bffd063a4808e741935` |
| `notes/theory/lean/YulangClosure/PaperCombinedExecution.lean` | `58661ddec13e1fe4abb6a9b6627597fa824dedbf36f952e56dc15906141314d1` |
| `notes/theory/lean/YulangClosure/PaperTypeApplicationPreservation.lean` | `60e095545530bc784487a4bfcc1c7acfc1160b3adf8c1c8dc03ab98806154556` |
| `notes/theory/lean/YulangClosure/PaperTemplateExecution.lean` | `3ead9cf7d0f57d02d5fd8b44da24f133d7859e76dff8ee1d1b17cb233920d792` |
| `notes/theory/lean/YulangClosure/PaperExtendedExecution.lean` | `a29c5cc15748e8a91338f2a068e94ff7dc58c2a19adad564ba3f5a6fea337ea7` |

Source scan matches: 0.

Scratch outputs: isolated project and its copied/rebuilt `.lake`,
`modules.txt`, `build-1.log`, `audit-2.log`, `audit-3.log`,
`check-seconds.txt`, and `source-scan.txt`, all under the leased `call-entry/`
directory. The helper also created and removed its ordinary temporary audit
source under `/tmp/yulang-lean-audit-*`.

Independent review: NOT PERFORMED by this producer. Root integration/import,
review adjudication, records and Git/push belong to the primary.

**Producer writes STOPPED after this frozen handoff.** No work is continuing in
an unobserved background process.
