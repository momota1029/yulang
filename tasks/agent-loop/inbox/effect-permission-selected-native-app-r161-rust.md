# R161 Rust source/native handoff

Sprint/contract: `EFFECT-PERMISSION-SELECTED-NATIVE-APP/20261102-R161`, revision 1.
Contract SHA-256: `f50df70ebb875b1368daa3f2ef8cda6344975fa3d65a86b494a2a25cdec76395`.
Baseline: `b6c11c33ddf2a9208ac09c36edf3e2018a375124`.

## Outcome

**`NO_SAFE_CODE_SLICE` for encoding the selected-native witness into original App formation consumers.** The R160 source-to-native Apply path remains structurally source-indexed, but its fields do not construct or carry the original `App` typing/admission premise, annotation alternatives, or finite `Checking` judgments needed by the original consumer telescope. No Rust edit, observer, or test can supply those meanings under this read-only lease.

This is a source map, not a semantic proof or source/native closure. P and independent A remain OPEN; production remains unauthorized by these results.

## Prior evidence reused

Reused the independently PASS-reviewed and pushed R160 Rust map at `tasks/agent-loop/inbox/effect-permission-source-app-r160-rust.md`, SHA-256 `900c6210ed58dad9bd55f7d50c2f800086d54ac441b71cffb424887f793a3b44`. Its inspected Apply owners and conclusion still match the source hashes below. It correctly identifies that source occurrence and operand provenance are not the original two finite Checking derivations, and that native effect ports do not establish typing or admission.

R160's selected-signature and native-construction dependencies remain the contract references (definition `e6c6cf995a3618172e45b4f8cdf4578313c057c6ec1e3e118c4dc11b6f162ab9`, selected construction `7367ce8eb69376583386c6d675d067712ec6fa173e96f458ee34ce390dc8901a`). I did not reconstruct that construction or treat either dependency hash as Rust proof evidence.

## Clean source owners inspected

| Owner | SHA-256 | R161 evidence |
|---|---|---|
| `crates/yu-hir/src/module.rs` | `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646` | Ordinary HIR Apply projection retains its source form, occurrence, callee/argument children, errors and range (Apply lowering around lines 3060–3105). This is structural formation; no App typing payload is constructed there. |
| `crates/yu-hir/src/module/local_source.rs` | `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1` | `LocalSource` is rooted by `SourceRootId`; its expression indices and retained formals preserve source identity. Apply source carrier remains a source tree, not a typing derivation. |
| `crates/yu-solver/src/candidate_source.rs` | `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49` | Apply admission (around lines 1900–1930) records one owner, callee and argument indices, source occurrence/checking-cause IDs, endpoint values/effects, result/application effect and optional formal/receiver routes. The `CandidateRelation::Apply` is a constraint recipe; these IDs are not finite source `Checking` judgments. |
| `crates/yu-solver/src/shadow_apply.rs` | `99d67895c250e5d79fb774728867fe2fc88c4dc22df9bfc38ac9fd1aeb0908e5` | Apply native construction (around lines 4290–4380) makes a negative Function demand from argument value/effect, result and invocation effect; it retains callee evaluation, argument evaluation, invocation and application effects as separate structural ports. It adds no App derivation or consumer edge to a source typing law. |
| `crates/yu-solver/src/candidate_call.rs` | `fdc39e01fa3665b4dc14e167973de63b275eb0280b831e340b6cdcee5ed0fc3f` | `ApplySourceInput` (lines 39–61), `CandidateSourceCall` (around 289–395), its validation/observation consumer (479–680), and `PendingCallConstruction::suppliers` (397–430) preserve and re-authenticate same-owner source Apply identity and structural native fields. Explicit supplier gaps include `OriginalGenCall0`, source typing/admission, module use receiving-export correspondence, and whole argument/provider compatibility. Authentication checks source links/ports; it does not discharge these suppliers. |

Hashes were measured directly from these files. These are the only Rust owner paths reviewed for this handoff. Dirty/quarantined `candidate_receiver.rs`, `candidate_scheme.rs`, runtime files, and quarantined/unreviewed artifacts were not read.

## Witness-to-consumer correspondence

| Required identity/consumer | Existing Rust fields | Result |
|---|---|---|
| One source root/owner and Apply occurrence with both operands | `ApplySourceInput.owner`, `expression`, `callee`, `argument`, `checking`; checked against the owner-local `LocalSourceForm::Apply` and exact expression occurrence in `candidate_call::observe_inner` | Structural source-incidence correspondence exists. It carries no original `App` proof. |
| Owner partition / selected native signature witness | Owner-local annotation and module/parameter resolution are available to candidate construction; native demand has argument/result/effect ports | No retained witness field links a selected signature derivation to the original App consumer. A formal route is candidate provenance only. |
| Receiver | `ReceiverBoundaryAttachment` records receiver lambda/body/region and lexical region; observation validates its source links | Explicitly experimental source evidence. It is not a semantic receiver witness, admission, or protection proof. |
| Occurrence / checking premise | `ConstraintOccurrenceId` and `CauseId` identify the candidate recipe | Provenance identifiers only; neither field contains a finite source `Checking` derivation or its proof object. |
| Extension and joint witness | No field on `ApplySourceInput`, `NativeInterface`, or `CandidateSourceCall` packages the original extension together with the same binder's App, FunctionGuard, and Logical payload witnesses | Missing. Separate value/effect endpoints cannot be joined into the required semantic telescope by this structural map. |
| `Kernel.atom` at `.descriptorFormation`; `FunctionGuards.formation/profile`; annotation and governed-port realization; same-binder `Logical` payload | No Rust consumer among the inspected owners constructs or consumes these original formation premises | No source-to-consumer edge is present. These are not fields of the candidate Apply interface. |

The native `NegativeFunction` establishes only its structural argument, argument-effect, invocation-effect and result ports. The independently named callee-evaluation and application effects also remain structural. No row distinctness, soundness, original typing, descriptor formation, profile formation, or admission is inferred.

## Earliest missing owner and parent application

The earliest missing owner on this Rust path is the **source typing/admission rule owner for the original App formation**, before native projection can be interpreted by the original consumers. The HIR owner retains a structural Apply; the candidate-source owner turns it into a constraint relation; the native owner emits a function/effect interface; and the candidate-call consumer revalidates those links. None supplies original `App` typing/admission, the exact two finite `Checking` derivations, selected signature/descriptor witness, annotation alternative, or extension-linked same-binder `Logical` payload.

This locates the missing source premise without narrowing R159's App telescope or deriving independent admission A from profile P. The next proof/source step needs an authorized source owner that constructs that premise and its consumer correspondence; inventing a readback/observer field would only relabel candidate provenance.

## Checks, limits, and handoff

- Checks performed: direct source inspection and `sha256sum` of the five owners above, plus comparison to the frozen R160 map. No Cargo, build, test, scratch/cache/worktree, Git, `current.json`, or other Rust files were accessed.
- No implementation diff or executable behavior change was produced; the exact contribution is the bounded owner-to-consumer map and first missing source owner.
- Requested settings: `implementer`, Luna/high, 300-second maximum. Actual effective model/effort metadata was unavailable to this worker and is **UNKNOWN**; the request is not evidence of effective routing. No Astra work was requested or used.
- All inspection processes completed; there are no live subprocesses. This worker's writes are stopped after this frozen handoff. No disposable scratch paths were created.
- Fresh independent source-map delta review is still required. This author does not certify this handoff.

Next related in-envelope step: reconcile this source-owner boundary with the proof lane's frozen witness fields and identify the precise original App supplier/consumer constructor to implement or prove. Do not treat any structural port or observer result as that construction.
