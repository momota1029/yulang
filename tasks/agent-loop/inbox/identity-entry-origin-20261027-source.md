# IDENTITY-ENTRY-ORIGIN-20261027/r1 — implementation trace

Primary-persisted read-only handoff from `/root/identity_entry_impl`; the implementation lane stopped without writing a file. This receipt records the message returned by that lane. It is conditional Rust constructor evidence, not a checked source/native correspondence or a compiler defect.

Contract: `tasks/agent-loop/sprints/identity-entry-origin-20261027-r1.md`, SHA-256 `54bf2ba78b1cde38e22970115ad8f309639c1225995894af50a8ea1d57747fe0`. Baseline `aec5cd0de3bed8a9a364a38a4601fefd2a066014`.

## Conditional source-to-runtime path

Assuming one supplied `LocalSource` root/index is the same occurrence throughout:

1. `RuntimeProgram::from_hir_with_roots` selects `local_source_for(source_root)` (`program.rs:567–574`). Lambda/Apply traversal follows their supplied source indices (`:653–664`). `label(i)` checks `source.expression(i)` and derives `offset + i.ordinal()` (around `:580`); each `Code.site` retains source root, expression occurrence and range (Code construction around `:870+`).
2. Lambda lowering copies `parameter.id`, the body label, and assigns Value when the annotation is absent or its outer `ty.effects` is `None`. The annotated callback schema is built only by `CallbackResultSchema::from_parameter` (`program.rs:819–850`; schema requirements in `receiving.rs:64–92`), so an unannotated identity has `callback_schema = None`. Name lowering resolves `LocalSourceResolution::Parameter(id)` against Lambda roles; this unannotated formal is Observe (`program.rs:735–780`). Apply retains actual callee and argument labels (`:852–855`).
3. Evaluating that Lambda creates a Closure value and executable with the Lambda `SourceSite`, same `HirParameterId`, Value role, body label, and lexical environment (`machine.rs:864–886`). Apply pushes `Frame::Callee` with its actual callee, argument, caller environment and Apply site (`:888–898`).
4. After the callee returns, Callee allocates the argument as a Computation Delay at the Apply site, storing argument label and caller environment, then appends an ordinary receiving view. `receiving.delay` copies inherited image/unknown or defaults to `(None, true)` (`machine.rs:1181–1199`; `receiving.rs:208–222`). Selection uses the returned value's executable; its source supplies the Lambda provider site. `new_invocation` records the Apply call site, Lambda provider site and active Invocation descriptor before `execute(delay)` (`machine.rs:1224–1248,1280–1297`; descriptor definitions at `:90–103,1780–1798`).
5. ValueEntry runs only after Force/Delay returns. With no callback schema for this unannotated identity, it creates no callback-entry formal receipt. It binds the returned Value/view under `Binder::Parameter(parameterId)` and evaluates the body (`machine.rs:1438–1489`). The body Name instruction resolves the same `HirParameterId` as Observe; lookup reaches the bound cell and `consume` records a Name-read receipt `(owner=current Invocation, view=bound view, slot=body Name SourceSite, formal=None)`, then returns without execute (`machine.rs:2470–2483`; `receiving.rs:261–279`). A body that is only Name creates no callback-use receipt; that later Apply branch requires callback-entry/formal evidence (`machine.rs:1358–1386`; `receiving.rs:338–416`).

For comparison only, an annotated callback Value path may create a post-Force formal callback receipt with a new callback view, Lambda schema site and `Some(formalId)` (`receiving.rs:297–335`). That path does not apply to this unannotated identity. The original source Value-entry rule still places its source receipt before designated Force (Call semantic input realization §6, item 2, lines 491–496; `OriginalFormalShared.lean:54–73`). The pre-Force source receipt, native invocation descriptor/Delay/view, post-Force callback formal receipt, later Name-read receipt and later callback-use receipt remain distinct.

## First unsupported owner equation

`OriginalIdentityRealization.Identity` records declaration/context and source Sites/name (`OriginalIdentityRealization.lean:22–48`); `identity_value_entry` and `identity_body_resolves_formal` establish the Value role and formal lookup for that Lean record. No checked construction equates it to the actual HIR `RuntimeSourceRoot`/`LocalSourceIndex` that carries the matching Lambda, Apply and Name source root, occurrence and range. In particular, code labels and equal numeric identifiers do not establish that cross-representation identity. The conditional native equations above therefore do not establish source authenticity, selected Closure/provider equality or an end-to-end identity source/native join.

Next owner: the original source/HIR frontend construction and correspondence. After that join, the existing original Parameter receipt/readout/admission owner remains separately open. This is `NO_CHECKED_IDENTITY_TO_HIR_JOIN`, not a claim that every frontend correspondence is impossible and not a source counterexample.

## Pins and stop

The implementation lane verified the frozen contract and these runtime owner hashes:

| Source | SHA-256 |
| --- | --- |
| `tools/inference-playground/src/runtime/program.rs` | `6607c4371366739c0e593b29a5da96becbb0bd743b2618a3755653f1b0ac3907` |
| `tools/inference-playground/src/runtime/machine.rs` | `b621ba8ec28d7819db881a4fd5bad0236edbf23e2aa92a879eb1dd211a30c46e` |
| `tools/inference-playground/src/runtime/receiving.rs` | `57b1664e26f137e6425731dde2bb1f1559170d9914f5be7a0f17fae3a8555e26` |

The lane reused the previous annotated-path trace only as an owner locator, not as identity evidence. It performed no build, test, edit, scratch write, Git operation or descendant launch. Requested/observed model metadata was unavailable. All read-only work stopped within the assignment bound.
