# Q failure unwind — frozen handoff revision 1

- Sprint/contract: `LEAN-CALL-UNWIND-20261025/r1`, `tasks/agent-loop/sprints/call-unwind-20261025-r1.md`, SHA-256 `efeaabb27416bd9cb51066c37f8a36d13b3a4ced3eeba7f1f9488ac4ada38a2a`.
- Assignment/handoff ID: `LEAN-CALL-UNWIND-20261025/Q`; revision `1`.
- Contract baseline: `64d39df59`, branch `research/simple-sub-intrusion`; no Git observation or operation by this author.
- Sole author/actual worker: `/root/call_entry_body_typing`, acting as Q failure-unwind author. Fresh START acknowledgement/grant acceptance sent before work. Work began after Luna's explicit lease-state activation message. Separate session ID unavailable.
- Requested model/effort: `gpt-6.1-sol/high`; observed model/effort: `UNKNOWN/UNKNOWN`.
- Exact leases/all new paths: `notes/theory/lean/YulangClosure/CallFailureUnwind.lean` and this handoff. No scratch, descendants, generated outputs, P/composition edits or other writes.
- Outcome class: **candidate**, not yet Lean-checked or independently reviewed. Producer is ineligible to certify this result.

## Exact theorem, construction and parent application

`YulangClosure.Control.call_failure_unwind_exists` preserves the exact contract proposition and all quantifiers: for arbitrary metadata/world/failure, every four-constructor Call-frame list and all endpoint fields, there exists a final world and an actual `CallControlStep` prefix of exactly `frames.length + 1` from the active failure to the failed head with empty Call frames. The final world remains existential; the Call view, Original result type, scopes, views, receipts and literal Control suffix are precisely the supplied values.

The module imports only `YulangClosure.ControlSyntax`. A private `prependFailureUnwindStep` lemma inducts over the existing snoc-indexed `YulangClosure.Prefix`, prepending a supplied transition and adding exactly one to its length. The public theorem inducts over frames, generalizing the starting world. Empty frames use one `finishFailure` transition. Each cons case obtains a middle world and cleanup proof from `md.failWorld_total world (CallState.contextControlFrame frame)`, constructs the exact corresponding `failBind`, `failScope`, `failExpose` or `failAdapter` transition, then applies the recursive trace starting at that middle world. The private lemma prepends the actual cleanup step. `List.length_cons` identifies the resulting length `(frames.length + 1) + 1` with the original cons-frame length plus one.

No frame case is omitted. Expose cleanup uses the effect view identity through the actual mapping, preserving both effect/result view syntax in the source state. Adapter cleanup preserves its input/output types and body. No world equality, cleanup determinism, lifecycle restoration, scope activity change or new transition is asserted. Total cleanup is consumed as the existing `Metadata` field, not introduced as a custom axiom.

Parent application: Luna concatenates this constructed suffix to the supplied initial prefix ending in an active failure. The combined length is exactly `n + (s.frames.length + 1)`. Accepted finite-prefix preservation supplies the final typing and retained result/suffix; the failure trace endpoints directly supply the failed head, empty Call frames, unchanged Call view/scope/view/receipt fields. Q does not prove the initial signal state is reached.

## Owning source evidence and prior work

Inspected the exact formal owners: `Metadata.failWorld_total/failWorld`, `CallState.contextControlFrame`, all four `CallControlStep.fail*` constructors, `CallControlStep.finishFailure`, and `Contracts.Prefix.refl/snoc`. The cleanup mapping is `.bind body → .typedCallBind body`, `.adapter input output body → .typedCallAdapter input output body`, `.scope owner → .scope owner`, and `.expose effectView resultView → .view effectView.identity`. Constructor parameters were supplied in their actual declared order.

The accepted finite-typing chain is pinned for Luna's composition, not treated as a proof of progress, source generation or cleanup correctness. No historical failed proof or assumed-transition test is reused as a theorem. No Rust/source constraint generation, accumulation, propagation, consumer execution or native correspondence was established. The constructed trace follows the actual formal constructors, but Q supplies no source applicability or runtime cleanup-correctness bridge.

Original Call A/B, inference A/B, source/native, effects/world/receipt correctness, arbitrary terminal reachability, external resumption and production remain OPEN with Luna/existing source and operational owners. The `.force (.view (.delay body) occurrence)` coverage gap and r9 `SOURCE_INPUT_BLOCKED / UNACCEPTED` remain unchanged. No implementation slice is requested.

## Frozen artifact/dependency hashes

Candidate source SHA-256: `2d7422bc4c83310a1a1d0a2bcaa5528bb6a8801520c42db2f2ada6b12224b89c`.

All **50** exact path/hash records in the frozen contract dependency table matched before construction and again at `2026-10-25T03:31:52Z`. This includes 24 source/evidence/toolchain records and 26 binary artifact records (13 output pairs); the contract's phrase “output pairs: 26” labels 26 individual outputs. None was produced or executed by this author. The exact dependency set is the table in the contract identified above; no dependency was added or changed. Its observed canonical digest is `77ff027fa455a627984099ca5f5850b78b4a6d7c73c3a8126d1321eefbb15c95`, computed as SHA-256 of UTF-8 lines `path + TAB + hash + LF`, sorted lexicographically by `(path, hash)`.

Principal source dependencies, under `notes/theory/lean/YulangClosure/`:

| Input | SHA-256 |
|---|---|
| `ControlSyntax.lean` | `1f937e4c51b79d1a2dc4a2291a1e3f5797403eae5975a53a42d574867a1690f0` |
| `Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `CoreExecution.lean` | `86b4bdbf605046d7648fba803aa31eb9e96264627f123f8d14bf937813b4ef7e` |
| `CoreSubstitution.lean` | `c4bca75be173f20d7a48751205f488ac5f0057b476e6f52d1ef7abcf046a001a` |
| `CoreSyntax.lean` | `dff3e5851c9ef971ec404f9542d684074a13623bb0820c3a5e4d5da072783ece` |
| accepted `CallFiniteTyping.lean` | `555e6ee61fad15c93df70bbec13781716d83292a86110a6eb6670018e9b70588` |

Accepted finite-typing outcome/review/verification hashes respectively: `f82192a95c9d5cac2474160e56654ffa6b36fa737edca09fd443b3b0fab1456d`, `5ad32dc61b81056348607ba8bda344fd6c117806f14bf67dbcc8ae7b268c94c4`, `50a0c45503460cc166c45d5099698a1f7b8c3cd6a2cc5bd980f9386a1a86f108`.

## Checks/resources, mutual TODOs and cessation

Static checks: exact public proposition matches contract after whitespace normalization; no `sorry/admit/axiom/unsafe` tokens; only `YulangClosure.ControlSyntax` imported; all 50 dependency hashes matched twice. These checks are source audits, not Lean elaboration or independent certification. No Lean/compiler/tests/Git/external contact/nested CLI ran. No identified premise or static construction obstruction; first actual elaboration check remains Luna's responsibility.

Fresh author cap 600 seconds, no carryover, Astra zero. First work UTC observation `2026-10-25T03:30:36Z`; exact acknowledgement-to-STOP active elapsed unavailable. Conservatively charge the full grant; no remaining author continuation is claimed after STOP.

- `Q-FAILURE-VERIFY-COMPOSE-1`, owner Luna: revalidate frozen bytes/pins, compile Q in the authorized serialized sequence, query its exact signature/axioms, compose using explicit Prefix concatenation and accepted finite typing, then obtain fresh nonauthor review. First missing evidence is actual elaboration; required outputs are complete receipts and the unchanged failure initial-trace corollary. Falsifiers: failed elaboration, any missing frame case or cleanup witness, wrong `contextControlFrame`, length mismatch, changed endpoint metadata, world equality, unexpected axiom or changed proposition. No repair loop is authorized under this revision.
- `Q-FAILURE-SOURCE-1`, owner Luna/existing source and operational lanes: keep source construction/cleanup applicability and cleanup correctness separate and OPEN. Q does not justify a production edit or lifecycle restoration theorem.

Next in-envelope author step: none. Pending Luna checking/composition/fresh review/integration. Handoff ID/revision byte hash is sent separately. **STOPPED: all writes cease upon frozen submission.** No descendants, scratch paths or unresolved descendant leases; no ongoing work is claimed while awaiting intake.
