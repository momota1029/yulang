# Finite Call typing Q — frozen terminal-typing handoff revision 1

- Sprint: `LEAN-CALL-FINITE-TYPING-20261025/r1`.
- Contract: `tasks/agent-loop/sprints/call-finite-typing-20261025-r1.md`, SHA-256 `dfff6b8af11651122ebc0b3be6cb6a8722b3ce7a60845eb4e82ba1a9488eee68`.
- Assignment/handoff ID: `LEAN-CALL-FINITE-TYPING-20261025/Q`; revision `1`.
- Primary-supplied baseline: `c28827b29b4ff5f2f9d89c03f504fb9f886534f8`; frozen/pushed contract commit supplied as `7ba8442f6`. No Git observation or operation by this author.
- Sole author/actual worker: `/root/call_entry_body_typing`, acting as Q terminal-typing author under the fresh continuation. Fresh actual START acknowledgement and grant acceptance sent to `/root` before reads/writes. Separate session ID unavailable.
- Requested model/effort: `gpt-6.1-sol/high`; observed model/effort: `UNKNOWN/UNKNOWN`.
- Exact exclusive leases/all new paths: `notes/theory/lean/YulangClosure/CallTerminalTyping.lean` and this handoff. No scratch, descendants, generated outputs, P/composition edits or other writes.
- Outcome class: **candidate**; actual Lean verification and fresh independent review pending with Luna. No self-certification.

## Exact claims and application

Both contract Q propositions are preserved exactly, including every premise and quantifier:

- `returned_call_state_typed` extracts `TypedCall.ValueTyped Original.emptyContext v s.resultType` from `CallStateTyped sig s result`, explicit `s.frames = []`, and `s.head = .returned v`.
- `requested_call_state_typed` extracts payload typing at `op.payloadType` and continuation typing under `Original.extend Original.emptyContext op.responseType`, with result exactly `s.resultType`, from the corresponding requested-head equality and the same explicit empty-frame premise.

Each proof decomposes `CallStateTyped`, rewrites the frame list using `hempty`, and inverts `TypedCall.ContextTyping` for the empty list. Its only possible constructor is `nil`, identifying the active Original type with `s.resultType`. Rewriting `hhead` then exposes the corresponding `CallHeadTyped.returned` or `.requested` constructor. The former supplies its stored value typing; the latter supplies its stored payload and response-bound continuation derivations. No extra premise or helper is introduced. The independent suffix derivation is not used to identify the outer `result : Control.Ty` with the Call's `s.resultType : Original.Ty`.

Parent application: Luna applies these two lemmas to the typed target supplied by P's finite-prefix preservation in `initial_call_prefix_terminal_typing`, separately for each supplied empty-frame/head equality. This establishes conditional terminal typing at the endpoint. No terminal-reaching prefix, arbitrary endpoint emptiness, progress, successor coverage, or external resumption is asserted.

## Actual source/formal evidence and prior work

The module imports only the frozen `YulangClosure.ControlTyping`. Inspected owning symbols are `ControlTyping.CallStateTyped`, `CallHeadTyped.returned/requested`, and `CoreSyntax.TypedCall.ContextTyping.nil`. `CallStateTyped` explicitly separates Call frames from the independently typed literal Control suffix. `CallHeadTyped.requested` explicitly retains the operation response binder. Those existing derivations are the complete proof inputs; terminal reachability is not assumed as a theorem.

Inspected `ControlSyntax.CallControlStep.finishReturn/finishRequest`: their represented targets carry empty Call frames and returned/requested heads. This locates a formal constructor/consumer seam; Q does not establish that actual compiler/source constructors emit those transitions, nor prove a raw/native correspondence. No source constraint generation, accumulation, propagation, execution or native code evidence was produced. The accepted r2 one-step outcome/review was read as the sprint's existing preservation boundary, not used to infer progress or omitted transition coverage. Historical failed candidates are not reused as proofs.

Remaining source/native, world/effect/receipt, original Call A/B, inference A/B and production gates remain OPEN with Luna and existing source/operational owners. In particular `.force (.view (.delay body) occurrence)` still lacks the required transition coverage; r9 remains `SOURCE_INPUT_BLOCKED / UNACCEPTED`. Q supplies no premise to close these gates and requests no implementation slice.

## Frozen artifact/dependency hashes

`notes/theory/lean/YulangClosure/CallTerminalTyping.lean`: SHA-256 `319466c8276a638166733a28694881e3d980befd5798006ebc984907a8820a6d`.

All 15 source/result pins in the contract matched before construction:

| Input | SHA-256 |
|---|---|
| `Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `CoreSyntax.lean` | `dff3e5851c9ef971ec404f9542d684074a13623bb0820c3a5e4d5da072783ece` |
| `CoreSubstitution.lean` | `c4bca75be173f20d7a48751205f488ac5f0057b476e6f52d1ef7abcf046a001a` |
| `CoreExecution.lean` | `86b4bdbf605046d7648fba803aa31eb9e96264627f123f8d14bf937813b4ef7e` |
| `ControlSyntax.lean` | `1f937e4c51b79d1a2dc4a2291a1e3f5797403eae5975a53a42d574867a1690f0` |
| `ControlTyping.lean` | `e52aaca8baa5c3312a200952ef07fa7e304686d2642c154831de0365646a497f` |
| `CallStepTypingRepair.lean` | `2ef522c022a0708be670f1ab44b57c8f558d4736f123e14ceb5f6ff259a3c586` |
| `CallContextTyping.lean` | `09bc05fc8561ee81186dd6eae3667a77b0360a8dd27a6236548dfb01d33a5125` |
| `CallEntryTypingRepair.lean` | `f90c2192422e35cc7f85716e29199c9587976e230e12543aff0609eedcc49c39` |
| `CallPeelingTyping.lean` | `f89e31759657f602ba69b41a31c9f63ba61f003aa1ebe560323d65dda2b33c44` |
| `lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `lakefile.toml` | `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194` |
| r2 accepted step-typing outcome | `803dbc0e9724a18149bebf7bc40965c144bbfcefe3c9bce879333c40a9a0ac20` |
| r2 step-typing clean review | `f0e461a622e5309242ee151dac8f93a18183ed01262b77b836e066902f53981f` |
| r2 step-typing verification JSONL | `975f0c540e2e87219afd7fc0dd7477085bc81539f5f7da0de174764eeec5e52a` |

The 20 `.olean/.ilean` hashes enumerated by the contract also matched in a read-only hash audit; no binary was produced or executed by this author. Minimal direct import `ControlTyping` had accepted `.olean` `b487cae6f465c9aea4d5d42d04c8116c46ed58e84d60635e32318f880b1ae59e` and `.ilean` `c5b36c5c5032fc2eab1f3711fd8c7f83fa7a1db3cc6507f08c365c4d771cff6f`.

## Checks/resources, mutual TODOs and STOP

Read-only static checks: both exact propositions match the contract after whitespace normalization; no `sorry/admit/axiom/unsafe` tokens; only `YulangClosure.ControlTyping` imported. No Lean/compiler/tests/Git/external contact/nested CLI ran. Static matching and constructor inspection are not Lean verification or independent certification. No cases omitted from the assigned Q statements; requesting/failed heads and nonempty frames are outside these exact statements.

Fresh budget cap 600 seconds, no carryover, Astra zero. First UTC observation `2026-10-25T03:12:10Z`; exact activation-to-stop active time unavailable. Conservatively charge the full grant; no remaining author work/budget is claimed after STOP.

- `Q-TERMINAL-CHECK-1`, owner Luna: revalidate this frozen source and pinned dependencies, compile Q in the authorized serialized sequence, query both exact signatures/axioms, compose with P, then obtain fresh nonauthor review. First missing evidence is actual elaboration. Required outputs are complete compiler receipts and the unchanged conditional composition. Falsifiers: elaboration failure, dropped `hempty`, use of Control's value typing, dropped response binder, substitution of outer `result` for `s.resultType`, unexpected axiom or changed proposition.
- `Q-TERMINAL-SOURCE-1`, owner Luna/existing operational and source lanes: retain the named coverage/source/native/A-B blockers; do not infer reachability or progress from terminal inversion. No new compiler implementation TODO is justified by Q.

Next in-envelope step: none. Pending Luna verification/composition/fresh review/integration. Frozen handoff byte hash is sent separately with this ID/revision. **STOPPED; all writes cease upon submission.** No descendants, scratch paths or unresolved descendant leases; no ongoing work is claimed while awaiting intake.
