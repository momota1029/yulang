# Call-entry typing repair — frozen P handoff revision 1

- Sprint/contract: `LEAN-CALL-ENTRY-SPINE-20261025/r2`, `tasks/agent-loop/sprints/call-entry-spine-20261025-r2.md`, SHA-256 `0f81f286dd3910f48b3f7b49d4f61a6c7a415609a16f0e473fe093bf567c18d4`.
- Assignment/handoff: `LEAN-CALL-ENTRY-SPINE-20261025/r2/P`, revision `1`.
- Primary-supplied baseline: `3199f25f0`; no independent Git observation.
- Sole author/actual worker: `/root/call_entry_body_typing`. Fresh supported continuation received; actual START acknowledgement sent to `/root` before work. Separate session ID unavailable.
- Requested model/effort: `gpt-6.1-sol/high`; observed: `UNKNOWN/UNKNOWN`. No model switch claimed.
- Exact exclusive writes/all new paths: `notes/theory/lean/YulangClosure/CallEntryTypingRepair.lean` and this handoff. No scratch, descendants, generated outputs or other path writes. Frozen r1 P/Q/composition untouched.
- Outcome: **candidate**; not Lean-checked or independently reviewed by this author.

## Claim, repair and parent application

The new module imports only `YulangClosure.CallContextTyping` and declares the exact unchanged contract `YulangClosure.TypedCall.callEntryBody_typed`. Every mode, carrier, body, three type parameters, declared consumer, arbitrary pending list, and all four hypotheses/conclusion are preserved. The statement matches the contract after whitespace normalization.

The first proof step is now `cases mode with`. Each branch keeps its entered computation, consumer-input conversion, consumer bind and pending-adapter application local. Value mode derives `valueEntryBody` with `CompTyped.force` and `CompTyped.bind`. Computation mode applies the checked `computationEntryBody_typed`. Both use `hconsumer` to type the actual declared consumer bind, then the checked `adaptersTyped_plugResultAdapters` with the original `hpending`. Only `callEntryBody` and `consumeCallResult` are unfolded at the final step. No repeated dependent `match mode` expression appears in a local `have` type. No helper, premise, semantic rule or source restriction was added.

The original r1 proof failed actual elaboration: successive local matches accumulated discriminants `mode, hbody`, then `mode, hbody, hentered`, then further hypotheses, so Lean rejected their computation indices as mismatched. The complete persisted diagnostic in `20261025-call-entry-spine-verification.jsonl` was read. That r1 candidate is not reused as a checked proof and the failure is not presented as a theorem counterexample. This r2 candidate changes proof organization using the frozen existing constructors; it still requires actual Lean checking.

Luna's exact next application is unchanged: obtain Q's finite lambda leaf with its typed carrier and pending list, invert the leaf typing, convert the pending endpoint with the consumer-output equality, and apply repaired P to establish the entry-body component of `completeCallEntry_typed`. Both empty and nonempty pending lists remain quantified. No consumer is omitted, adapter order reversed, pending suffix dropped, adapter executed, or receipt modified.

## Source and historical evidence boundaries

Exact formal owners reused from the unchanged, hash-revalidated sources are `CoreSyntax.CompTyped.force/bind`, `Adapter.typed`, `AdaptersTyped`; `CoreExecution.valueEntryBody/callEntryBody/consumeCallResult/plugResultAdapters`; `CoreSubstitution.computationEntryBody_typed`; and accepted r3 `CallContextTyping.adaptersTyped_plugResultAdapters`. Their propositions supply only syntax typing. The previously inspected and now hash-revalidated `ControlSyntax.CallControlStep.peelWrap/attachReceipt/enterLambda` and operational paper's Call-entry/adapter and local preservation passages locate the construction path, not runtime/source adequacy evidence.

No source constraint generation, accumulation, propagation, native correspondence, execution coverage or operation/effect preservation was established. Original Call A/B and inference A/B, FL12 source applicability/complete Force result frontier, and raw/typed Call-step correspondence remain OPEN with Luna/existing source and operational owners. The existing `NO_SAFE_CODE_SLICE` remains. No production implementation TODO follows from this elaboration repair.

## Frozen source/dependency hashes

Candidate `CallEntryTypingRepair.lean`: SHA-256 `f90c2192422e35cc7f85716e29199c9587976e230e12543aff0609eedcc49c39`.

All r2 pins were observed matching before construction. The paper and frozen r1 P were additionally revalidated. Prefixes below are under `notes/theory/lean/YulangClosure/` unless a full path is given.

| Input | SHA-256 |
|---|---|
| `CoreSyntax.lean` | `dff3e5851c9ef971ec404f9542d684074a13623bb0820c3a5e4d5da072783ece` |
| `Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `CoreSubstitution.lean` | `c4bca75be173f20d7a48751205f488ac5f0057b476e6f52d1ef7abcf046a001a` |
| `CoreExecution.lean` | `86b4bdbf605046d7648fba803aa31eb9e96264627f123f8d14bf937813b4ef7e` |
| `CallContextTyping.lean` | `09bc05fc8561ee81186dd6eae3667a77b0360a8dd27a6236548dfb01d33a5125` |
| `ControlSyntax.lean` | `1f937e4c51b79d1a2dc4a2291a1e3f5797403eae5975a53a42d574867a1690f0` |
| `CallPeelingTyping.lean` | `f89e31759657f602ba69b41a31c9f63ba61f003aa1ebe560323d65dda2b33c44` |
| frozen r1 `CallEntryTyping.lean` | `21850ac899060ade9f9db5139b20e5e1779b4f18b67d6d1127501827ec146ba2` |
| `tasks/agent-loop/sprints/call-entry-spine-20261025-r1.md` | `77affc0d4d0765c8fffd92fc41653a154ab66bb6598c31c039e4e518d449d4d9` |
| `tasks/agent-loop/sprints/call-entry-spine-20261025-r1-outcome.md` | `11f2478ec74c36fa14c46b66a9027dc9bc8f3fce2e62f6c0356ab8063989c8bb` |
| `tasks/agent-loop/inbox/20261025-call-entry-typing.md` | `4e39371d8e46f722e025e203247a913a76aac8da4e5bccb7d5ea411bea8a1cd4` |
| `tasks/agent-loop/inbox/20261025-call-peeling-typing.md` | `70f2d41c9a785fb5d7d1cee065322c6b68c41bab2ff927f401218c79f20f865b` |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `notes/theory/lean/lakefile.toml` | `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194` |
| `notes/theory/lean/YulangClosure.lean` | `04a209f4aa4a9e8c2848aee11eb16befb6fe4e0b566d4683dd0705f96ccf3b2f` |
| `docs/yulang-operational-type-safety-ja.tex` | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |

## Checks, resources, next step and cessation

Read-only `python3` SHA checks matched all listed inputs. In-memory static proposition audit returned `MATCH`; no `sorry/admit/axiom/unsafe` tokens; only the required import; first proof step `cases mode with`. Frozen r1 P hash remained unchanged after construction. No Lean/compiler/tests/Git/nested CLI/external contact ran; no binary artifacts were created or trusted. Static checks are not proof verification.

Fresh cap 600 seconds, Astra zero, no carryover. First UTC observation `2026-10-25T02:36:54Z`; exact entry-to-stop active elapsed was not measured. Conservatively charge the full 600-second grant; no author continuation budget is claimed after STOP.

- `P2-CHECK-COMPOSE-1`, owner Luna: validate frozen source/dependency and accepted r3 binary receipts, perform the r2 serialized P check, then unchanged Q/composition/query sequence, then fresh nonauthor review. Input is this exact candidate and frozen contract. Required output is actual compiler receipts and unchanged parent-facing theorem. Falsifier: any elaboration failure, changed proposition, omitted consumer/suffix, mode confusion, missing output or unexpected axiom. Author does not independently certify the result.
- `P2-PARENT-BOUNDARY-1`, owner Luna/existing source/operational lanes: retain the named source/native/A-B blockers. No additional source premise is supplied by P2 and no production authority is requested.

Next in-envelope author step: none. Freeze this ID/revision and send its exact byte hash separately. Pending Luna checking, composition, review and integration. **STOPPED: all writes cease after this frozen handoff; no descendants or outstanding descendant leases.** No ongoing work is claimed while awaiting intake.
