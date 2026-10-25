# P Call-entry body typing — frozen handoff revision 1

- Sprint: `LEAN-CALL-ENTRY-SPINE-20261025/r1`.
- Contract: `tasks/agent-loop/sprints/call-entry-spine-20261025-r1.md`, SHA-256 `77affc0d4d0765c8fffd92fc41653a154ab66bb6598c31c039e4e518d449d4d9`.
- Assignment / handoff ID: `LEAN-CALL-ENTRY-SPINE-20261025/P`; revision `1`.
- Baseline: contract source baseline `e5ea192c0d42bcbc470fee9fb8474d1b8cbee981`; primary supplied launch baseline `73442584d` after contract freeze. No Git operation was used to independently observe either commit.
- Sole current artifact author: `/root/call_entry_body_typing`, assigned P prover. Current session is the primary's supported child assignment; no separate session identifier was exposed. START acknowledgement sent to `/root` at entry.
- Requested model/effort: `gpt-6.1-sol/high`; observed model/effort: `UNKNOWN/UNKNOWN`. No model-switch claim.
- Exact leases and all new paths: `notes/theory/lean/YulangClosure/CallEntryTyping.lean` and this handoff only. No scratch, generated outputs, descendants or other writers contributed to P.
- Outcome class: **candidate**, awaiting primary Lean verification and fresh nonauthor review. No independent certification by this author.

## Parent claim and application

The exact contract P proposition is `YulangClosure.TypedCall.callEntryBody_typed`: for either entry mode, an arbitrary thunk carrier typed at the argument, a body typed under the mode-specific argument binder, the declared consumer input equality, and an arbitrary pending list typed from the consumer output imply typing of the exact constructed `callEntryBody` at `finalResult`. The source statement matches the contract statement after whitespace normalization, including all premises and the conclusion.

The candidate types the mode-specific entered body first. Value mode uses `CompTyped.force hcarrier` and `CompTyped.bind` with the unchanged body derivation. Computation mode applies the checked `computationEntryBody_typed` to that mode's body and the same carrier. It rewrites the entered result using `hconsumer`, binds `consumer.body` with `consumer.typed`, and applies the checked `adaptersTyped_plugResultAdapters` to `hpending`. Unfolding only `callEntryBody` and `consumeCallResult` gives the exact target. No new helper or premise is needed.

Luna can apply this candidate in `completeCallEntry_typed` after Q supplies a typed lambda leaf/carrier/pending list and inversion supplies the leaf's mode-specific body and consumer endpoint equalities. P leaves the pending list arbitrary, including empty and nonempty lists; it never reverses, truncates, executes or inspects adapters. It is a syntax-assembly result and does not prove a transition or source-construction theorem.

The parent operational/source claims remain OPEN: raw/typed Call-step correspondence, operation/effect preservation, FL12 source applicability/complete Force result frontier, original Call A/B and inference A/B. Their owners remain Luna and the existing source/operational lanes; P supplies no new premise closing them.

## Source/native evidence and reused work

Inspected exact owners:

- `CoreSyntax.lean::CompTyped.force`, `CompTyped.bind`, `Adapter.typed`, `AdaptersTyped`, and `FunctionTyped.lambdaValue/lambdaComputation` supply the formal typing premises.
- `CoreExecution.lean::valueEntryBody`, `callEntryBody`, `consumeCallResult`, and `plugResultAdapters` supply the syntax equations actually used by P.
- `CoreSubstitution.lean::computationEntryBody_typed` and accepted r3 `CallContextTyping.lean::adaptersTyped_plugResultAdapters` are reused only at their exact exported propositions.
- `ControlSyntax.lean::CallControlStep.peelWrap`, `attachReceipt`, and `enterLambda` were inspected to locate the construction/consumer seam. No adequacy of those transitions, metadata action or receipt handling follows from P.
- `docs/yulang-operational-type-safety-ja.tex`, the call-entry/adapter subsection and local Call preservation lemma, identifies the intended force/bind versus substitution split and declared consumer. Its broader preservation prose is not substituted for Lean evidence.

No Rust source generation, constraint accumulation, propagation, consumer execution or native projection was established. No production implementation slice is requested; the existing `NO_SAFE_CODE_SLICE` boundary remains. Historical r1/r2 verification failures were not reused as successful checks; only the accepted r3 dependency/outcome is reused. No withdrawn bypass, changed inference rule or changed source domain is involved.

## Frozen artifact and dependency hashes

P source: `notes/theory/lean/YulangClosure/CallEntryTyping.lean`, SHA-256 `21850ac899060ade9f9db5139b20e5e1779b4f18b67d6d1127501827ec146ba2`.

All contract pins were observed matching before construction and rechecked at `2026-10-25T02:28:26Z`:

| Dependency | SHA-256 |
|---|---|
| `CoreSyntax.lean` | `dff3e5851c9ef971ec404f9542d684074a13623bb0820c3a5e4d5da072783ece` |
| `Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `CoreSubstitution.lean` | `c4bca75be173f20d7a48751205f488ac5f0057b476e6f52d1ef7abcf046a001a` |
| `CoreExecution.lean` | `86b4bdbf605046d7648fba803aa31eb9e96264627f123f8d14bf937813b4ef7e` |
| `CallContextTyping.lean` | `09bc05fc8561ee81186dd6eae3667a77b0360a8dd27a6236548dfb01d33a5125` |
| `ControlSyntax.lean` | `1f937e4c51b79d1a2dc4a2291a1e3f5797403eae5975a53a42d574867a1690f0` |
| operational type-safety paper | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |
| r3 contract | `50314a04521194eb9ec2faef2d122c7afc65f91c58d1cc0936c807d881935d42` |
| r3 accepted outcome | `98b9a65a899264cf739ad0ee42ed104e2c01716f530c9d11b561a9f2a0d1e9d3` |
| `lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `lakefile.toml` | `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194` |
| umbrella `YulangClosure.lean` | `04a209f4aa4a9e8c2848aee11eb16befb6fe4e0b566d4683dd0705f96ccf3b2f` |

## Checks, resources, and mutual TODOs

Read-only SHA-256 checks matched every pin. A `python3` in-memory text audit returned `EXACT_P_PROPOSITION_WHITESPACE_NORMALIZED: MATCH`, no `sorry/admit/axiom/unsafe` tokens, the single intended import, and the single intended theorem. The first attempt used unavailable `python` and exited 127; the identical audit under `python3` exited 0. These are static source checks, not Lean compilation or proof review. No Lean, compiler, tests, Git, external contact or nested CLI ran. No `.olean/.ilean` was written or reused by this author.

Budget: cap 900 seconds, no renewal; exact active elapsed was not measured. Conservatively retain/charge the full grant rather than claiming unobserved time is reusable. No continuing worker work is claimed after this handoff.

- `P-INTAKE-1`, owner Luna: revalidate the frozen P/dependency hashes; compile the exact module through the authorized serialized verification; query exact signature and axioms; apply P to the Q-derived leaf in the unchanged `completeCallEntry_typed` proposition after both author STOP receipts. Required evidence is actual elaboration plus fresh nonauthor review. Falsifier: any elaboration failure, changed proposition/premise, unexpected axiom, missing consumer or pending suffix, or mode confusion. This is a request, not a grant to change dependencies or semantics.
- `P-SOURCE-BOUNDARY-1`, owner Luna/existing operational and source lanes: retain all stated parent blockers and their owning Call/Force constructors and consumers. P supplies syntax typing only. No new implementation TODO is justified inside this lease.

Next in-envelope author step: none; assignment stop condition reached. Pending primary verification, composition, fresh review and integration. Writer status: **STOPPED after freezing this revision**; writes cease with this handoff submission. Descendants: none; unresolved descendant leases: none. The handoff byte hash is sent separately with the frozen ID/revision so no self-referential digest is claimed.
