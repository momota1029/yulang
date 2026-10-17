# Luna handoff: candidate source Function inference introduction

Sprint: `receive-function-introduction-proposal-20261017`, revision 1, contract SHA-256 `eeca47fc455c5aac9b5f9bb4e5ce6b10b7921599a07a693e2c4ac668442a7503`.
Assignment / revision: `receive-function-inference-introduction-proposal` / 2.
Author: Luna, sole author. Outcome: unselected source-rule proposal. Review: not yet run; preservation lane starts only after this proposal is frozen and pinned.

## Parent and fixed scope

Original FORWARD-FIRST-CALL A/B claims, universal alpha, source domain, actual providers, punctured contexts/worlds, raw resumptions and finite futures remain unchanged. Immediate source case is original `g(Unit)` c2 at `F2`, `sigma2`, `Delta2`, and shared `xi=(nu,K,D)`. The proposal creates no actual provider, role/entry, receipt or successful comparison.

## Frozen proposal

- File: `notes/design/2026-10-17-receive-function-inference-introduction-proposal.md`
- SHA-256: `a021cd088a9b0bab768a3fd509602012dae061c54b13a1353045aa80c15b71d4`
- Status: candidate, unselected; not implementation authority.
- It gives a concrete `Gen-CallView?` source-generation schema and compares the exact selected `Strict(I,formal:A,R,IF)` constructor with a role-indexed CallView bridge. It derives fields from source occurrences/local laws, forbids opaque whole-F2 inputs, retains the existing descriptor universe and Option 2, and names the joint embedding equation as the key open premise.

## Proposal author pins

All hashes rechecked before freeze:

| Dependency | SHA-256 |
|---|---|
| `notes/theory/2026-10-17-receive-inferred-function-view-formation.md` | `7cb867df64f1d931b1667f33a6c323448d687c5d0d7fdcf9bac7535577f72590` |
| `tasks/agent-loop/inbox/20261017-receive-inferred-function-view-formation.md` | `a60a7ca1e5ea6b9d30adff7f1141b183bc8b9c8f6b8eda1302664721e7081e3a` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-08-captured-closure-constructor-definition.md` | `6292b778e804988b32d48df663061d01e1593340ccb584fb6a8c0565bd817cfd` |
| `notes/theory/2026-10-08-captured-call-closure-introduction.md` | `0f8adcf70a72d1f46bd4ca95f3984554d8cf2ff6af6434b679e991e346ffd50f`; selected theorem-body pin `76d54ceb51de6836c3ecff1e520fa0ce99b881e10ccca85d75c8a4599b33b410` |
| `notes/design/2026-10-08-call-source-interface-definition.md` | `20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c` |
| `notes/design/2026-10-08-native-signature-formation-definition.md` | `e6c6cf995a3618172e45b4f8cdf4578313c057c6ec1e3e118c4dc11b6f162ab9` |
| `notes/design/2026-10-08-contextual-function-membership-definition.md` | `0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| `notes/theory/2026-10-16-first-call-joint-forward-preservation.md` | `f71cc442bcccb23f7e6f1aa6221b089abb8c24d1c4ce01fecef37995541c16b6` |
| `questions/2026-10-05-production-function-denotation/approved-answer.md` | `7e7f3c717b16a70fc754c930a1654666c8b61a89a4861fca27b0ae3fa5f1890a` |
| `questions/2026-10-05-production-function-bound-membership/approved-answer.md` | `d9ddea04a44d2307cf587bc4ae9b2a1c50d062c4077306a5bf9ea9da00eca179` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |

## Preservation assignment and falsifiers

After Luna acknowledges this frozen hash, the sequential Astra author may attempt only the four preservation stages in the sprint contract: telescope/record correctness; local `WF_Dec` and joint embedding for the proposed clauses; lawful substitution/generalization/use preservation; exact c2 application. The author must distinguish a result conditional on a missing law from a proved constructor.

Falsifiers include: any field depends on a later Return/receipt/Q; `Unit` selects actual role/entry; the map requires whole F2 or `WF_Dec` as an input; one field witness is lost under `DescMem`; independent Option 2/context/future members are dropped; a shared witness is freshened across aliases; or the selected `Strict` prerequisites are not supplied. A falsifier may invalidate this candidate but cannot narrow the original theorem or select another semantics automatically.

## Review boundary, implementation and runtime

Fresh independent compiler_referee and spec_auditor review the combined proposal/proof after both freeze. Neither author reviews the bundle. Any new interpretation remains unselected pending user adoption. No code lease, compiler edit, tests, build, probe, execution, source `T`, native MODEL, production conformance or parent closure is supplied.

Luna's proposal work is complete and frozen; no further writes under this lease. Proposal author elapsed time, model telemetry and active-time breakdown were not instrumented. No independent result is claimed. Astra remains NOT_STARTED until Luna confirms this exact hash as the proof input.


## Revision 2 clarification

This revision corrects the revision-1 summary after the independent compiler review. The proposal is an obligation/schema outline, not an implemented or mathematically complete constructor. Its source premises still require a real inlet/role introduction with an owning telescope. The proposal artifact bytes remain unchanged. Revision 1 is preserved in Git at commit `79b2d9a4f`; the preservation proof records its exact hash as an input.
