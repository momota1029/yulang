# R23 adjudication — source-scope authority blocker

Sprint: `FULL-PAPER-TYPE-SUBSTITUTION-20261026/r23`  
Contract revision: `r1`; SHA-256 `7fde0c40896ce366d403e394ddcb397d595a3bc80c13e0d21bc6a889fef7e18e`  
Baseline: `9d1962d56872f551f20476b0578002c49f7d5f1d`  
Outcome: **SOURCE AUTHORITY BLOCKER; semantic phase remains blocked.**

## Decision

Accept the frozen source-only handoff and its independent review. The handoff identifies the exact missing premise: a source-grounded relation between the stored body's declaration/graph contexts and the original caller contexts under entry-local type instantiation. The minimum context equation under investigation is:

```text
mapDeclarationTable σ D_body = D_call
mapGraphEnvironment σ Xi_body = Xi_call
```

Equality is only one possible bridge; a source-authorized weakening or scope-opening construction could also work. The paper and accepted Lean artifacts inspected in R23 do not establish any such bridge. This is an authority/evidence blocker, not a counterexample to the paper, not a proof that no embedding can exist, and not a theorem result.

The accepted `PaperComputationTyped.typeTransport` remains applicable conditionally: given a genuine body derivation at `D_body/Xi_body`, it produces a derivation at the mapped contexts with the instantiated body and result. That algebra does not identify those mapped contexts with `D_call/Xi_call`. R23 therefore creates no `TemplateBodyTyped` judgment, no instantiation theorem, no examples, and no audit artifact.

## Frozen evidence and review

- Worker handoff: `tasks/agent-loop/inbox/paper-typing-subst-r23.md`, SHA-256 `0bb37512743ab279a83ef7e4d35dddd97e435dc516139246b3f6fd317f6727ec`.
- Independent M1 source/spec review: `tasks/agent-loop/inbox/paper-typing-subst-r23-review.md`, SHA-256 `64d7c36797080afde96019298690a2ce487bfa44327f624bf0093c5afb038d8f`. Disposition: **ACCEPT SOURCE-GATE STOP; no blocking or major findings**.
- Contract SHA-256: `7fde0c40896ce366d403e394ddcb397d595a3bc80c13e0d21bc6a889fef7e18e`.
- All eight frozen input hashes matched at worker intake and independent review.

Review explicitly checked the strongest apparent counterevidence: closed-table one-step preservation (:1089–1105), actual template expansion (:327–329, :1878–1879), shared graph typing/extension (:264–269, :981–990, :1141–1146), and forall freshness (:238, :2058–2073, :2104–2110). These constrain a future proof but supply no generic stored-body-to-caller `D/Xi` embedding. The review also confirms the handoff does not treat arbitrary context non-invariance examples as valid source configurations or counterexamples.

## Execution and Git receipt

- Proof worker `/root/r17_forall`: fresh R23 receipt recorded before work; all leased paths reconciled; source audit only; writes stopped; no descendants.
- Independent reviewer `/root/r16_independent_review`: fresh receipt recorded before review; handoff unchanged; report frozen; writes stopped.
- Lean/Lake/checker calls: **0** for both worker and reviewer. No Lean module, audit source, generated cache, Rust change, test, or dependency change.
- Static repository check: `python3 tools/agent_sprint.py check` passed after state updates. This is tooling consistency evidence, not mathematical verification.
- R23 admission, worker receipt, source-audit start, blocker handoff, reviewer receipt, and review were committed and pushed. No accepted R22 source was changed.

## Parent application and remaining owner

R23 closes no mathematical parent premise. R22 remains an accepted signature/resolution/argument-typing prerequisite only. The first unresolved item is `R23-TEMPLATE-CALLER-CONTEXT-EMBEDDING-1`, owned by primary semantic/source-proof intake: locate an authoritative body-context schema or derive a source-justified embedding that preserves the exact resolved table/body and shared graph identities. Any closure, freshness, or weakening assumption must come from its governing source owner.

Until that gate is resolved, do not continue the conditional semantic construction or claim registered-body typing. Full-paper simultaneous substitution, R18 correspondence, omitted rules, inference/executor semantics, original A/B, source/native/Rust correspondence and production remain OPEN. The Force(Int) signature-only falsifier and the positive polymorphic example remain unconstructed and unchecked. `NO_SAFE_CODE_SLICE` remains the implementation-lane disposition.
