# Module contract registration definition sprint closeout

Sprint: `module-contract-registration-definition-20261017`  
Contract: revision 2, SHA-256 `a1214caca4d0c8ab115c0d4925515bb5279e76c2579817304049955f0b98d17f`  
Proof: SHA-256 `074455cef680c22a4d0eb471406c7aa6945d7d85543769c1b57fdb5de0d73353`  
Handoff: SHA-256 `72c471b0adac1d76cc6e5a80d1ed2fa01c4ced8f83fac91e21455f0ef1e1eaf5`  
Adoption receipt: [scoped `Sigma_M` adoption](../design/2026-10-17-module-contract-registration-definition-adoption.md), SHA-256 `9b8f514416542e250e061e6cc459b5723cb0096f522ab7d21e57fe80cf53e837`  
Status: **CLOSED — REVIEWED-PARTIAL; one local premise adopted and applied**

## 1. Original conditions genuinely discharged

**One local source-registration premise** is discharged for the reviewed source under adopted `Sigma_M`: `MODULE-REGISTERED-ROOT-u_id@Sigma_M`. The proof derives `C_decl` from the typed `D_pub/G_id` source presentation, restricts the actual whole `mu_id` map to that graph, constructs the simultaneous image, and applies the adopted `MReg-Intro*` extension at the unchanged §7.2(2) indices.

This is an explicit semantic family extension preserving all old constructor meanings; it is not an embedding into unchanged `Reg_orig`. Therefore the count of conditions closed in the fixed old-family interpretation remains **0**, and global original theorem gates closed remain **0**. `MODULE-ROOT-ORIGINAL-COMPAT` and the existing IF/Call consumer applicability remain open.

Fresh compiler/source, spec, and architecture reviews were CLEAN within their bounded scopes. The adoption preserves old-only derivations and explicitly does not claim compatibility with global opaque predicates/consumers over an enlarged root domain.

## 2. Newly established implementation or test behavior

**None.** Read-only compiler/source inspection found `NO_SAFE_CODE_SLICE`: HIR identities and native FreshUse/Apply propagation do not emit the typed registration fields or total source/native map; `candidate_source.rs` and `candidate_call.rs` remain quarantined under inherited UNKNOWN writers. No compiler edits, tests, builds or runtime behavior changed. Astra allocation: **0**.

## 3. Remaining condition and next step

First next condition: prove whether an adopted `Sigma_M` root can enter existing IF-Insert/IF-Use and complete Call formation at the original scopes, with actual typed `q_f`, `Comp(E_f,A_id_use)`, argument Reify/carrier and all original checking clauses. Any new consumer case must preserve existing rules and full quantifiers; `R_M` cannot be passed as an old `Reg_orig` premise by renaming.

Native `Phi_u`/field correspondence, old/new admission and observation equivalence, F1/FK1, N-Transport, soundness, principality, termination and production remain open.

Resource accounting: proof600 + read-only source audit180 + compiler/source review180 + spec review120 + architecture review120 = **1200/1500 seconds**. The remaining 300 seconds are retired; no carryover. All authors and reviewers STOPPED; leased proof outputs FROZEN.
