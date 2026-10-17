# Fixed-c source selection and scoped collection closeout (2026-10-18)

Sprint `npair-fixed-c-source-selection-scoped-collection-20261018`, rev3, baseline `d9e6949a4cdc2d1899f55d5e7a75a014d4630606`, closed with parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR` still OPEN and original-condition closure **0 → 0**. Original quantifiers, source domain, receive route, C1/C2 and F1/FK1 are unchanged.

## Proof result

Frozen source audit [artifact](../theory/2026-10-18-npair-fixed-c-source-selection.md), SHA-256 `b3e8fb90bb425901c416ec4aeadcf141820a447fdb699c788897dd1afc440ba8`, and [handoff](../../tasks/agent-loop/inbox/20261018-npair-fixed-c-source-selection.md), SHA-256 `5f38998ddfa52078912bd966bd9390470300ee68fe6245bc5bb72aa0a92a43fc`, received CLEAN bounded independent review. It confirms conditional complete-result membership from independent Sigma while preserving `A_decl`; neither full-f nor CallMem selects the original fixed `c` at actual `r.s1`. SWR1 remains unadopted source-owned interpretation content and establishes no compatibility or parent premise. No admitted counterexample was found in the separate source-case audit. No original condition closed.

## Implementation result

The exact diagnostic submission received CLEAN compiler review. One reviewed command ran once:

```text
YU_SCOPED_COLLECTION_DIAGNOSTIC=1 timeout 120s cargo run --offline --manifest-path crates/yu-solver/Cargo.toml --example research_source_registration --features shadow-apply-candidate
```

It exited **2** at `candidate_source.rs:1098`, where the scoped Apply-callee spine rejects `Name(Local(_)|CatchBinder(_))`. The fixture's `g ()` reaches this source-provenance guard. No candidate inference, source-call or scoped relation was returned. This is not a resource-limit failure. The exact existing `LocalSourceIndex → local slot → Action::Local/Install → Capture/FreshUse` route exists, but no explicit typed edge joins the Apply source input to the captured supplier. A Local-only relaxation changes admission and remains unadjudicated; CatchBinder remains unsupported. The evidence and hashes are in [scoped collection note](2026-10-18-npair-scoped-collection-repair.md) and its inbox. The fixture was restored to SHA-256 `969e20e0f38a2c341a96ff4fe07028bf567ca134e0fb24602fadf6e4c723d9c0`.

No semantics correction, source-call relation, Replay linkage, regression or production path was established. Environment-gated caller/occurrence diagnostics are provisional, reviewed instrumentation only.

## Next target

The next sprint will make the output-origin seam explicit: determine whether the original source contribution can be connected to the complete output binder without replacing fixed `c` or narrowing the original source domain; in parallel, derive a typed Local-supplier edge from existing owner records and prototype only that justified route. The next exact selected packet and leases are recorded in `tasks/agent-loop/current.json` and its successor contract. Parent remains OPEN; no soundness, principality or termination closure follows.
