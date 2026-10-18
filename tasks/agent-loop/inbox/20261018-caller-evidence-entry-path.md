# R26 Luna entry-path audit

Sprint: `caller-authentic-evidence-intake-20261018-r26` rev1, SHA-256
`763f10b84abb5a597526e76708a7113c40c5450034db03f2c814a8f8be2947fd`.
Baseline: `8de842c4d34ae0fdc191b72acfe64ef75b77fc67`.
Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN,
closure 0; this is repository path evidence, not semantic nonexistence.

## Inspected owners and trace

1. **Public caller / preparation:** `tools/inference-playground/src/lib.rs`.
   `infer_with_scoped_experiment` and `execute` reach private `prepare`, which
   parses caller text, then calls `lower_module_with_local_source(...,
   SemanticImports::empty())`. The operation-v1 helper does the same. Inference
   receives `hir.clone()`; ordinary execution passes the resulting HIR to
   `RuntimeProgram::from_hir` with `RuntimeEvidence::default()`. The research
   operation-v1 path separately derives candidate/runtime receipts from this
   HIR. No caller-owned semantic registration/world/context is accepted by
   these entrypoints.
2. **HIR source declaration owner:** `crates/yu-hir/src/module.rs`.
   Lowering plans parsed root items, admits plain top-level bindings, assigns
   `DefId`/`DefinitionRootId`, records parse-branded definition source keys,
   and retains local-source carriers. R25's `SemanticImports` can structurally
   retain a payload for a parse root, module identity and admitted declaration
   key. Its docs explicitly do not authenticate payload contents. Repository
   search finds `with_caller_evidence` calls only in
   `crates/yu-hir/tests/semantic_import_binding.rs`; no production caller uses
   it. Existing production callers still pass `empty()`.

## Earliest absent input and code-slice decision

The first missing value on the selected path is at the public caller/host
adapter: no independently constructed context tied to the actual source
registration is supplied alongside the source. Consequently there is no
observed `(source/declaration, scopes/dependencies, W0,xi,h0; j0,a0,license)`
value or introduction derivation for HIR to retain. The Rust call-site absence
is not proof that no external host could construct such evidence. R24 assigns
evidence construction to the caller but names no actual provider or introduced
judgment. The R25 opaque payload API supplies neither.

**NO_SAFE_CODE_SLICE.** An adapter calling `with_caller_evidence` with a new
wrapper, key, type marker or synthetic world would create the missing meaning
rather than transport observed evidence. A prospective implementation needs
an identified host/source-registration owner and the original guard/license
construction; the current HIR anchor is a binding declaration key and does not
by itself map an operation/member/signature registration. No compiler source,
semantics or tests changed in this read-only lane.

## Frozen sources

- `tools/inference-playground/src/lib.rs` —
  `bdf996d0264e252e345c05bc77b2adcf625120281244171f0054f1d87a8d1e1b`
- `crates/yu-hir/src/module.rs` —
  `c40ebde1755d300c83aafba0a81a85d19ed5200dfc2163ab72c8a3bb08baf29a`
- `crates/yu-hir/tests/semantic_import_binding.rs` —
  `b9b3aa5f0d1a3e6783d2e8b53e2d4edd13b5c4ac43538d71216662bcd19399d1`
- `notes/progress/2026-10-18-r24-caller-binding-closeout.md` —
  `da8910aa088db1455ab5e3725429621333ecb319978c933491bd6310f8bf7007`
- `notes/theory/2026-10-18-caller-evidence-source-binding.md` —
  `b6a51aa9b4cd716382f4b180a0c5a348dc1d84ced263d08a461b727b6b344df5`

No tests/builds/probes were run (R26 contract does not authorize them).
