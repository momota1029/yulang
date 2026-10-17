# NPAIR source-admission failure read lease

Sprint: `npair-source-admission-correspondence-20261018`; versioned resource
continuation from the 2100-second cap to 2460 seconds. The extension is adopted
by Luna: 240 seconds of primary read-only owner tracing plus 120 seconds of
fresh review, charged in full at issue. Astra0; no new worker, test, code write,
or semantic change is included.

## New exact read owners

These syntax paths were hash-pinned before reading their contents:

| Path | SHA-256 | Exact purpose |
|---|---|---|
| `crates/yu-syntax/src/pattern/mod.rs` | `1b608422c93ce0f6947125a9b1ea88314a48b3a5e45030ed23e5154492ad7883` | Pattern parser and named formal parameter syntax producing the target Lambda header. |
| `crates/yu-syntax/src/pattern/delimited.rs` | `9da9ec948775b438a85ca3f27c2805254a4f4171caddb54cabe44e563d017029` | Delimited pattern children and annotation attachment. |
| `crates/yu-syntax/src/type_expr/mod.rs` | `2e08a49960cd4010ba39641ae509afb7cf59711f1464d3349f5f6db590ebf01f` | Type-expression parser and function-arrow structure. |
| `crates/yu-syntax/src/type_expr/delimited.rs` | `db6335a8f6c95bafb72d096fe241201202938c5869fb89a5e3c43758021651b6` | Parenthesized type groups and bracket-row attachment. |

Existing HIR owners remain at the exact hashes in
`notes/progress/2026-10-18-npair-source-admission-read-lease-amendment.md`
(`a23049d05a35244a4434c622873e4db060d64fa50e2a6768bcedb936380d546f`). The
unreviewed solver candidate is pinned at `candidate_source.rs`
`8d695bd9c71ed8b145456917e973528c1c87c5728073615641cb59f55fdbb2f0` and is
read-only during this continuation.

## Fixed result and boundary

Determine the first CST/HIR shape or source-key lookup that makes
`lower_module_with_local_source` return `StructuralProjection` for the two
recorded fixtures, or establish the minimal authentic syntax/HIR carrier shape
for the adopted nonempty concrete-only negative formal port. Output is frozen
in `notes/theory/2026-10-18-npair-hir-first-failure.md` and its assignment inbox
`tasks/agent-loop/inbox/20261018-npair-hir-first-failure.md`.

This read lease does not authorize syntax/HIR edits, new tests, executable
probes, compiler changes, or any change to the adopted row class. Stop after
the owner-level obstruction and the smallest repair contract/falsifier are
clear. The prior solver code delta remains unreviewed and unintegrated.
