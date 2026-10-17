# Sprint `npair-parser-row-key-separation-20261018`

Status: ACTIVE, primary-issued 2026-10-18.
Contract revision: 1.
Branch / compiler baseline: `research/simple-sub-intrusion` / `515b705f6879bd8fd4a57fd1f6732e11ea9c0a29`.
Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`; original claim, quantifiers, source domain and adopted semantics unchanged.
Dispatcher: `/root/npair_replan_dispatch`; recommendation adopted after independent major finding against unconditional SourceNodeKey injectivity.

## Fixed outcome

Prove the exact key-separation fact required by the explicit Operation root-result-row cache miss: in one accepted Operation signature, any earlier row that can seed the local cache is key-distinct from the root result row. Include parser recovery and malformed/recovered bracket structures unless the actual admission gate excludes them. Reuse only verified SourceNodeKey Eq/Hash and HIR transport. If any constructor case remains uncovered, retain the conditional address lemma and name that exact case. Do not claim a source collision without authentic input.

No semantic Operation projection, `At`, parent condition, or implementation is authorized by this source-identity packet. Original parent and quantifiers remain unchanged. Do not retry the supplier proof, narrow to error-free parsing, or infer behavior from enum names.

## Frozen inputs and direct source hashes

- Prior contract rev3: `tasks/agent-loop/sprints/npair-operation-self-effect-decision-20261018.md`, SHA-256 `0ab0e6a7353810204825ffd05815b2a42195a0915c5380c72831061b7355cd94`.
- Major review: distinct-start premise missing; no authentic source collision; Eq/Hash and HIR transport supported. Adjudication and earlier receipts: `notes/progress/2026-10-18-npair-operation-self-effect-decision-closeout.md`, SHA-256 `4efd9fccf44fd905a6e0e1446f019c18842d45f0dd27491aa63113fa06b8d3be`.
- Conditional cache lemma: `notes/theory/2026-10-18-npair-explicit-row-address-invariant.md`, SHA-256 `2796562ac2e359933ff5ac8ec58352a5b61b83264b5b88baa7ef8ce0065382ac`.
- Eq/Hash candidate (not accepted as unconditional): `notes/theory/2026-10-18-npair-source-node-key-injectivity.md`, SHA-256 `8ab47830c985e13a4823a8a707ad6ee0b3ff9bb970f68da752d517052f59eeb6`.

| Exact source owner | SHA-256 |
|---|---|
| `crates/yu-syntax/src/cursor.rs` | `f08aae49fcf048ad11890def7ef9cadab56825a63b8d87db44821a792fe9b142` |
| `crates/yu-syntax/src/type_expr/mod.rs` | `2e08a49960cd4010ba39641ae509afb7cf59711c1464d3349f5f6db590ebf01f` |
| `crates/yu-syntax/src/type_expr/delimited.rs` | `db6335a8f6c95bafb72d096fe241201202938c5869fb89a5e3c43758021651b6` |
| `crates/yu-syntax/src/full_parse.rs` | `24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8` |
| `crates/yu-hir/src/module/source_annotation.rs` | `b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f` |
| `crates/yu-hir/src/source_identity.rs` | `7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3` |

## One proof lane, exact outputs

**Parser row key separation — `/root/npair_parser_row_key_separation`, requested Sol/prover/high, cap 240s.** Trace the actual `BracketRow` constructors (including `type_expr/mod.rs:1608`), ordinary and recovery paths from `cursor::parse_root`, delimiter consumption, empty-width/recovery-node behavior, source-key minting, and HIR admission. Establish key separation for every earlier row that can enter the candidate cache before the root row, using start offset and green identity as available. A syntactic error is not by itself exclusion: only a pinned actual gate can exclude an input. If an indispensable owner is missing, stop at its exact symbol and keep the result conditional.

Write only:
- `notes/theory/2026-10-18-npair-parser-row-key-separation.md`
- `tasks/agent-loop/inbox/20261018-npair-parser-row-key-separation.md`

No code/tests/builds/probes/Cargo/compiler execution. After freeze, obtain a **fresh independent compiler/source review**, cap 120s, not authored by this lane or the prior address/injectivity authors. Luna owns 60s integration. Fresh envelope: **480s total**: proof 240, compiler review 120, primary 60, reserve 60. Astra0, children0. Previous 900s are fully charged. Effective runtime settings remain UNKNOWN without runtime evidence. At closeout parent closure increases only if a proof is reviewed and applied; this local identity lemma alone closes no parent condition.
