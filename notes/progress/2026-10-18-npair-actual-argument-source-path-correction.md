# Actual-argument source-path correction

Sprint `npair-actual-argument-ingress-20261018`, contract rev1
(`c0754dc6de94c15e923ce24cc58b8208d0934dcf7bc92abcae34589185ec9d32`).
This correction supersedes unsupported absence/refusal claims in
`2026-10-18-npair-actual-argument-source-path.md` and its inbox handoff. Those
frozen bytes are retained as the submitted record; the implementation review
found one major evidence-boundary error.

## Corrected result

The one authorized command ran and returned exit code 0. Its output reported no
structural recoveries and HIR diagnostics, including `UnsupportedExpression`
at the added `received` binding. The example continued on partial HIR. This
establishes neither successful acceptance nor refusal of the source binding.

The pinned harness prints selected LocalSource information for `f0` and
`receive`; it does not query or print LocalSource for `received`. Therefore the
run does **not** establish whether `received` has a LocalSource, whether it was
collected, or whether an outer Apply was represented in the collector. The
diagnostic alone cannot establish absence: the same output reports
`UnsupportedExpression` for existing `f0` and `receive`, whose LocalSource is
available. The claim that the new binding had no collector coverage is
withdrawn.

The output still exposes the pre-existing `receive` body shape: `f ()`, its
binding to `g`, and `g ()`. It does not establish that the added outer binding
was connected to this body through an actual Call, nor establish the actual
argument/formal comparison, same returned R1, complete Function child
comparison, `s1 -> D`, or either ordered Replay input. Those edges remain
unestablished, not refuted. The parent remains OPEN and original conditions
closed remain 0.

## Next discriminator

Do not assume the diagnostic identifies the HIR lowering owner or implies a
lowering defect. A successor lease should inspect how the authorized example
selects LocalSource output and derive the added binding's HIR/LocalSource and
collector status directly. The proof-side missing native-demand constructor
remains `shadow_apply.rs`; full Function-child dispatch remains `lib.rs`.
Pin current hashes and lease these exact owners before reading. Then connect
only observed source data to the existing candidate constructors and ordered
Replay inputs. If the outer Apply is not exposed, identify its actual producer
from leased source evidence before assigning a lowering owner.

Review: independent implementation/compiler review found the above major
overclaim in the frozen submission. This correction records the minimum repair;
it does not claim a new experiment or code change. Proof/spec review of the
separate actual-argument artifact was CLEAN. No tests/builds ran beyond the
single contract-authorized Cargo command. Fixture remains restored to SHA-256
`969e20e0f38a2c341a96ff4fe07028bf567ca134e0fb24602fadf6e4c723d9c0`.
