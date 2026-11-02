# R232 independent model-conformance review

Disposition: **PASS for MODEL-INCOMPLETE only. Theorem activation remains
CLOSED.** Parent-premise delta 0; no root or package closure established.

Reviewer: `/root/r232_literal_model_review`, fresh nonauthor `spec_auditor`.
The reviewer returned this receipt in its final report; it could not write the
leased output file. Luna recorded the returned receipt here without changing
the frozen producer artifacts.

## Authentication

The frozen R232 contract, model note and handoff match their dispatched hashes.
All eight direct dependency hashes match the contract:

| Dependency | SHA-256 |
|---|---|
| L1 adoption | `f69a11121b0bade01586293fbda5500c4264424c3ac568fd1336ebb1b2eec9b8` |
| Contracts | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| OriginalSourceSyntax | `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1` |
| OriginalSourceGeneration | `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef` |
| OriginalSourceInterpretation | `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef` |
| SimpleSubConstraintSyntax | `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6` |
| AbstractSimpleSubCore | `023635d283f9a00e906ec965a6eaa5595eab21f2b93f353a1d5ea0ede0bffb6c` |
| Root-first plan | `890fa8a5a1c88c6400e293870598750b285fe12075ad13cbd3e884cc71921c16` |

## Findings

**BLOCKING — candidate reciprocal bounds lack an algorithm derivation.**

The approved L1 rule fixes source literal meaning, not Simple-sub generation
(L1 adoption, lines 56–62; root-first plan, lines 80–89). The reference
Simple-sub `Typer.scala`, pinned at commit
[`9bae772624c23b52a93c1b226157e16898b4d9db`](https://raw.githubusercontent.com/LPTK/simple-sub/9bae772624c23b52a93c1b226157e16898b4d9db/shared/src/main/scala/simplesub/Typer.scala),
`typeTerm` lines 55–70, returns `IntType` directly for `Lit(n)`; result
allocation is lazy. It does not construct the proposed fresh reciprocal pair,
and its grammar lacks Yulang effect ports. The R232 pair remains an
unadopted candidate unless its relation to the actual selected generator and
source ports is derived.

**BLOCKING — reciprocal structural subtyping does not imply syntactic
equality.**

In `SimpleSubConstraintSyntax.lean:86–100`, let `B := atom b` and set
`ρ(.value, α) := union B B`. Then
`Sub (union B B) B` follows by `unionElim (refl B) (refl B)`, and
`Sub B (union B B)` follows by `unionLeft B B`. Both candidate value
constraints hold, while `union B B` is not the same syntax as `B`. This
refutes direct syntactic-equality readout. It does not refute a later semantic
interpretation that proves the terms equivalent.

**BLOCKING — original carrier and coordinate readout remain absent.**

`Term.atom` holds only a kind-indexed opaque `Nat`; source coordinate
allocation and an atom-to-original-carrier embedding are not supplied.
`SourceAssignment` independently supplies descriptor/value/root/event;
`LiteralAtom` assumes declaration and groundness and reads `.finalRoot`.
Those assumptions do not derive an arbitrary valuation's readout. The eight
payload-bearing forms agree between the original syntax and paper syntax, but
full payload values are not recoverable from base-type constructor tags.
Annotated synthesis, `writtenTarget` and `finalRoot` remain distinct. The
missing construction must retain the same `(q,r,e₀,ξ,ω)`, pure Return, and
enclosing permission, inflow, residual, Call, guard, future and conversion
obligations.

No approved source-semantic change is proposed or implied. No source form or
quantifier is narrowed; Rust evidence, source satisfaction, `LiteralAtom`,
and native success are not used as mathematical authority.

## Verification and boundary

Read-only definition, authority, baseline and hash inspection. Reference source
was inspected at the pinned commit; byte-hash retrieval failed DNS, so no
`Typer.scala` SHA-256 is claimed. No Lean/Lake, Rust/Cargo, builds, tests,
caches or file writes by the reviewer. Reviewer status: **STOPPED**.

The original soundness premise remains open. R232 proves no theorem and
removes no parent premise.
