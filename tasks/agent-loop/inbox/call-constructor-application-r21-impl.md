# CALL-CONSTRUCTOR-APPLICATION/r21 implementation application — revision 1

Assignment: primary Luna/high, read-only, R21 contract SHA-256 `94a586910611e74d7f9da6330e3962d9e5a5f32f934965c55ded5ecd5ef0137e`; manifest SHA-256 `d814136808b65b33e20c142d91f3c10e2ba757513a6ce1aaa074d30654131c78`. Outcome: **owner-specific NO_SAFE_CODE_SLICE** for the selected source Call → native producer/ordered ports → transported consumer equation. This is a finite source-owner audit, not a global impossibility result or independent review.

## Authenticated direct inputs

The 19 entries of the R21 manifest were SHA-256 checked before body inspection; all matched. The five implementation owners are the exact R18 snapshot files:

- `candidate_effect.rs` `7c8e4fe5270fd45cecece80dfbbdff81aa8f294546687938bf89212325fc146b`
- `candidate_context.rs` `be1be2277d54288ba4ae542e003dabc294031c29cb26b2b5d0454b0d1c102bd0`
- `candidate_scheme.rs` `3eb9ba3b414dd0e40f49957e0ee2b9de1ba21fd86dff718111d1b5030ccac6b7`
- `candidate_call.rs` `fdc39e01fa3665b4dc14e167973de63b275eb0280b831e340b6cdcee5ed0fc3f`
- `shadow_apply.rs` `8db4bae1b79959161b6b0dc4d516164b0e756eb8cbc73896bb4a4545a0b0ebf8`

R18 source handoff `tasks/agent-loop/inbox/latent-demand-transport-classification-r18-source.md` authenticated at `9878f83cd1410da9c83305b711bc234b7424617776b46844602ebbd692d8c383`. R20 artifacts were authenticated against the R21 manifest; R20 remains unreviewed producer evidence. No R20 review file or independent ACCEPT exists.

## Same-App row mapping

The R18 handoff records four replay rows for two source Call occurrences:

| Rows | Original source occurrence | Replay rows | Lower positive root / lower relation | Upper copied negative root |
|---|---|---|---|---|
| 0, 1 | call0, expression1, occurrence2, `f 1` in `invoke` | module uses1 and3 | 310 / 58; 349 / 116 | 299; 338 |
| 2, 3 | call3, expression6, occurrence22, `h z` in `local` | local uses5 and7 | 402 / 188; 439 / 245 | 393; 430 |

The two rows for each source Call are separate use/route instances. Call occurrence alone therefore does not identify one transported consumer. The R18 source handoff records lower owner-emission admission/readback values 56, 113, 184, and 240 for rows 0–3 respectively. It also records FreshUse and Replay ancestry/typed FunctionPort evidence before the observer’s first failed positive-node selection. The focused R18 fixture failed when it selected an element from empty `emission_cases`; it is finite diagnostic evidence, not a successful semantic validation or source-qualified counterexample.

## Producer-to-consumer equations found

`candidate_effect::candidate_bound_origin` assigns `BoundAdmissionCause::OwnerEmission { processing }`, where `processing` is the active candidate relation. `candidate_bound_origin_with_evidence` chooses the origin from the explicit pair, processing relation, or `bound_pair`, then requests a candidate context relation. The `BoundAdmissionCause` carries no original semantic Call identity, complete `TypedCallCert_Dec`, source incidence derivation, callable-image derivation, or four-port tuple.

`candidate_context_bound_for` constructs a candidate pair from the bound and origin, reuses a matching processing relation or creates an origin relation, creates a derived child relation, and attaches the bound. `BoundAdmission` retains bound/origin/relation/cause/coverage; `BoundEmission` retains the admission, bound, physical slot, and readback. The physical slot is owner row/lane/index. These records establish candidate-local bound and physical emission incidence; they do not name which original C-Call/J-Owned constructor supplied the producer or its four ports.

R18’s `authenticate_replay_ancestry` independently checks exact FreshUse/Replay relation incidence, bound endpoints, and four ordered FunctionPort dependencies. Its field order is Argument, ArgumentEffect, ResultEffect, Result with Value/Effect/Effect/Value kinds. The corresponding candidate-native `Node::Function.children` order is `(argument, argument_effect, result_effect, result)`. This authenticates the candidate relation/graph tuple when its checks succeed, not an original source owner.

The R18 captured-graph observer joins a route by retained use/context, original call/root demand, unique captured source relation/bound, imported evidence snapshot, remapped scope/input, and a negative Function node. It reconstructs positive/negative Function ports from retained graph nodes and terms and compares typed relation pairs. R18’s four rows all stop at `positive-function-node-absent`, which does not distinguish zero matching nodes from multiple matches. `candidate_call::authenticate_scoped_apply` separately checks the local HIR Apply shape and FreshUse route; it does not join that candidate owner to the original selected C-Call/J-Owned owner or lower OwnerEmission.

Thus the first missing implementation-side equation remains:

```text
one original source Call derivation and shared xi
  -> the same candidate Call/use owner
  -> its actual lower OwnerEmission and four ordered typed ports
  -> the same captured/transported consumer after FreshUse and Replay
```

No inspected equation supplies this whole join. Reusing an equal term, endpoint, bound membership, physical emission, or candidate HIR call as the source owner would be circular or would change source identities. The R20 tuple and row evidence are reusable observations, not an independent proof of this missing source/native bridge.

## Scope and stop receipt

This audit read only the five R21-pinned Rust source files, the R18 source handoff, and the R20 artifacts explicitly pinned in the R21 manifest. It did not read `candidate_extrusion.rs`, R19 overlays, or current working-tree Rust. No source/code/test edits, Cargo, tests, build, formatter, Lean, checker, or Git command was run by this assignment. No code lease or execution authority is requested.

First clock observation / conservative start anchor: `2026-10-28T14:17:45Z`; freeze-write observation: `2026-10-28T14:19:15Z` (90 seconds on the conservative clock interval). CPU/RSS are UNKNOWN. No descendants or scratch outputs. All original theorem, source/native, effect-hygiene, implementation and production gates remain OPEN.
