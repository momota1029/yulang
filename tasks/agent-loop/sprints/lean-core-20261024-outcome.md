# Original raw substitution and concrete core reduction

LEAN-CORE-20261024/r1. Baseline `23819fbf76d7de467e19a5edbe5222eaefd71d84`. Contract SHA-256 `c815ccfe4e6f98e888ec5b94851a10f8a780224b9e353f428c2adbedc094f9c1`. All11 dependency hashes match, including unchanged Contracts/CoreComposition and three Control modules. Whole original goal remains ACTIVE/OPEN; compiler implementation excluded.

## Before / after and parent status

Before: original raw type/value/computation vocabulary and executable substitution were absent from Lean; Control's registered body relation was assumed. It also kept the current stack unchanged, so direct let/Handle/mapop entry was not represented there.

After: named raw constructor trees and four binder namespaces, immutable identity atoms, executable capture-avoiding traversal, and raw renaming/substitution identity/composition are kernel-checked over every Raw/Forest. This is a raw syntax algebra; constructor arity/sort/original typing remain unproved. The original full typed-substitution V1 is NOT closed by this algebra.

The explicitly typed source fragment is exactly **unit/variable/delay + Ret/Force/let**. Its contexts are partial Nat→OptionTy functions with a genuinely empty context. Typed renaming/substitution and `substitute_top` are proved, and `substComp_raw/single_raw` show their executable raw correspondence. Let/Force principal rules use actual bodies and substitution; syntax-bearing bind frames are pushed before the unchanged suffix. Closed progress and arbitrary finite-step preservation follow without a body-safety assumption.

`RawStep` includes an actual incorrect unit-Force→Bad rule. `raw_step_lifts` proves that EVERY raw step from a closed typed fragment image corresponds backwards to a concrete fragment step; this rules out proving safety only of a chosen safe transition subset. `raw_finite_safety` uses the existing root Prefix over all finite raw traces and proves a typed image, Bad exclusion and a typed return or next step. RawStateTyped is syntax image plus independent derivation, not reachability/safety. View/graph/type-application operands are not declared Bad merely because their surface is not Delay; their original normalization rules remain absent.

**Fixed outcome is partial.** Actual substitution and concrete entry/reduction obligations have been removed for the stated fragment; raw algebra covers the common vocabulary. Full original typing/substitution, nonfragment principal rules, complete registered-body interpretation and syntax-bearing stack-prefix bridge to Control remain OPEN. No full V1, BodyLaws, all-language principal preservation or whole-language soundness is certified. Original full scope is unchanged, not reduced to this fragment. No Core→Nat cast or permissive dummy analysis/certificate was introduced. The existing Control body hook remains unchanged.

## Coauthorship / repairs

Producer actual FINAL/STOP froze three unchecked candidates:

| File | Producer SHA-256 |
| --- | --- |
| CoreSyntax.lean | `5617778afc1335cb45e7f022e24639cc19547b17c9e0d38d21fd2ae8cff4ba3e` |
| CoreSubstitution.lean | `958d30e18e717056a44cec154fa043e815d2ded669cd289c9251ee25fb4dbbe3` |
| CoreExecution.lean | `c326f84fb2d312978476fccdeed3515fa63c088225c29d19ac42049801fccfdb` |

Producer wrote the raw vocabulary/traversals, fragment substitution and principal/entry proof candidates; it explicitly reported partial scope and the missing Control bridge. Primary took the three leases after STOP. Initial checker rejected an undefined Context (auto-implicit arbitrary sort), a reserved pattern name and a resulting finite proof failure; a constructor-name linter warning was also fixed. Primary defined partial contexts, adapted typed renaming/substitution, and proved full raw algebra, embedding commutation, closed progress, raw forward/backward correspondence and raw all-finite safety. Char raw content uses String rather than a single Unicode scalar; validity remains extrinsic.

Primary authored proof extensions after the initial syntax/typing check, and repaired three definitional-equality goals in lifted substitution by exposing the actual binder cases. Final full project checking succeeds. Independent reviewer is not an author. No failed proof/placeholder remains in the frozen mathematical files.

## Actual verification

Primary sole verifier: official task-local Lean4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; same verified distribution as prior sprints, no global setup change. One CPU affinity, `-j1 -M1024`,120sec process timeout. Dependency-order module checks, final `lake build` and `lake env lean -j1 -M1024 YulangClosure.lean` returned exit0. Final check had no warnings. No compiler build/tests/probes.

New export audits:

- `Original.substituteRaw_composition`: standard `propext`, `Quot.sound`.
- `Original.substComp_typed`, `single_raw`, `raw_step_lifts`, `raw_finite_safety`: standard `propext`.
- Existing root/control audit results unchanged.

No project axiom, sorry/admit, unsafe or native-decision escape is used. These standard Lean foundational dependencies are not claimed absent and do not establish missing original typing/semantics.

## Frozen independent review inputs

| Path | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/CoreSyntax.lean` | `293c550dca8550fc31eb997bcb0cac490e91db3860175b337c84dac954e5cd04` |
| `notes/theory/lean/YulangClosure/CoreSubstitution.lean` | `980a7b196d398af84ecd681b057030d4a7d2eb7f9a36d143432fd01819656f35` |
| `notes/theory/lean/YulangClosure/CoreExecution.lean` | `e2f348e696a2f22c69ac7e95270a4020e6aaa638e59a5e271356880baa248e87` |
| `notes/theory/lean/YulangClosure.lean` | `3a6b610ab3041f531445dab0605cb838273c76dd3a3daec144c7a08cbbcd9ff0` |
| `notes/theory/lean/README.md` | `056480aeb5bbc09169b9b22dcad90100b1b9d8294b992f51f8447a1476dd572f` |
| `notes/theory/2026-10-24-lean-core-correspondence.md` | `33743dd160e9cfd904ae303904d830e6716d7553d2e6ba3703affa3c2528e44b` |
| `docs/yulang-whole-proof-closure-ja.md` | `68d12bcd3758c17283683061ae82a6d8acd8141795bc7e74c539e9ada558d892` |
| `docs/yulang-proof-index-ja.md` | `c847f492915570945e5996231643705e034981f6d8f8dab1d570608d9a633662` |

## Review and exact remaining owner

Independent `/root/astra_semantics_review` returned actual FINAL/STOP accepting the stated raw algebra and typed fragment. No BLOCKING/MAJOR findings. All supplied output/contract hashes matched; all three new modules were read. Reviewer confirmed cross-namespace shift, immutable atoms, typed substitution scope, raw embedding, both let rules preserving suffix, every raw successor covered by raw_step_lifts and exclusion of forceUnitBad. It confirmed full typing/principal/Control bridge limits; checker receipts were not rerun.

One MINOR finding distinguished the source eabs term formal from the chosen raw evidence namespace. Primary clarified the future lexical encoding: only occurrences resolving to that binder map to evidence indices; other value locals/shadowing remain distinct; eapp substitutes into that namespace. This encoding is explicitly not implemented or relied on by the checked fragment. CoreSyntax changes after review are comments only; README/correspondence status/clarification are prose only. No proof theorem changed, and no extra checker/review was needed for these nonmathematical edits. Primary accepts the reviewed limited result; original parent remains OPEN.

Next original owning work: define full constructor-specific well-formedness and typing on the same raw vocabulary, including type/evidence binders and one-value intersection; discharge the original principal rules and connect syntax-bearing frames/values to the control machine. The existing algebra and proved fragment are reusable, but their scope must actually be extended. Do not make another opaque interpreter or rename BodyLaws as its own proof. Full Call/Resume/μ/∀/nominal/tuple/record/variant/graph/primitive/perform/handler/mapop/eabs/eapp, actual metadata/full observations, source initialization, native correspondence, extrusion/intrusion/birth-SCC A/B, source-scoped coverage, principality and inference termination remain OPEN. AH/RZ are unreviewed and unused.

## Resource and integration

Actual direction30sec FINAL; producer190sec FINAL/STOP; reviewer80sec actual FINAL/STOP. Full grants charged:9950+30+190+80=10250 cumulative,300thissprint,max1activeAstra, no automatic renewal. Requested inherited Astra/medium; observed model/effort/elapsed UNKNOWN. No descendants. Original checkout unknown writers stay quarantined; protected questions remain excluded.

Only explicit proof/doc/state paths are intended; mathematical Control/Contracts/CoreComposition remain unchanged. Primary adjudicates review, runs static new/changed-file checks and inspects the full intended outbound range before ordinary authorized push. No force or unrelated staging.


### Post-review nonmathematical updates

- `notes/theory/lean/YulangClosure/CoreSyntax.lean`: `1253b796473c1cca0ef21e8819b6e87575d7f5cdd9f26fc4e5f10b59ef7df712`.
- `notes/theory/lean/README.md`: `d2ad32c5b2fa79881e972c53f9d890656fe19e099dd29d5d7e164c466889c3a9`.
- `notes/theory/2026-10-24-lean-core-correspondence.md`: `4dd2b9dfd2580c614129e3701be47aea979c548542955d5150e184805133ccbf`.


### Final static and integration audit

New/changed relative Markdown link targets exist; no all-historical-link claim. New file whitespace and mathematical-module proof-hole/project-axiom scan passed. Frozen lease hashes match; current state remains below16KiB. Current proof workers all STOP at integration; the original worktree unknown writers remain reserved. Explicit intended paths exclude questions and generated .lake. Primary checks the staged diff and full outbound range before ordinary push to the inspected research branch.
