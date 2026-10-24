# Structural raw finite-trace proof: frozen outcome

LEAN-STRUCTURAL-20261024/r1. Baseline `f1c08808ae575cdc3032442ac3c98f4e4a7c9ca5`.
Contract SHA-256 `eac1799aa53a7153a6d6ef3b138175c214c4a10b31f984799c56232238ed09ca`.
Status: REVIEWED_SCOPED_PROGRESS. Original whole goal ACTIVE/OPEN.

## Before and after

Before: unit/var/delay + Ret/Force/let, full raw substitution algebra, allfinite raw safety. After: same syntax, independent extrinsic typing, substitution and allfinite raw theorem extended to union injection/case, one-value intersection/choose, Top and Bottom elimination. Canonical forms and backwards lifting cover every successor in the enlarged RawStep, including malformed-unit Bad alternatives. The proof assumes no body preservation/progress.

Intersection typing has two Prop premises on identical v. Its computational rawProofBoth is explicitly distinct from the three-child rawBoth: only typing proof data is erased. Choose remains an actual step, selects the matching typing proof, returns the same underlying v. General explicit-evidence/runtime-View/metadata correspondence remains OPEN. No implicit full-language claim.

## Construction and checks

Producer /root/astra_corrected_machine, primary coauthor after actual STOP. Producer final exact candidates:
CoreSyntax `4c036531cdd599799d0b943b4c8e2f1398aa91f5cf32296d7d6c50be1ff7a001`;
CoreSubstitution `5f95f769acfb956e5d42c7cf3bcd61702a10a56fb0897f5d22f3bdc9882edd61`;
CoreExecution `928586bed14d0e466ec230a8d9a62e7dd2215085b71daf1c0a755e2d85f6bf1d`.
Contract and seven baseline inputs verified by producer. No descendants or generated outputs. First primary Lean check caught a shadowed renaming variable r in unionCase and unused simp arguments. Primary repaired after actual STOP; all three modules then exit0, no warnings. Subsequent lake build and root lake env lean -j1 -M1024 exit0. Official task-local Lean4.35.0,1CPU/1GiB/120sec check envelope; no compiler implementation/tests/probes.

Axiom audit: closed_bottom none; principal_preservation/substComp_typed/single_raw/raw_step_lifts/raw_finite_safety use standard propext. Existing raw substitution composition uses standard propext,Quot.sound. Existing Control/root audits unchanged. No project axiom/sorry/admit/unsafe/native_decide added.

## Frozen review target

| Path | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/CoreSyntax.lean` | `4c036531cdd599799d0b943b4c8e2f1398aa91f5cf32296d7d6c50be1ff7a001` |
| `notes/theory/lean/YulangClosure/CoreSubstitution.lean` | `6d7d5da463480fbb618072b086c5092452575c56526579e4f898babd37b4567c` |
| `notes/theory/lean/YulangClosure/CoreExecution.lean` | `2cc68ffc79f17c0cb478802fec10ca2861e1a558a8202796bd7599595e5907ed` |
| `notes/theory/lean/YulangClosure.lean` | `5af826a59689a21294b36f361df95cceae8dc78b674c523e789a0e7e7bc1614d` |
| `notes/theory/2026-10-24-lean-core-correspondence.md` | `5aa9c3c417c98b3f6e69e3cb1ecb8872b49db836a10d0ca72e2606c0399dcbb0` |
| `notes/theory/lean/README.md` | `2c29c8abd8902afddef747dadab0279a5fc2d47f2e80d81aa9c6bfe1f2b3409d` |
| `docs/yulang-whole-proof-closure-ja.md` | `17f7518e72f5977b17ce085523adc788ba72a472041555fd18a24da96b4c79a5` |
| `docs/yulang-proof-index-ja.md` | `bb2d07bfe7bbbd4ad7364831ea2608ba94ef54514ae7a37b1a9724ac3891bb10` |

## Independent review and integration

Independent /root/astra_semantics_review actual80sec FINAL accepts exactly the structural fragment; no BLOCKING/MAJOR findings. Contract, this review snapshot and all8 output hashes matched. Reviewer inspected O/V and confirms identical-v proof selection, independent branch lifting, closed Bottom impossibility and EVERY enlarged raw successor/allfinite quantifier. General explicit evidence/runtime Views/metadata/Control/full-source boundaries remain OPEN. Checker results are primary receipts; reviewer reran no checker. No writes/descendants; actualSTOP. Primary adjudication accepts this scoped finding.

Budget10250 prior+30direction+190producer+80review=10550 charged on issuance. Requested inherited Astra/medium; actual model/effort/time UNKNOWN; full grants retained, max1activeAstra. No automatic renewal. Original checkout unknown leases quarantined; protected questions unstaged. Static20frozenlease hashes,9new/changed local links, current JSON size11806bytes and git diff --check passed. New Core files contain no project axiom/proof holes/unsafe/native_decide tokens. Explicit11path checkpoint is the commit containing this receipt, followed by inspection of the full outbound range before ordinary push. Protected questions remain excluded. No source-branch writes authorized merely by the terminology clarification; that target is being clarified in conversation.

## Original parent application

V1/V2/V5/V6 now have concrete checked cases for the listed structural proof-erased syntax under the SAME allfinite execution theorem. Whole original type/evidence binders, every remaining constructor and actual principal semantics, original values/stack-prefix Control body interpretation, actual metadata/full observations/AnalysisLaws/source initial formation remain OPEN. Original A/B, birth-level SCC/source-native occurrence correspondence, coverage/principality/termination and AH/RZ review remain OPEN. No independent source policy has been inferred from the checked fragment.
