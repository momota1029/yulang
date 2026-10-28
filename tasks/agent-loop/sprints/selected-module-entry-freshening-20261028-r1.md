# Sprint contract — SELECTED-MODULE-ENTRY-AND-FRESHENING/r1

Status: READY, pending proof and baseline-review acknowledgements. Objective:
derive the selected source occurrence's actual typed module entry and identify
whether the present Rust overlay preserves its whole freshening image. This is
a bounded step toward open source/native and effect-hygiene obligations; it
closes no parent, native, or production gate by itself.

## Authority and fixed claim

- User goal: prove Yulang inference and soundness in Rust and Lean, especially
  effect hygiene; retain the original source domain and parent quantifiers.
- Selected outcome: SELECTED-MODULE-ENTRY-AND-FRESHENING/r1, chosen by the
  primary's current next_action_selector result after
  MODULE-SUPPLIER-NATIVE-CORRESPONDENCE/r1 closed incomplete.
- Prior outcome: tasks/agent-loop/history/module-supplier-native-correspondence-20261028-r1-outcome.md
  SHA-256 67b2fd34479b069d8016689fc8d99f8b1bf2608baba72dd48feddc5c198375f5.
- Selector closeout SHA-256
  b8c5c990da8631e8a3af625465946e616f673066091428f499dff3420aa3b76e.
- Adopted module environment authority
  notes/design/2026-10-17-module-environment-exposure-definition.md:
  d5d03de8b80eb2792cc35690f3fc3c871f9704f4aee8df815bce40b1f49f9d4d.
- Adopted candidate source
  notes/theory/2026-10-17-module-reference-materialization.md:
  f1971e53ef62a5b3d94897ca9774d67c021d21524d9774b14439748a00fee9eb.
- Module-expression source owner
  notes/design/2026-10-16-module-expression-source-owner.md:
  ab12b442f4f3d3d11565c89cda82c1cb25b17e943c2851b6bc937252410311e5.
- Fixed source fixture: my id x = x; my answer = id 0. Use its actual
  occurrence and adopted identity transport; do not reconstruct a cross-session
  HIR identifier.

## Baseline and exact Rust scope

Repository HEAD: bc2a0836ec8fc9dee6a1094552a3dd34cfbcfd0d. The current overlay is
a new baseline under review; this does not recover or authenticate its missing
predecessor. Exact complete owner hashes at admission:

| Owner | SHA-256 | Net diff |
|---|---|---:|
| crates/yu-solver/src/candidate_effect.rs | 1715046b29b760fe70b3c2fb05665dad23e7f95ad05883c39d06d4da37b925ab | +719/-41 |
| crates/yu-solver/src/candidate_scheme.rs | 31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707 | +62/-4 |
| crates/yu-solver/src/shadow_apply.rs | c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff | +7/-0 |

Only these three Rust paths are in review scope. Runtime paths
tools/inference-playground/src/runtime/machine.rs and receiving.rs, plus every
other quarantined path, remain unavailable: do not read, edit, stage, or treat
them as baseline evidence. No Rust writer is admitted before fresh independent
complete-delta review and explicit primary baseline admission.

## Lanes and leased outputs

Proof — registered lean_prover, maximum 1,000 seconds. Construct the actual
selected occurrence's environment/registration/scope/lookup derivation under
the adopted authority. State the exact dependent map, provider and occurrence
witnesses, branch-specific use/admission, and obligations connecting
freshening's lower term to Phi_u of the actual whole branch allocation root.
Do not assume LocalLaws, a generic supplier, a proposed interface, or successful
native routing. Reuse prior results only after authenticating exact hashes and
apply every accepted lemma to its original supplier. Exact leases:

- notes/theory/lean/YulangClosure/FormalPermissionSelectedModuleEntry.lean
- notes/theory/lean/YulangClosure/FormalPermissionFresheningImage.lean
- tasks/agent-loop/inbox/selected-module-entry-freshening-proof.md

Baseline review — fresh nonauthor compiler_referee, maximum 300 seconds.
Authenticate the three owner hashes and inspect the complete net diff against
the pinned HEAD, including test-only gating, laziness, changed call sites, both
Graph literals, sibling constructors, feature-gated compile risks, and claims
in prior handoffs used to characterize this delta. Do not inspect quarantined
paths. Review only: no edits, builds, tests, Cargo, Lean, or Git mutations.
Exact output: tasks/agent-loop/inbox/selected-module-entry-freshening-review.md.

Source lane — primary, read-only pending review. Freeze the exact diff and
identify the witness chain from actual allocation through whole dependent-map
image, scopes/shared witnesses, successful owner export, and exact selected
occurrence. Distinguish actual export from observer export. No code writes or
Cargo before review acceptance and primary baseline-admission receipt. Any
later writer needs an exact isolated-workspace lease and versioned amendment.

## Success, falsifiers, and boundaries

Success is either a checked construction for the selected actual typed entry
plus a freshening-image lemma with exact premise ownership, or a precise first
unsupported mathematical/source/native equation that materially reduces the
open premise. Baseline admission separately requires complete review with no
unresolved blocker affecting scope. Finite tests/instrumentation do not prove
the supplier or parent theorem.

Falsifiers: wrong occurrence or constructor; circular supplier premise; changed
provider/component; inconsistent dependent-map image; lost original
scope/shared witness; observer substituted for actual export; wrong allocation
root or owner; unreviewed/unpinned Rust delta. Any uncovered dependency, failed
baseline review, resource-limit breach, or changed authority stops the affected
lane. Preserve original A/B and effect-hygiene claims, quantifiers, source
domain, semantic decisions, and expected outputs. Parent/native/production
gates remain OPEN absent direct reviewed closure.

## Resources and integration

Fixed envelope 3,600 seconds: proof 1,000; baseline review 300; final
independent review 300; primary 1,000; contingency 1,000. At most two producers
at once; zero Astra. This contract does not authorize Cargo or Rust tests
before baseline admission. Any later Cargo/Lean run needs exact argv, frozen
inputs, one owner, and a fresh attempt receipt. Serialize heavy checks. Stop at
the envelope or on resource exhaustion. Primary alone grants exact leases,
adjudicates, updates current state, stages reviewed paths, and pushes a coherent
checkpoint. UNKNOWN writers and quarantined paths remain untouched.
