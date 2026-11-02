# R268 approved-clause/source-owner audit — 2026-11-02

Luna's 300-second lane was a read-only owner/clause audit, not a proof attempt.
No production edit, test, build, probe, Lean, Cargo or Git operation occurred in
this audit. All 36 R255 pins matched, and R267-r6 contract, theory, handoff,
review, the R255 manifest, R70/R71 contracts and approved occurrence-principle
pins matched before the inspected source excerpts. The 14-path source-body
allowance remains exactly the one listed by R267-r6.

## Approved rule to implementation-owner map

- Top-level principles §1.1(2) require each copying occurrence to retain its
  parent and child identities and propagate those occurrence-associated pairs.
  The approved intrusion association selects the actual extrusion occurrence
  and its retained source Value / parent-copy pair; it does not license a
  permanent Value owner or infer occurrence reachability from endpoint IDs.
- `candidate_source.rs`, `shadow_apply.rs`, and HIR `module.rs`,
  `module/local_source.rs`, and `shadow.rs` own construction and retention of
  source roots, expression occurrences and applied source actions. The missing
  proof prerequisite is a source-qualified accepted occurrence linked through
  its actual direct row/Parent history to the candidate used at extrusion.
- `candidate_intrusion.rs` owns `Parent` records and occurrence-indexed row
  parent/copy identity; its representative/merge operations own canonical
  identity changes and third-owner consequences. These structures preserve
  facts supplied to them but do not themselves prove an accepted source path
  requires a particular canonical candidate.
- `candidate_extrusion.rs::candidate_extrude` owns selected physical-slot
  traversal, `Work::Bound` transport and retained operation/occurrence data;
  incoming bound restoration and `candidate_replay_bound` own opposite-bound
  construction and ordered Replay inputs. `candidate_effect.rs` owns bound
  evidence/origin transport. `candidate_context.rs` owns raw/canonical
  context transport and Replay's ordered dependency/scope/demand composition.
  These owners provide the local slot and consumer seams; the unresolved
  bridge is accepted-source occurrence → required candidate → complete
  Parent/slot/merge history → the actual ordered opposite Replay input.
- `candidate_scheme.rs`, `candidate_value_graph.rs`, `candidate_scope.rs`, and
  `term.rs` own supporting scheme/value graph/scope/typed-key representations;
  they do not discharge the missing source-to-Replay incidence by themselves.

R70's admitted successful-helper envelope and unchanged copy edge remain the
application site. R71 requires physical owner/side/item/slot, raw evidence key,
canonical child key, contextual fibers, actual transport order and copied
emission to remain distinct. The audited source map matches those approved
owners. R267-r6's source-first review independently confirmed the bounded
Function-slot path and exact ordered-input construction. Neither establishes
the missing source-wide necessity/ancestry equation.

## Audit disposition

No approved-clause violation or production repair is established. Missing
prerequisites remain the authentic accepted-source incidence, direct-row
Parent ancestry, complete competing slot/merge/history paths, independently
required canonical candidate and actual ordered opposite input. TEMP265/Z265
Effect temporal simulation remains open. This audit is not proof evidence,
source-wide closure, or authority for code changes; implementation stays
`NO_SAFE_CODE_SLICE`. Parent/A/B delta remains 0→0.
