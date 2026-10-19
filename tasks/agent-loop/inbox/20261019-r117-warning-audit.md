Sprint-ID / contract revision and SHA-256:
  effect-static-runtime-projection-warning-audit-20261019-r117, rev3
  2a8336e2c42228fca21ef156b84fc471f56d5636d63c508f12186da8670c4457
Assignment-ID / handoff revision:
  R117-warning-owner-cleanup / 1
Parent gate / original theorem and scope locator:
  Broad proof-backed inference/evaluator goal; this bounded implementation
  slice is warning ownership only. Static-to-runtime projection parent is
  separately owned by the R117 proof lane and remains OPEN.
Baseline / direct dependency hashes:
  R116 CLI finite observation reused: 2 approved surface cases passed with
  exact stdout `7\n` and empty stderr. It is not proof of general behavior.
  Implementation input pins before edits:
  module.rs c40ebde1755d300c83aafba0a81a85d19ed5200dfc2163ab72c8a3bb08baf29a
  candidate_scheme.rs d4ff8a9e98eb667a5eb85aff9c0feec1f0227e86257bb56892493ac1d04a9278
  candidate_context.rs 42f89dcf5fa6d7095db1e220c89308a2a35f4e74b05c3e8821d4fb2e3e32b0ca
Role / actual worker ID / current session / launch or resume receipt:
  Luna/high implementation lane; /root/r117_warning_implementation;
  current-conversation-2026-10-19-breadth-surface-method-goal; launched by
  Luna for the exact R117 rev3 source and handoff leases.
Requested model and effort / observed model and effort:
  gpt-6-luna / high; observed model UNKNOWN / effort UNKNOWN.
Exact leased paths / all authors and contributing descendants:
  crates/yu-hir/src/module.rs
  crates/yu-solver/src/candidate_scheme.rs
  crates/yu-solver/src/candidate_context.rs
  tasks/agent-loop/inbox/20261019-r117-warning-audit.md
  Author: /root/r117_warning_implementation. No descendants.
Outcome class:
  implementation; source-local behavior-preserving warning cleanup.
Parent application:
  Removed unused HIR helper `replace_admission_root`. Marked `requested`,
  `graph_row`, and the `Ready`-arm `completion` binding as `cfg(test)` because
  their only consumers are test observations. Marked
  `freshen_candidate_graph` `cfg(test)` because its callers are test modules.
  This removes production-only dead-code bindings while retaining all test
  observation code and all effect/method provenance. No source-to-constraint-
  to-propagation-to-execution behavior or theorem gate is changed.
Source constructors -> generated constraints -> propagation -> consumer/native:
  Not modified by this cleanup. `freshen_candidate_graph` call sites found in
  candidate_effect's `#[cfg(test)] mod tests` and candidate_context's
  `#[cfg(test)] mod tests`; the retained production route is
  `freshen_candidate_graph_retained`. The binder projection path and its native
  correspondence remain with the proof lane; no claim is made here.
Artifact locators and byte hashes / frozen review snapshot:
  crates/yu-hir/src/module.rs
    153a23ecaa68fd150d8bd0cc0316f3723e1cb5d98a6e3026aadef2bfd08fd907
  crates/yu-solver/src/candidate_scheme.rs
    2e64dc8781189b4da21c30f4d1b3208aaef48ca247cae55fb7e77e68b5857850
  crates/yu-solver/src/candidate_context.rs
    337f998d0d37af3397927f734660a1ef392cc8ec45b5746398ea76a8ab566b2f
  Frozen after this receipt; hashes are the review targets. No other source
  output was written. Luna separately owns the runtime/program.rs callback
  field cleanup after the proof writer stops.
Warning-by-warning classification of the 17 R116 warning instances:
  Safe local cleanup (six instances total across the full R117 contract):
  - yu-hir: unused `replace_admission_root` — deleted here.
  - yu-solver: test-observation locals `requested`, `graph_row`, and
    `completion` — `cfg(test)`-gated here; test consumers retained.
  - yu-solver: test-only `freshen_candidate_graph` wrapper — `cfg(test)`-gated
    here; production retained path unchanged.
  - yu-playground: redundant stored `OperationV1Plan.callback_apply` — safe
    deletion identified by owner audit, but not in this writer's lease; Luna
    owns it in runtime/program.rs after proof STOP.
  Intentional provenance/evidence (eleven retained instances; no suppressions):
  - yu-hir: `AssociationProvenance::Token(SyntaxToken)` and
    `AssociationProvenance::Synthetic(Vec<AssociationProvenance>)` payloads;
    `AssociatedFieldTailSource` and `source`, `receiver`,
    `receiver_provenance`; `AssociatedRoleImplSource` and `source`, `node`;
    `ShadowArtifact::with_associated_method_role_sources`;
    `walk_associated_pairs`. Retain these source-association constructors and
    provenance even while current production consumers are incomplete.
  - yu-solver: `LicensedOperationFieldV1` fields `declaration`,
    `field_position`, `negative_port`, `handler_argument`;
    `CallbackFieldRealizationV1` fields `response_annotation`,
    `handler_argument`; `FieldBoundV1` fields `source_occurrence`, `lower`,
    `upper`. Retain these operation/license/handler and bound evidence fields.
  Classification follows the frozen R116 warning-owner audit and R117 rev3
  scope. No additional warning count is inferred without the authorized build.
Checks, coverage, omitted cases and resource budget:
  Static exact-path diff and call-site/configuration inspection only. No tests,
  build, CLI, probe, formatter, or warning suppression run/added, as required.
  Approximate active work: under 180 seconds of the 300-second assignment cap.
  Runtime/executable verification is Luna-owned after frozen reviews.
Next related step inside the existing envelope, or exact boundary needing Luna:
  Obtain fresh compiler/source and regression review of these three frozen
  files. Luna may then perform the separately leased playground field deletion,
  after proof STOP, and run only the exact rev3 coordinator command if review
  and deadline gates admit it. No lease expansion requested.
Mutual TODOs:
  R117 proof lane: finish exact Catch payload binder identity/environment trace;
  first missing edge, if any, must name the source owner and falsifier in the
  proof handoff. This implementation did not supply or alter that evidence.
Worker state / writes stopped receipt / unresolved descendant leases:
  STOPPED; all four leased files are frozen at hashes above; writes stopped;
  no descendants or scratch outputs; no unresolved implementation lease.
Commit-ready milestone or explicit pending review/integration:
  Pending fresh independent review and Luna-owned runtime/program.rs change,
  verification, and full integration inspection. No commit claim.
