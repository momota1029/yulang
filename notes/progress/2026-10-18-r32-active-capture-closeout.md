# R32 closeout — active-capture conservativity

## Outcome

- Original parent conditions discharged: **0 → 0**. The parent remains OPEN;
  R30's `j0/a0` guard and same-event world action is an independent OPEN gate.
- The proof establishes exact erasure and lifting for a reference-only record
  retaining existing Call operands, source scopes and event cursors across the
  joined tree with two helper uses. Independent spec review found this valid as
  definitional retention, but it does not satisfy R32's allocating-record
  predicate. It introduces no authentic C/D declaration, scope, dependency
  telescope, owner, typed edge or signed-pair/equality incidence.
- Neither a shared nor frame-local C/D completion is proved conservative. No
  original Call witness refuting conservativity, source counterexample, or
  irreducible semantic choice was established. The proof stops at the exact
  authentic C/D declaration reference needed for the allocating lift.
- The native test lane made no code/test change and ran no Cargo command. It
  found that the public source-call/FreshUse observers alone do not supply the
  needed join. Fresh compiler review found a broader existing API that the lane
  omitted: `CandidateInference::intrusion_observation()` and its events/parents/
  groups, also exercised by `candidate_intrusion_observation.rs`, expose
  checking occurrence, source Values, signed parent/copy incidence and
  representatives. The corrected remaining observer gap is narrower: the
  active initializer Link endpoint and exact demand/pair incidence joined to
  both FreshUse images. This correction does not produce an end-to-end trace.
- Fresh spec review: CLEAN for the reference-retention lemma and honest
  obstruction classification; BLOCKED for allocating conservativity and the
  native regression predicate. Fresh compiler review: CLEAN for preservation,
  with one minor observer-inventory correction above; both R32 success
  predicates and parent closure remain blocked.

## Frozen evidence

- [Candidate conservativity artifact](../theory/2026-10-18-active-capture-conservative-extension-r32.md), SHA-256 `fa0e0f25dfd454a51c924b505e847b02133a37b38689e033d34ae5796b24eb8b`
- [Proof handoff](../../tasks/agent-loop/inbox/20261018-active-capture-conservative-extension-r32.md), SHA-256 `6a39a4dba3a3a5fa149ab26d5d1753f1b50bc1bf7f4a8b4b0bd798ddca6e10eb`
- [Native-path report](2026-10-18-active-capture-native-path-r32.md), SHA-256 `7f17c297866236db3d0b6eaa1e1e26d6b030216280add558bc2fda124e652655`
- [Native handoff](../../tasks/agent-loop/inbox/20261018-active-capture-native-path-r32.md), SHA-256 `ac88eb4da9679589238765cca8f8853326942fa31b68c2efdbb3941312e1badf`
- Leased test [candidate_local_self_recursion.rs](../../crates/yu-solver/tests/candidate_local_self_recursion.rs) remained byte-identical, SHA-256 `a6406f3eef2b25844272da9cbe121277001760d004f733029dcc3f600aa79c7a`.
- Contract [R32](../../tasks/agent-loop/sprints/active-capture-conservative-extension-20261018-r32.md), SHA-256 `4f4037e01d1d3775bfa86f8642b6b0ee4c225dde16e26244b64919b0788ce479`.

## Next discriminating evidence

Audit the existing `intrusion_observation()` API and its focused regression
against the exact nested-helper witness. Determine whether current records can
connect the active initializer Link to its demand/pair incidence and then to
both FreshUse maps. If not, a narrowly leased test-only observer can be
considered in a new contract; do not infer the missing join from unrelated
canonical equality or graph-wide identity. Independently, C/D allocation still
needs an authentic source declaration/telescope and whole-tree lift. No
production allocation policy is authorized by R32.

## Verification and limits

Static source inspection, hashes, and independent reviews only. The focused
Cargo test was not run because the contract's path could not be asserted with
the initially inspected public records. No compiler/test edits, builds, probes
or Astra work. `python3 tools/agent_sprint.py check` and `git diff --check`
validate repository state only; they are not theorem evidence.
