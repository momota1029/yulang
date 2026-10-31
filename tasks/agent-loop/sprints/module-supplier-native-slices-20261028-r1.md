# Sprint contract — MODULE-SUPPLIER-NATIVE-SLICES/r1

Status: **ACTIVE**. Baseline `bc2a0836ec8fc9dee6a1094552a3dd34cfbcfd0d`
on worktree `yulang3`. This is a bounded follow-through to the reviewed
module materialization supplier audits. The adopted rule and exact two supplier
identities remain fixed; no new source owner is admitted beyond the files and
direct helpers listed below.

## Goal and preserved obligations

Audit whether the current native construction supplies an identity/receiving
map relevant to:

- `ModuleNameSourceTypingAndAdmission`
- `ModuleUseReceivingExportCorrespondence`

Trace the bounded field chain:

`ModuleDef target → DefinitionUse → target/use components → selected routing
branch → captured/freshened receiving value → owner export`.

For every field, record its producer, validator, consumer, and the exact
equation or source premise it establishes. Compare these native facts with the
adopted rule's typed-entry/environment/lookup/admission requirements. Structural
identity, successful routing, observer traces or port presence do not establish
source typing. Treat a missing equation as the first unsupported edge; do not
infer absence outside inspected functions.

The actual `CandidateInference::export` and the observer interface's
`receiving_export` are distinct. Do not conflate them. Preserve all original
quantifiers, source domain, shared witnesses, callback → Call result → tuple
`left`, original A/B, complete Call/effects, and all source/native and
production obligations as OPEN unless direct reviewed evidence discharges
them. `DELTA_AUTH_UNRESOLVED / NO_SAFE_CODE_SLICE` remains binding. No compiler
or expected-output edit is authorized.

## Exact bootstrap and authenticated source set

Use the existing 21-entry manifest and preflight, with exact paths:

```text
tasks/agent-loop/sprints/effect-permission-module-materialization-r3-manifest.json
SHA-256 aee1a5e3c06e9c72348e45676157bdb56b57f0dc5673ddcffe58b30a8fb16f11
tasks/agent-loop/sprints/effect-permission-module-materialization-r3-preflight.py
SHA-256 7ef05dc938c7f44cbbcd08004cc5fc9b306677b58415cc4276c21330a832d133
```

The manifest pins the admitted source/design dependencies; specifically:

```text
crates/yu-solver/src/candidate_source.rs 96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a
crates/yu-solver/src/candidate_scheme.rs 31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707
crates/yu-solver/src/shadow_apply.rs c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff
crates/yu-solver/src/lib.rs ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07
crates/yu-solver/src/candidate_call.rs fdc39e01fa3665b4dc14e167973de63b275eb0280b831e340b6cdcee5ed0fc3f
```

Each lane independently authenticates the final contract pin, manifest, script,
and all 21 entries before any body read. Primary supplies each lane the exact
literal bootstrap command containing the frozen contract digest. No fallback,
path substitution or body inspection after a failed hash/preflight.

Reuse only each worker's own unchanged governance coverage, after checking its
own frozen r4/r4a1/r4a2 receipts and reauthenticating every reused file hash.
The reviewed r4a2 source receipt provides locators only; its conclusions are
not treated as proof of source/native implementation.

## Exact files, functions and coverage cap

Initial locator ranges (line numbers are locators; workers must record actual
byte offsets and verify complete named local units):

- `candidate_source.rs`: Name-resolution arm 1762–1808; complete
  `execute_candidate_action` 2457–2511; required `Action` declarations.
- `lib.rs`: definition registration 1054–1108; pending-use resolution
  1400–1478; `validated_route_use` 19466–19474; `route_internal` and
  `route_internal_inner` 18207–18236; candidate-graph dispatch 19179–19187.
- `candidate_scheme.rs`: `route_candidate_open_use` 4184–4191;
  `route_candidate_graph` 4193–4220; `instantiate_candidate_graph` 4717–4799.
- `shadow_apply.rs`: actual `CandidateInference::export` 2029–2055; separately,
  observer `CandidateDefinitionUseRef` 3038–3102 and `definition_use`
  3233–3253, only to distinguish evidence channels.

Read one file/page per response, with each page no larger than 4,096 bytes and
output allowance at least 8,192 tokens. Record exact SHA-256, contiguous byte
boundaries, line boundaries, and continuation. Complete each named function,
closed match arm and necessary declarations before using it. Follow only direct
helpers in these already admitted files when needed to complete the local
equation. Maximum relevant body coverage is **100 KiB total** across both
producer lanes, counting overlapping bytes once for the budget but separately
recording each lane's authenticated coverage. An additional owner requires a
new primary admission before reading. If a page truncates, discard and retry a
smaller range at most twice; stop on two failed retries, any gap, mismatch,
cap, or unresolved ambiguity. A file's uninspected tail stays explicitly
unread and cannot support an absence claim.

## Lanes and fresh outputs

**Source lane:** resume the same stopped source identity as a read-only
`researcher`. Build the fieldwise producer→validator→consumer inventory and
identify the exact first mismatch or unsupported source premise. Exact output:
`tasks/agent-loop/inbox/module-supplier-native-slices-source.md`.

**Proof lane:** resume the same stopped proof identity as a read-only
`lean_prover`; no Lean/Lake execution or theorem/axiom claim. Independently
classify which native equations can discharge the adopted premises without
assuming a lawful source map or typed environment. Exact output:
`tasks/agent-loop/inbox/module-supplier-native-slices-proof.md`.

Fresh nonauthor `compiler_referee` review after both receipts, read-only. It
checks hashes/ranges, every fieldwise join, the distinction between native
graph export and observer export, circularity, and that conclusions stay
inside the read domain. Primary records the review in
`tasks/agent-loop/inbox/module-supplier-native-slices-review.md`.

## Resources, stop rules and closure

Prior conservative charge is **3,950 / 7,200 seconds**; 3,250 remain. New total
grant ceiling: **1,000 seconds** (source 350, proof 300, review 200, primary
100, contingency 50), leaving 2,250 seconds after full grants. Charge grants
fully; no refund or reuse. Zero Astra, no Cargo, tests, builds, Git, source or
compiler edits, expected-output changes, or descendants. A cap overrun is a
protocol failure and must be reported with a measured lower bound and unknown
startup; do not claim compliance.

At closure, retain the first unsupported field per supplier and all exact open
dependencies. Review must reject claims that target identity, successful
routing, observer `receiving_export`, or a partial native path supplies typed
source admission or the whole receiving/export interpretation. Both suppliers
and all parent/native/production gates remain OPEN unless direct reviewed
evidence establishes otherwise.
