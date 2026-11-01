# Sprint R169 — derive the FormalEntry pre-state and retained permission

Status: **ADMITTED** under the continuing Yulang Rust/Lean soundness goal.
Branch / baseline commit: `yulang3` / `87ddd80c3`.
Contract revision: 1. Primary: Luna. This contract does not authorize production
promotion or alter the accepted effect-hygiene semantics.

## Original outcome and success evidence

The unchanged parent is `YulangClosure.SourceProblem.InferenceSoundness` in
`notes/theory/lean/YulangClosure/Contracts.lean:127`: for every supported
source `s`, original scope `x`, generated constraints `d`, and successful
solution `a`, derive one witness `e` such that
`sourceJudgment s x e ∧ sameScoped s x e a`. R169 does not discharge that parent.

R169 attacks the first source/native premise for the existing R116 permission
theorems. Starting from finite raw collector and pre-action state data, model
the actual LocalSource Lambda parameter annotation, `Action::FormalEntry`
construction, and constructor events. From a successful constructor trace,
derive (rather than assume) the same R39 `prepare` equation and, for a nonempty
concrete row, the `permissionFor` equation for the exact ordered published
record. Preserve the authentic pre-state absence checks and the same annotation
payload across collection, action, execution and publication.

Success evidence is a checked Lean theorem connecting a raw finite event trace
to R39's exact result, plus a source review showing the event relation follows
the frozen Rust branches. Empty concrete rows retain no permission. Duplicate
concrete entries and their order are preserved. A symbolic tail equality event
precedes permission publication. A resource-sample failure after publication
is represented as failure with the published post-state; no method-local
`Err => unchanged` law is allowed.

## Authority, baseline and frozen inputs

Current Rust audit: `tasks/agent-loop/inbox/effect-permission-formal-entry-current-rust-audit.md`, SHA-256
`7004a57f14b79c73450c68431743ef7401232195b7d63c85d55f76f04eabb33d`.

Direct Rust dependencies, all inspected clean at the audit freeze:

- `candidate_source.rs`: `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49`
- `candidate_effect.rs`: `4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15`
- `lib.rs`: `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be`

Lean dependencies:

- R39 `ComputationPermissionEntryR39.lean`: `748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e`
- R116 `SuppressionPermissionR116.lean`: `2aed350468964d90d8d83714177fff77d477e3df0846ae23150194bd76270e3a`
- R118 `NativePermissionDecoderR118.lean`: `f976e0b3b5e8b2b70ee902bdca30ce140db503a4972e8cf1b621892b57bf5d27`
- R45 `InternalPermissionIncidenceR45.lean`: `9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f`
- R54 `OwnedResidualProjectionR54.lean`: `cc5d0b01485560e5091ce454b066ca2fc41eb350eee24ae525133a13bed401c9`
- Original parent `Contracts.lean`: `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`

Toolchain: `leanprover/lean4:v4.35.0`; `lakefile.toml` SHA-256
`212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4`;
`lake-manifest.json` SHA-256
`058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`.
The only permitted build cache is the existing `notes/theory/lean/.lake`.

## Two lanes

### Proof lane

Registered `lean_prover`, requested Sol/high, maximum 2400 seconds. Exact output
leases:

- `notes/theory/lean/YulangClosure/FormalEntryPrestateBridgeR169.lean`
- `tasks/agent-loop/inbox/effect-permission-formal-prestate-r169-proof.md`

Construct a small-step finite relation from raw list/map inputs. The action
collector must derive its registration from the actual Lambda parameter ID and
carry the exact parameter annotation, owner, occurrence and registered scope.
The constructor pre-state must include recipes, authentic LocalSource Lambda,
source-owner lookup, occupied formal domains and retained-registration state.
Prove the R39 `prepare` result for the action and, only when concrete is
nonempty, `permissionFor` equals the record actually appended. Track symbolic
link-before-publish order. Include explicit empty, duplicate/order, symbolic,
already-retained rejection and post-publication sample-failure cases. Do not
assume `Valid`, `prepare`, `permissionFor`, or final payload equality as a
transition premise. State exactly which Rust event authentication is supplied
by the primary source handoff and what remains unmodeled.

Use pinned Lean 4.35.0 and existing `.lake`; no Cargo, Rust build/test, new
environment, target, cache, dependency or persistent scratch. Two focused
checks maximum, each 120 seconds; one CPU, process memory within the project's
`-M1024`. Keep complete theorem types and transitive axiom audits.

### Rust/source lane

Owner Luna, maximum 600 seconds, read-only exact lease:

- `tasks/agent-loop/inbox/effect-permission-formal-prestate-r169-source.md`

Map the frozen source reads at `candidate_source.rs:1323–1327, 2469–2475`,
`candidate_effect.rs:1991–2063`, and `lib.rs:18341–18470` to the proof relation.
Preserve producer provenance because the constructor does not compare the
annotation payload with the Lambda parameter's annotation. Preserve the
post-publication resource failure branch. The native consumer is still
disconnected (`internal_formal_permission_incidence` is evidence-only); do not
wire Catch subtraction in this sprint.

The R169 source audit found no justified code change. Implementation status is
**NO_SAFE_CODE_SLICE**: the producer/retained lookup had no concrete defect, and
consumer integration still lacks reviewed selected-arm, operation, endpoint,
and state/batch correspondence. This records the searched owners and first
missing gate; it does not mark the end-to-end implementation complete.

## Parent application, falsifier and limits

Apply the derived R39 equations to the existing R116 `selected_endpoint_member`
only when its independent selected-source, operation-match and endpoint
equations are supplied. The result is still conditional. R45 accepted
permission extraction, R54 state/batch ownership, actual successful Rust
consumer execution and the original shared-witness A/B obligation remain open.

Falsifiers include a bridge using post-state as the pre-state; action
construction from a different annotation; lost/changed concrete order or
duplicates; a constructor success model that records a permission for empty
concrete input; or an `Err` case after publication asserted to leave the state
unchanged. Any such counterexample stops the packet and is reported without
weakening R39 or the original parent.

## Review, resources, Git and state

Total ceiling 3600 seconds: proof 2400, primary source mapping 600, fresh
independent proof/source review 600, Astra 0. One proof/cache writer at a time;
no concurrent Lake process. Existing `.lake` is 98 MiB. No target or new
environment. Current capacity override already releases 16 stale reservations;
UNKNOWN workers and quarantined paths remain intact and no second release is
authorized or needed. Current live roster at admission: no active child
writers; prior named children are completed. The pending question bundle and all
dirty/untracked files outside these exact output leases remain excluded.

Fresh independent Lean proof review and separate compiler/source review are
required before acceptance. Only Luna stages these exact R169 files and pushes
after review and full outbound-range inspection. Static sprint consistency is
checked after state update; it is not a proof. Stop on changed dependencies,
source mismatch, counterexample, lease conflict, absent cached dependencies,
resource cap, or budget exhaustion. R168 runtime remains BLOCKED_RESOURCE and
does not authorize a new runner.
