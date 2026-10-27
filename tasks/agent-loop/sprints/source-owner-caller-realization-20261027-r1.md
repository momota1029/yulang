# SOURCE-OWNER-CALLER-REALIZATION-20261027/r1

Status: Luna-admitted bounded continuation; full Yulang parent remains OPEN.
Code baseline: `90d6332ffc30fdb9f005e1f788bfdb3eaf82bc8c` on `yulang3`.
This contract is metadata/authority only; it changes no compiler semantics.

## Parent and bounded outcome

The unchanged parent is the complete Yulang inference/executor objective,
including its original supported source domain and quantifiers, soundness,
Effect hygiene, principality, termination and source/native obligations. The
previous finite source-owner table and 28 audited Lean roots are accepted only
as inputs. Their incoming `Context`, route, ambient scope and runtime frames
remain premises.

This packet follows one concrete source-import owner through an exact finite
consumer/provider corpus. Its success condition is either (a) an authenticated
finite Context lookup plus a complete root-rule walk yielding the selected
subtree route and ambient scope, or (b) the first exact missing interpretation
equation, with no default or fabricated field. It does not promise a complete
semantic caller Context, runtime `OwnedFrame` values, or universal frontend
refinement.

Freeze the existing `source_imports_resolve_named_alias_and_glob_by_exact_provider`
fixture from `crates/yu-hir/src/module.rs`, preserving its three provider
modules and consumer alias `identity` resolving to `std::core::id`, with
prelude `id` resolving to that same provider. Add the prior accepted nested-
shadowing lambda fixture as a selected consumer declaration in the same
finite corpus. Keep the import declaration, selected declaration, physical
source keys, resolved provider identity, HIR declaration owner, LocalSource
root, complete source rule tree, and event-route walk as distinct typed facts.

The Rust adapter emits data only. It must use the real `ParsedFile`, exact
`ModuleIdentity`, resolver-created `SourceImportEnvironment`, provider
`SourceExportIndex` values, selected HIR declaration and source-rule tree.
Recheck all owner joins before writing. Exercise foreign-parse and foreign-HIR
rejection before publication. Never infer an original `Context` field merely
from an import index, module label, alias, serialized ordinal, or successful
HIR lowering.

The Lean lane may prove the concrete lookup/route/ambient relation only where
every constructor field follows from the accepted original rule and the frozen
owner table. It must stop at the first unsupported field and report the exact
equation/premise. Reuse `OriginalSourceOwnerReification` and its frozen
instance without edits. `callerContext = none` from the previous trace remains
unobserved, never an empty Context. Runtime frames, semantic guards, all other
inputs/forms, universal frontend refinement, original Simple-sub A/B, full
Call, source/native, soundness, Effect hygiene, principality, termination,
receipt/admission and production remain OPEN in original scope.

## Frozen inputs and revalidation

Before any worker consumes inputs, Luna rehashes every governing pin and
import/config entry recorded by the prior contract
`tasks/agent-loop/sprints/source-owner-trace-realization-20261027-r1.md`
(contract hash `71ecc354bcd354396ed9b12ce15b9bb8a0070763b1492b08993fb40a92e44bbe`)
and the prior proof handoff. The following direct inputs must also match:

| Input | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/OriginalSourceOwnerReification.lean` | `95d9749ce93ecfc82d6423ba193a261f2725178a7e62cea469b57ae316af3d7e` |
| `notes/theory/lean/YulangClosure/OriginalSourceOwnerReificationInstance.lean` | `3aab685323e00b69cb9c21d847582e442590e0ff5e810fab50662b7d9127f887` |
| `notes/theory/lean/YulangClosure/OriginalSourceOwnerReificationTrace.lean` | `b9a15df005c730db27fc385c58ca07b433f1095f017e0969155106da7478fb0a` |
| `tools/inline-authentic-extraction/src/bin/original_owner_reify.rs` | `4921d14f813e931cb064ecc87d8120734b69d1eedaf48fe0bd36deb014e862e9` |
| `crates/yu-hir/src/module/source_exports.rs` | `03727fd3918738a48afde7f7a875de60b63b43ac2cc620896a4ed73d8b0a9179` |
| `crates/yu-hir/src/module.rs` | `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646` |
| `tools/inline-authentic-extraction/Cargo.toml` | `21c64b4a22318a1ae89c346357161812a6ac313b6f0c4999853272cf73e2832b` |
| `tools/inline-authentic-extraction/Cargo.lock` | `2ee467b8f6416aa7dda36f96e3401a0b0ae24a739ff7c6a2efccc1323777ee91` |
| `tasks/agent-loop/inbox/source-owner-trace-realization-20261027-review.md` | `0cfd23e798742440fd142d300e624081faa7036d841ae76ac9abe3a479a1bc82` |

Pin drift, a mismatched provider identity, or an incomplete inherited cone
stops the packet before execution. No dependency version/checksum may change.

## Exact leases

Implementation — registered Luna/high implementer:

- `tools/inline-authentic-extraction/src/bin/original_caller_reify.rs`
- `notes/theory/lean/YulangClosure/OriginalSourceCallerReificationTrace.lean`
- `tasks/agent-loop/inbox/source-owner-caller-realization-20261027-source.md`
- scratch only under `/tmp/yulang-source-owner-caller-realization-20261027/impl/`

Proof — registered `lean_prover`:

- `notes/theory/lean/YulangClosure/OriginalSourceCallerSchema.lean`
- `notes/theory/lean/YulangClosure/OriginalSourceCallerReification.lean`
- `notes/theory/lean/AuditOriginalSourceCallerReification.lean`
- `tasks/agent-loop/inbox/source-owner-caller-realization-20261027.md`
- scratch only under `/tmp/yulang-source-owner-caller-realization-20261027/proof/`

The proof writer may author schema and finite theorem statements while
implementation runs, but may not consume the generated trace or start Lean /
Lake until implementation cessation and Luna's exact trace-hash ACK. The
reviewer is a fresh non-author read-only `compiler_referee`; Luna persists its
report at `tasks/agent-loop/inbox/source-owner-caller-realization-20261027-review.md`.
Luna alone owns this contract, outcome, `current.json`, leases, review
adjudication and explicit-path Git integration. No worker has Git or compiler
semantic authority.

## Resources and execution-envelope receipts

Fresh budget: 3600 active seconds (implementation 900, proof 1200, Luna 600,
review 720, dispatcher 180); Astra 0. At most two offline/locked Cargo
processes / 240 seconds total and six pinned Lean 4.35.0 checks / 360 seconds
total. One verifier process at a time. No tests are requested; tests may be
read but not run.

Every Cargo and Lean invocation must retain an exact, hash-pinned receipt for
argv, cwd, complete environment, start/end timestamps, wall time, exit status,
stdout/stderr hashes, selected one-CPU affinity, and inherited memory/CPU
limits. Derive the selected CPU from the process's allowed affinity and record
it. Invoke each command under explicit `taskset`, `prlimit` (1 GiB address
space and 120 CPU seconds), and `timeout` (120 seconds); a shell inside the
limited process records the child and wrapper status before exit. Keep command,
wrapper script and receipts beneath the lane's scratch root. Do not claim the
cap was enforced without those receipts. Preserve failed calls; no retries
beyond the call budgets. No call is concurrent with another verifier.

Implementation freezes source/schema hashes before Cargo. On success it freezes
the exact emitted trace and stops all processes before Luna sends proof the
trace hash. Proof audits every originating declaration, full type and
transitive axiom set. The fresh review inspects source joins, provider identity,
root incidence, exact receipts, all theorem statements/axioms and remaining
premises without running Cargo, Lean, Lake, tests, Git or formatters.

## Falsifiers and stop conditions

Stop for any pin/lease/dependency drift; wrong consumer/provider/alias identity;
foreign parse or HIR accepted; declaration/root mismatch; omitted or reordered
root incidence; Context, route, ambient field without an adopted rule and
actual owner; published trace before all rejection checks; theorem using a
fabricated field, proof hole, unauthorized axiom or native-evaluation trust;
missing execution-envelope receipt; resource exhaustion; or overlapping
writer. Preserve the exact first obstruction. A bounded obstruction is useful
evidence and closes no parent claim.

## Luna bounded retry authorization after Cargo call 1

Luna records that Cargo call 1/2 exited 101 in 24 seconds inside the required
envelope; the wall timeout did not fire. Its compiler diagnostics were seven
`E0277` conversions from `HirAvailabilityError` and one `E0599` reference to
nonexistent `SyntaxKind::UseStatement`. Luna explicitly replaces the earlier
direct instruction to stop at the first failure for **one final call only**.

The sole authorized source repair is adapter-local: route each affected
`HirAvailabilityError` result through the existing `availability(...)` helper
and replace `UseStatement` with the owner-defined `SyntaxKind::UseDeclaration`.
Preserve the exact fixture, data schema, provider/alias joins, selected nested-
shadow subtree, foreign-owner checks and their pre-publication order. No other
source/schema change, compile-only call, binary rerun, test, dependency edit,
compiler/API change, or semantic claim is authorized. Rehash the amended
adapter and unchanged governing pins before execution. One final locked offline
Cargo call remains (call 2/2; at most 120 seconds; same explicit CPU/memory/
timeout envelope); after it, stop and freeze regardless of outcome. The proof
lane remains blocked from Lean/Lake until Luna ACKs a successful frozen trace
hash. Failure leaves the exact import-to-Context/root elaboration equation
OPEN and authorizes no further retry.

Consult the dispatcher at material obstruction, authority/dependency/lease or
resource change, frozen review seam and END. Current user scope continues to
govern. Capacity-only releases remain released, and all UNKNOWN worker
observations and quarantined path leases remain unchanged.
