# NATIVE-READBACK-AND-CALLBACK/r7 proof handoff — revision 1

Outcome: **STOPPED / INCOMPLETE — dependency and external-effect boundary.** No Lean module was written. No theorem was constructed, checked, axiom-audited, independently reviewed, or promoted.

## Authority, worker, and authenticated inputs

- Contract: `tasks/agent-loop/sprints/native-readback-and-callback-20261028-r7.md`, SHA-256 `35b3b0b23eeeb842acddc47ce4685bb8bd1ad6152825c9d1cbba4ba6bce0840a`; admission baseline `16cab92bb`, source baseline `7b3ad7074`.
- Worker `/root/native_readback_callback_r7_proof`, registered leaf packet; requested `gpt-6-sol/high`, observed model/effort UNKNOWN. No descendants.
- Initial immutable manifest SHA-256 `72cd5bb14ddc4f203d0f4ce8a311b0b4204376a9e1139add990105530184e200`: all 15 exact files independently MATCH before dependent reads, exit 0; ACK at `2026-10-28T09:51:14Z`.
- Amendment 01 SHA-256 `ad7c7c365cfc6e559df2ec7444c0d851073d40e85db6bfaeeab1cfe3a8bcbef8`, revision `b5b66d697`; amended manifest SHA-256 `e49700a9c8e446633de567c3cafe6ce6eb71d77ca42a393b0c6164c5b93d1aec`: all 19 exact files independently MATCH before amended reads, zero missing/mismatches, exit 0; ACK at `2026-10-28T09:57:33Z`.
- Source bodies read only from the two immutable proof snapshots and frozen R6 review/outcome. The three additional solver files were hashed only in the admitted R7 source snapshot before amendment; their bodies were not read there. No mutable R7 Rust outputs were consumed.
- R6 review SHA-256 `4323f806ad9767f9da111dfca187b3866bb9bc54a203d6825ad85ea96007ebe3`; R6 outcome SHA-256 `4fc13d56c2ce12d13e94f467545bc94ea00983de57c509e83e532f216f5348b5`. Both retained as rejected failure references.

## Original parent and bounded source application

Original manuscript: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`, §§1, 3, 5; governing corrections `notes/design/2026-10-24-birth-level-scc-intrusion.md`, §§2–6, and `notes/design/2026-10-10-annotation-effect-hygiene-integration.md`, §1 and clarifications. Exact parent definition inspected in pinned `Contracts.lean`:

`YulangClosure.SourceProblem.InferenceSoundness p = ∀ s x d a, p.supported s → p.generates s x d → p.solves d a → ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a`.

`YulangClosure.SourceProblem.NativeCorrespondence` is separate. No lemma can yet be applied: there is no delivered declaration. All original source cases, quantifiers, shared witnesses, immutable Value-birth qualification and annotation-effect policy remain unchanged and OPEN. No concrete `LocalLaws` instance, source judgment, launch theorem, or production authority follows.

## Pinned caller/callee chain and precise obstruction

All locations below refer to the r2 immutable snapshot:

1. `crates/yu-solver/src/lib.rs:9253`, `InferenceSession::observe_typed_route_capacity`: physical-change flag precedes the callback; failure flag is written only after returned `Err`, with panic bypassing that branch.
2. `lib.rs:10774`, `sample_f4_resources`: test trace sample precedes attempt increment, then TLS peak reads **route_journal.value_rows.capacity()**. This owner is distinct from replay undo capacity. `sample_f4_resources_with_finish_output` passes zero finish bytes and no term/store overrides to `sample_f4_resources_with_term_override` (`10821`).
3. `sample_f4_resource_parts` (`lib.rs:11017`) prepares a counter clone, can return early from checked arithmetic, prepares/mutates a LOCAL test ledger clone, and can fail before its publication. The visible assignments publish ledger, counters, and sample count in that order (`lib.rs:11424–11430`).
4. The route-lane fold can panic after publication (`lib.rs:11431–11436`). `f5c_session_baseline` is then called at `11437`, before `completed_sample` in the enclosing override path (`10995`). Completed-sample argument evaluation can itself panic: `IndependentNestedCapacityLedger::total_bound_bytes` (`lib.rs:5165`) uses panicking `checked_usize_sum` (`322`). The completed callback can mutate TRACE before a panic; a later matrix observer can detach/mutate its observer before panic and restore it only at `lib.rs:20744`.
5. Exact newly authenticated owner: `crates/yu-solver/src/f5c_draft_heap.rs`, SHA-256 `b973ec0667e6f80de54d9a1de55df112361859982ea2617dae3fe8d34903b1cb`. Its export (`802`) maps `f5c_session_baseline` to `event_sink::session_baseline` (`378–397`). That body conditionally mutates WALKER_LEDGER and calls `event_sink::record` (`540–554`). The latter first flushes any excluded interval (`Sink::flush_excluded_interval`, `311–319`), then records the baseline via `Sink::write_words` (`303–308`).
6. `Sink` (`299`) contains **BufWriter<File>**. `write_words` calls `self.writer.write_all(&word.to_le_bytes())` once per word. This is an actual external sidecar write, not a pure counter operation. A write can partly reach the buffer/file before returning `Err`; that Err sets `sink.failed = true`, is not propagated as the sample's Result, and the loop continues. Each attempted word is followed by wrapping checksum addition. After all eight words, checked count increment can panic. An excluded-interval record may already have been emitted before the baseline record. On normal excluded-record return, interval capacity, interval bytes and dirty flag are updated in order. On a panic, earlier sidecar/TLS effects remain.

The exact external `std::io::Write::write_all` / `BufWriter<File>` buffer/file effects and exits are outside the 19 authenticated source inputs and current permitted effect interpretation. No std implementation or newly named owner was read. Amendment 01 explicitly requires stopping for an unresolved external write/exit; the primary acknowledged this boundary and directed this handoff, with no Lean write.

A minimal mathematical frame could explicitly retain sink failed/checksum/count, excluded-interval state, partial sidecar output, ledger/counter/sample publication, TRACE mutation, and detached matrix state. However, an exact native realization would still need an authorized external-I/O contract and its source/model bridge. Treating that effect as pure or replacing it with unconstrained evidence-preservation would assume the very footprint at issue. No non-assumptive exact callback theorem is available within this unchanged contract and remaining grant. This is a missing dependency/effect premise, not a counterexample to the projection claim.

## Evidence, omissions, and next owner

Executed only read/hash/inventory commands (`sed`, `rg`, Python hashlib/path reads, clock). Hash scripts exited 0; Python observed `3.12.3`. Inspected project pin is `leanprover/lean4:v4.35.0`, empty package manifest, `-j1 -M1024`; actual Lean/Lake versions, goals, diagnostics, exits, theorem types and transitive axiom results are **NOT_RUN / unavailable**. No checker, build, tests, formatter, installation, Git, or scratch output ran. There are no delivered theorem names or axiom claims.

All callback-prefix construction and source/native realization remain omitted, including exact capacity arithmetic, TLS/internal observer prefixes, sidecar partial writes, wrapper composition, and matrix unwind/drop effects. No `clear_diagnostic_scratch`, seeding, enqueue/receipt, destination/Running or parent instance was modeled. First remaining owner: **Luna, callback external-effect authority/source intake**, to decide and freeze a non-assumptive BufWriter/File effect interface and any additional exact dependencies. A subsequent separately admitted proof packet must first derive that bridge, then construct and independently review the complete callback frame. The later launch owner `clear_diagnostic_scratch` remains OPEN separately.

Read-scope deviation: the first amended incoming_sample_trace read printed the entire small file, including unrelated start/event/finish helpers, rather than only the requested sample/completed_sample methods and support declarations. No extra file/path was read or written; those unrelated bodies were not used as proof evidence. This is disclosed rather than silently omitted.

## Resources, paths, and cessation

Original grant: 900 seconds, no renewal. Actual launch timestamp and total active CPU/RSS were not captured locally: UNKNOWN. Locally observed interval from first authentication `09:51:14Z` to final source/hash stop `09:59:04.975793Z` is 470.98 seconds; this does not include earlier startup. Therefore no more than 429.02 seconds of the original grant could remain at that point. A conservative local deadline of `10:04:00Z` was adopted, without resetting the primary's earlier bound. No resource capacity is claimed reclaimed.

Only changed path: `tasks/agent-loop/inbox/native-readback-and-callback-r7-proof.md`. Leased Lean path `isolated/native-readback-and-callback-r7/notes/theory/lean/YulangClosure/NativeResourceCallbackR7.lean` was not created or edited. Scratch/generated paths: none. No descendants or outstanding generated-output writers.

Construction and source reads have stopped. This revision is frozen at UTC 2026-10-28T10:00:30.701827+00:00; after this handoff write, **all writes STOPPED**. Independent review and any conditional checks remain primary-owned and NOT_RUN.
