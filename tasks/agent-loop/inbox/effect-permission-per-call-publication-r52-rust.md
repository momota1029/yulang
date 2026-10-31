# R52 Rust per-call publication handoff — revision 1

Sprint: `EFFECT-PERMISSION-PER-CALL-PUBLICATION/20261031-R52`  
Contract revision/hash: admitted R52 contract, `24d286d8eb80c3ac926fe0b65b27a5f9d8b51d231ba750061bcfbbfdbc0cb93d`  
Assignment: Rust author `/root/r52_rust`, handoff revision 1.  
Parent: original Simple-sub A/B and `SourceProblem.InferenceSoundness`; unchanged and OPEN.  
Claim class: implementation / provisional source-native observation.

## Runtime and frozen inputs

- Base checkpoint: `ccdb3e6bb` (primary-confirmed R52 integration base); the R52 contract's original dependency baseline `b8564a10bb6c10dfea61434441a73c718a3d927b` is retained as provenance.
- Requested lane: Luna/high implementation lane. Effective model/effort and runtime session telemetry are UNKNOWN to this worker; launch and RUNNING state were confirmed by the primary.
- Frozen pre-write artifact hashes matched: receiver `41272bf276761cdfe847264b4aaf0093d9feab361ca8d80881fd69ca86d449e0`; context `c26a152e957980fcc844b7ff7145f712c4fd218b03415c50263e3dd81156c71f`; read-only `lib.rs` `25498cc1be404b12d060cbd47f77e78c23ad27b2b99113e15823bc8b6fa92ca4`.
- R51 model `78a729b25e95812ba292c4e625ec69e46ff5eb70ff3ac2ae5b85dd1b33214d61`; R50 model `4fc4380f3ad1827ecf155f982e5186b32d6d66d91909039fb118063d8f1e2df2`; R51 outcome `dce798fe2270685b35b0d432b37905cdd66a487689a34a97406df0113dec7caf`; R51 review `5ee94d0574e12a03ec23ac71ef65cd860dfd658977d78b659169fe27b21e4bc5`.

## Result and source path

The private receiver now allocates a process-unique, checked publication identity and associates every actual Forward invocation with its original complete-plan index. Immediately before each `constrain_live_effect`, the optional observer takes that call's origin, completion, and emission cuts and records the exact pre-call physical slot value plus prior emissions for that slot. Only after a successful return does it inspect the corresponding half-open windows, require one exact matching source origin and completion, and capture that call's physical bound evidence. New emissions must lie in that call's emission window; AlreadyPresent preserves the existing slot, including zero old emissions and zero new emissions.

`native_publication_call(identity, plan_index)` selects uniquely by the pair before a caller compares endpoint fields. Adjacent calls with identical occurrence/task/cause cannot supply one another's origins, completions or emissions. Missing identity, plan metadata, any observer reservation, or any exact-window evidence disables the whole observation; it does not alter Forward order, arguments, successful returns, or ordinary inference success. The original outcome-vector allocation and actual `constrain_live_effect` errors remain on their pre-existing paths.

Path: receiver plan decision and plan index -> best-effort pre-call cut -> actual `constrain_live_effect(endpoint, pending.upper, fact.id, fact.cause)` -> successful-return origin/completion/emission window -> unique observation query by `(publication identity, plan index)`. The context helper verifies the exact completion index inside the call window. No `lib.rs` producer change was required.

## Evidence, boundaries, and remaining premises

- `git diff --check -- crates/yu-solver/src/candidate_receiver.rs crates/yu-solver/src/candidate_context.rs` passed.
- No build, test, Cargo, Lake, Lean, formatter, cache, target, scratch, worktree, or environment operation was run, per contract. This is source inspection and diff-format evidence only; compilation and execution remain unverified.
- Reused R51's retained source-drain, completion, physical-slot, admission, and emission evidence. Rejected as insufficient the R51 publication-wide frontier and post-hoc `checked_source_drain(occurrence, cause, task)` selection; the active capture path uses only cuts bracketing the actual call.
- The observation is still provisional. It does not establish executed Rust behavior, complete source extraction, the original A/B, subtraction, soundness, principality, termination, whole-language effect hygiene, or production cutover. The R51 reviewer also identified raw stdout capture authentication as a separate receipt caveat.
- Falsifiers for review: repeated identical calls; swapped indices; duplicate identity/index rows; older origin/completion/emission; a later call's evidence; cut off-by-one; AlreadyPresent with zero prior emissions; missing completion; lost allocation/identity. Observer loss returns no observation while Forward remains successful.
- No scratch or generated output was created. No descendant workers.

## Frozen artifacts and resource receipt

- `crates/yu-solver/src/candidate_receiver.rs`: SHA-256 `2707cbe4c41a4f91816ef85fe18ac58cc3f5dfe22a648cdcd598215843cb5d4d`.
- `crates/yu-solver/src/candidate_context.rs`: SHA-256 `c9deb23ebb2b7762f6404c6529231f3581e9959082ee301e03eb1c0895d111eb`.
- `crates/yu-solver/src/lib.rs` unchanged: SHA-256 `25498cc1be404b12d060cbd47f77e78c23ad27b2b99113e15823bc8b6fa92ca4`.
- This handoff SHA-256: report in intake message after freeze.
- Budget: <=1,200 seconds; measured process resources not applicable because no build/test process ran. Assignment elapsed-wall telemetry is not available to this worker; the primary retains the launch envelope accounting.
- Worker state: STOPPED after freezing this handoff; writes stopped; no unresolved descendant lease. Frozen review/integration pending.

Next in-envelope step: independent review against the R52 falsifiers and the Lean R52 call identity/cut correspondence. Any producer change outside the two Rust leases returns to Luna as a specific dependency; none is requested here.
