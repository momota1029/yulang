# R54 Rust implementation handoff

Assignment: `EFFECT-PERMISSION-OWNED-PROJECTION/20261031-R54`
Contract SHA-256: `480535acc8ef0a25c9aa4a9a96a567dd546cc7043dbf45324683733f8a49421f`
Admission SHA-256: `7826998d952795a7fddf01790cb3838a1e9a834e903dcb87aba86a0ceae289e3`
Requested model/effort: Luna/high. Observed model/effort: UNKNOWN.

## Implemented bounded contribution

`ReceivingResidualExperiment::native_owned_projection` now constructs a private `OwnedResidualProjection` borrowing from the owning experiment. It retains pointer anchors to the exact experiment, schema, session, batch, whole-publication observation, and live candidate `State`. It builds complete dense-index inventories from owner collections before any call/query selection: publication, calls, facts, effect rows, relations, origins, origin-attached source drains, drain completions, admissions, and emissions. Fallible reservations and any missing/misaligned owner evidence return `None`; forwarding and ordinary inference do not read this observer.

Round-trip validation requires exact indices and pointer equality against the owning iterators. The source fact is selected through the original relay/answer `Action::Fact` schedules and checked against the retained original fact, edge scrutinee, catch, owner roots, and local slot 51. The plan is traversed in original order: Suppress consumes no call; each Forward consumes exactly one corresponding retained call at its original plan index with matching publication identity, endpoints, upper row, occurrence, and cause.

For each call, the projection resolves the exact origin, source-drain receipt, completion, relation, admission and emission through stored owner indices. It checks the per-call origin/completion/emission cuts, task and cause, source relation pair, physical result-row slot, emission/readback bound, constructor-after-append phase, and evidence owner links. AlreadyPresent requires the original physical slot and prior emission count and rejects emissions of that slot in the call's window. New emissions must resolve to the exact admission/relation and occur in that call's emission window. Initial row/atom vectors are checked as prefixes of the final live row vectors, which must match the observation.

Raw source coordinates are reconstructed from the retained original fact terms by `raw_source_effect_endpoint`: Component uses the same session's pre-representative `component_endpoint(term).ordinal`; LiveVariable preserves its ordinal only under the exact effect-kind and polarity guard; the two effect leaves map to their corresponding endpoint constants. Canonical coordinates are derived with `canonical_effect(raw)`. Validation recomputes both coordinates and requires the existing `effect_endpoint(term)` result to equal the canonical coordinate. This retains a raw/canonical relation rather than treating the already-canonical `effect_endpoint` result as raw.

`candidate_context.rs` adds feature-gated borrowed iterators over complete relation, completion, and bound-emission owner collections, needed where prior observers exposed only filtered projections or counts. These add no mutation route, producer history, new identifier, or public API. The projection remains private and feature-gated.

## Source/native boundary and remaining gap

This code constructs a finite, same-owner native projection and refuses missing, collapsed-index, foreign-pointer, mismatched-call, or raw/canonical-substitution evidence. It does not construct Rust values proving the entire R50 semantic `Context` or establish that all retained Rust reads faithfully denote the source-level primitive reads in that same context. That full source extraction premise remains open as the R54 contract requires. No producer outside the leases was needed for the bounded projection.

The projection is research-only observer evidence, not a cutover, compiler behavior change, parent A/B theorem, source-domain theorem, or production authorization. Existing R53 whole-publication records and R50–R52 Lean/model evidence are reused only within their admitted conditional scope; R32–R34 are not used as solver evidence. No runtime execution or Rust type-check is claimed.

## Checks and frozen outputs

- `git diff --check`: PASS.
- `python3 tools/agent_sprint.py check`: STATIC CHECK PASS; this is not execution or independent review.
- No build, tests, Cargo, Lake, formatter, or project execution was run, per contract.
- `crates/yu-solver/src/candidate_receiver.rs`: SHA-256 `cd914826f79cec065af2dbba7bb79d0ddc7681080e12a0e974738186118e769f`.
- `crates/yu-solver/src/candidate_context.rs`: SHA-256 `8fa738f5050b642a9a52a55ffb2744cadeb95a0a0decefcc336663430deb4f89`.
- This handoff hash is to be recorded after writing by the primary.

## Evidence reused, limits, hygiene

The R53 outcome/review and R50–R53 source/model pins listed in the frozen R54 contract were rehashed before edits and read for the exact publication/call owner model. R53's successful conditional whole-publication correspondence was retained; its explicitly open faithful-extraction premise was not upgraded. No R32–R34 theorem or callback source correspondence was imported.

Only the two leased Rust files and this handoff were written by this worker. `git status --short` also showed many unrelated pre-existing dirty/untracked paths, including the R54 Lean module being written by the proof lane; none were touched. No scratch or disposable path was created by this worker. No Git mutation was performed.

STOP: source-only review and the two permitted checks are complete. The exact frozen source hashes above are ready for independent review. No further writes will be made in this assignment.
