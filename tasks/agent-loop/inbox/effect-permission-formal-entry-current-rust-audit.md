# Current Rust audit: FormalEntry permission construction

Status: source audit only; no Rust or Lean code changed, and no build/test was run.

## Frozen source bytes

The inspected files were clean in the working tree at review time:

| File | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_source.rs` | `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49` |
| `crates/yu-solver/src/candidate_effect.rs` | `4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15` |
| `crates/yu-solver/src/lib.rs` | `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be` |

No dirty or quarantined path was read.

## Source construction path

`candidate_source.rs:1323–1327` clones the annotation from the actual LocalSource lambda parameter, looks up the registration using that parameter's `id`, and queues `Action::FormalEntry` with the lambda occurrence and the registered scope. `execute_candidate_action` dispatches that action directly to `candidate_formal_entry_annotation` (`candidate_source.rs:2469–2475`). This producer-to-dispatch chain is required evidence: the constructor itself checks the annotation owner and the HIR lambda parameter ID/occurrence, but does not independently compare the annotation payload with `Lambda.parameter.annotation`.

`candidate_effect.rs:1991–2012` reads the action annotation's effect row, rejects more than one row variable, and checks computation role, owner, scope, parameter recipe, source-owner lookup, exact LocalSource lambda/parameter identity, absence of a formal domain, and absence of an already retained permission for the registration. It obtains the registered entry effect.

For a nonempty concrete row, `candidate_effect.rs:2015–2039` copies the complete ordered `SourceEffectId` sequence into `FormalEntryPermission`, retaining registration, recipe position, formal ID, occurrence, owner, scope, annotation position, row position and entry effect. It reserves retained storage and accounts the temporary payload. If there is one symbolic variable, lines 2041–2045 create/find its scoped effect variable and admit equality constraints at source slot 45. Lines 2047–2051 then publish the retained permission. Empty concrete rows intentionally retain no permission.

Publication is not the final fallible operation: the resource sample at lines 2059–2063 can fail after the permission is pushed. Therefore a function-local claim that every `Err` leaves no permission would be false. The enclosing inference attempt must be treated as failed on that error; the constructor alone is not an atomic transaction. The permission checkpoint/rollback methods truncate retained entries and restore byte accounting (`candidate_effect.rs:480–501, 660–695`) when a transaction owns that checkpoint.

## Current native consumer seam

`lib.rs:18341–18470` implements `internal_formal_permission_incidence` as read-only evidence. It checks the exact internal use and unique route/fact, selects a unique computation registration and lambda recipe for the target root, verifies the exact LocalSource lambda and unique pointer-identical origin, reads the negative live effect entry from the positive Function argument, checks the original lambda fact, and finally retrieves the retained permission for that same registration/source owner/entry.

The method is marked `allow(dead_code)` with the reason “no consumer is connected.” This is the key implementation gap. The audit found no Rust consumer that applies this evidence to handling/suppression. It also found no concrete defect in the current producer or retained-record lookup that would justify changing their semantics in this checkpoint.

No dedicated FormalEntry regression test was found in the searched clean effect/context test sources. Existing checkpoint code is not test evidence for this constructor path.

## Lean correspondence boundary

The producer/action/constructor path provides concrete source reads for a future R39 `prepare`/`permissionFor` bridge. A valid bridge still has to construct the authentic pre-state (including absence of this registration), preserve the same action annotation and row, and show that the published record is the exact returned permission. The post-state alone cannot supply the pre-state guard. The source audit does not establish a Rust operational interpretation or close R116, R45, R54, or the original `InferenceSoundness` obligation.

## Next bounded work

Build the pre-state-to-retained-record bridge from these exact source bytes, retaining the action producer premise and the post-publication failure boundary. Keep the native consumer disconnected until the original effect-hygiene design's source/semantic gates and an independently reviewed integration are satisfied. Do not infer permission from equal row contents or a post-state lookup alone.

No Cargo/Rust or Lean build/test was run. No alternative environment, target directory, or cache was created.
