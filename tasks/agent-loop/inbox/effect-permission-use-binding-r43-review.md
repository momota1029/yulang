# R43 independent review

Verdict: **bounded PASS**. No blocking, major, or minor finding was established in the reviewed delta. The review was performed by a fresh non-author after both writers stopped; changed paths: none.

## Rust source review

The binder in `candidate_effect.rs:534–563` selects the actual owning `formal_entry_permissions` record by registration. A second record with the same registration rejects the binding before the remaining identity checks. It checks computation role, raw entry port, parameter recipe, formal identity, source owner, scope, Lambda occurrence, nonempty concrete payload, and effect-row kind. The view borrows the retained record and its complete concrete slice, preserving order and duplicates; it does not sort, filter, reconstruct or deduplicate the payload.

The original constructor at `candidate_effect.rs:1911–1988` authenticates the owner-local Lambda/formal, annotation owner and scope before retaining those coordinates and the ordered concrete vector.

In `candidate_scheme.rs:505–536`, the route obtains the R42 native certificate, matches registration and Lambda occurrence, and binds the same raw entry port. Definition-use and context come from that owning route. Capture at `:2974–2989` retains the original entry port beside its checked representative; FreshUse at `:4558–4567` carries the original entry port without replacing registration identity with a mapped row.

The API accepts no separate proposed annotation, use, or context argument. Returned annotation/row coordinates come from the retained permission; returned use/context come from the authenticated route. The Lean checks against separately supplied request/use values apply under explicit extraction equations and do not establish arbitrary caller authenticity.

The binder allocates no payload or persistent record. Its view borrows the retained permission; the R42 certificate clones shared identity backing. Added raw-entry fields enlarge existing incidence records whose graph, scratch and retained accounting already uses `size_of` for those record types. No inference, propagation, permission consumer, or subtraction path changed.

## Dirty-baseline isolation

Reversing only the R43 additions reproduces both admitted dirty source baselines exactly:

| Source | Reconstructed baseline SHA-256 |
|---|---|
| `candidate_effect.rs` | `82da9265af3bd663443550f4b113816cf2618c56e96014d9298c4563e875e6db` |
| `candidate_scheme.rs` | `c14f6cecb38fbf54b15e808f7385d9782dec1a784a12eac1315e1c32becd8429` |

This preserves unrelated dirty bytes and prior R41/R42 code. The reviewer used no Git command.

## Lean review

The reviewer inspected all 11 actual declarations and proofs, complete recorded printed types, and complete axiom results. All declarations are in `YulangClosure.UseScopedPermissionR43`.

- `lookup_iff`, `accepted_iff`, `payload_preserved`, `ordered_payload`, `missing_or_ambiguous_rejected`, `absent_or_multiple_rejected`, `mismatch_rejected`, `shared_images_distinct_bindings`, `shared_images_and_duplicate_order_witness`, and `foreign_and_ambiguous_witness`: `[propext]`.
- `constructed_entry_binding`: `[propext, Quot.sound]`.

`constructed_entry_binding` composes R42's construction theorem and R39's exact-retention theorem with the same permission witness. Original validation, native extraction, three lookup/image equations, and `owningTable` singleton completeness remain explicit premises. It does not derive authentic Rust tables or rich labels from hashes.

Finite witnesses preserve `[7, 7, 11]`, distinguish registrations sharing native images, and reject absent/duplicate permissions and foreign owner/formal/scope/annotation/row, Lambda label, definition-use, and context. These are mathematical witnesses, not Rust execution observations.

## Evidence and limits

Producer final audit receipt: exit 0, 2.413858 seconds, input SHA-256 `582224cf3fcbe0b57b2754565646cd1a8f6b436051efd6e249601ddea69c9e91`; stdout SHA-256 `e526d0df96670692d5d76978387efddbd44e9e8dd44fb95ea816fa698475969f`. These are inspected producer receipts; no checker was rerun by the reviewer. An earlier rejected diagnostic stream remains recorded.

R43 reports no Lake invocation. The resource receipt records one-CPU affinity, `LEAN_NUM_THREADS=1`, CPU/wall limits and `-M1024`; final RSS was 1,028,828 KiB. No strict address-space cap was used, explicitly disclosed after the prior toolchain thread failure. This does not establish a stronger OS memory bound.

Frozen snapshots:

| Artifact | SHA-256 |
|---|---|
| `candidate_effect.rs` | `73ad01324356672f1e45e56ea18d6f5bf0ded8628cce56e884960eb29bd5786d` |
| `candidate_scheme.rs` | `bf8f5c80ce2761dc2a1235d2e02e348a91bc9e8965653db26b9abd4c8d6ca631` |
| `UseScopedPermissionR43.lean` | `83ede0609353cec9dfde8258fa86f0f7c72aadef647dbe0819fe326776e46f8d` |
| Rust handoff | `c04110859cafa42cffa0d52982f6c9f52fbdd474512fa1054f37bc72f19aa9ee` |
| Proof handoff | `4f4551361b1c966576c7799a59a3fe1d3505465227810b980a9e42f5aeb8abb8` |
| R43 contract | `0e4e11482fe905f10229f08e015e3088f1da9bba3db04bd462241b9ecf920aed` |

Pinned term accessor, `lib.rs`, context, and R39/R41/R42 model hashes match the contract. No build or test was run.

Authentic source extraction, complete owning-table realization, mechanically verified Rust execution, provider arrival, permission consumption, Catch/residual subtraction, original A/B, and whole-language/production obligations remain open. No semantic decision or expected-output change is approved.

Reviewer STOP: no writes, Git, checker, Lean, builds, tests, Cargo/Lake, formatter, scratch, cache, target, worktree, environment, or descendants.
