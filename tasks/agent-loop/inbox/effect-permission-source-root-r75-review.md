# R75 independent review

Reviewer: `/root/r75_review`, fresh independent reviewer.
Disposition: **ACCEPT for the bounded R75 source repair and conditional Lean result.**
Findings: **0 BLOCKING, 0 major, 0 minor.**

Review performed read-only. No file was edited, including the proposed
review-report path. The primary materializes this report.

## Cause and Rust correspondence

The change repairs the cause of the private inventory rejection.

- `candidate_receiver.rs:2346` constructs the source pair as `TypedPairKey::Value`
  from the same Internal fact's endpoints. At `:2350`, that pair is passed to
  `checked_emission_for_internal_use`; the successful result now retains that
  exact pair.
- `candidate_context.rs:3159` independently authenticates the admission
  relation against `bound_pair(admission.bound)`. The caller's fresh bound has
  Effect endpoints.
- `candidate_context.rs:3170` selects the source-use root using the exact use
  occurrence and Value pair. Its source-drain checks retain completion, origin,
  cause, task and selected-root identity.
- `candidate_context.rs:3164` preserves
  `require_relation_ancestry(emission_relation, source_root_relation)`. The
  implementation at `:3199` takes descendant first, ancestor second.
- `candidate_receiver.rs:4345` retains both IDs and the source pair. At `:1821`,
  each ID selects its own indexed relation-table row and validates its
  corresponding pair. The returned view at `:1871` retains both IDs.

`TypedPairKey` derives equality and has disjoint Value/Effect variants
(`lib.rs:809`). The relation reader is functional. Consequently, the baseline
requirement that the Effect admission relation equal the Value source relation
cannot hold in this checked mixed case. Removing that equality and validating
each role separately is justified.

The tables originate in the same owner's complete indexed inventories
(`candidate_context.rs:2985`, receiver `:3464`).
`ProviderNativeContextProjection::capture`, receiver `:4590`, also checks owner
and emission/admission pointer identities. Shared immutable borrows prevent
mutation between these checks and inventory capture. This supports retaining
the earlier ancestry authentication without rerunning it.

The existing physical-slot, admission/emission index, bound, source-use, fact
identity, permission and owner joins remain. The patch introduces no alternate
ancestry search or failure conversion. `SearchLimit` from the original native
helper continues through `?`; the newly explicit missing admission relation
produces `MissingRelation`. Structural inventory mismatches retain their
existing unavailable-view/`BoundMismatch` behavior.

All source additions are feature gated. `inventory_package` has no ordinary
inference callsite. The existing private certificate path gains retained data;
no constraint generation, solving, routing or publication operation changes.

## Lean review

I inspected the actual R39/R45/R47 definitions and R75 proof terms before using
the author's explanation. R75 uses the existing R47 endpoint constructors,
functional relation reader, query/probe roles and ancestry semantics.

All **13 theorem declarations** match the retained successful audit's printed
types:

| Declaration | Premises and conclusion |
|---|---|
| `value_effect_disjoint` | Arbitrary `Id`, endpoints `v,e`; `IsValue v → IsEffect e → v ≠ e`. |
| `typed_relation_ids_distinct` | Arbitrary functional reader and IDs; both read equations and Value/Effect pair hypotheses imply distinct IDs. |
| `roles_distinct` | `RelationRoles e q p sourcePair → q.rootRelation ≠ p.relation`. |
| `old_guard_rejected` | The same roles imply `¬ OldEqualityGuard q p`. |
| `roles_preserve_ancestry` | The roles imply `RelationPath e q.rootRelation p.relation`; no equality-instance hypotheses. |
| `matches_from_local_ownership_and_roles` | With only `[DecidableEq Id]`, explicit `LocalOwnership` and `RelationRoles` imply R47 `Matches`. |
| `mixed_roles` | Establishes the finite fixture's relation roles. |
| `mixed_local_ownership` | Establishes the fixture's remaining R47 ownership obligations. |
| `mixed_matches` | Establishes R47 `Matches` for the fixture. |
| `mixed_ancestry` | Establishes the fixture's root-to-emission relation path. |
| `mixed_old_guard_rejected` | Rejects the old equality for that fixture. |
| `mixed_accepted` | Existing R47 `extract` returns the fixture certificate. |
| `mixed_discriminates` | Combines extraction success and old-guard rejection. |

The first two theorems require no `DecidableEq Id`. Constructor disjointness
covers both row and atom endpoints. `LocalOwnership` retains every remaining
R47 `Matches` conjunct, including physical uniqueness, current/historical
readbacks, positive entry ownership and `RootMatches`. The composition theorem
therefore does not conceal those obligations.

The fixture uses source relation `0`, emission relation `1`, and dependency
`(0,1)`. R47's forward root-to-emission ancestry and Rust's reverse traversal
from descendant to ancestor express the same direction.

Complete recorded transitive axioms:

- `value_effect_disjoint`, `typed_relation_ids_distinct`,
  `mixed_local_ownership`: `[propext]`.
- All other ten: `[propext, Quot.sound.{u}]`.

The successful receipt contains no `sorryAx`, `Classical.choice` or additional
axiom. Static inspection of the flattened dependency cone found no authored
holes, project axioms or checker bypasses.

## Audit binding and deviation

I independently reconstructed the successful stdin **in memory**, preserving
R39/R45/R47/R75 sources except removal of project import lines and addition of
the declared audit footer.

- Input: **64,305 bytes**, SHA-256
  `8b3b30ed3a8333573aa5a78b923819491be56456f7d0e958085a4f0ec119d91c`.
- Exactly 13 theorem checks and axiom queries.
- Retained stdout reconstructs SHA-256
  `b1053c85ddf239c336f80964a5088533d80814db116592c7b0253b90353e029d`.
- Retained stderr is empty.
- Receipt reports exit `0`, elapsed `6.718` seconds, `-j1 -M1024 --stdin`,
  timeout `120` seconds.

This independently binds the reviewed bytes to the recorded successful audit.
I did **not** rerun Lean or independently observe that historical process.

The first audit remains a failed audit: exit `1`, fixture typeclass failures
and recovery-generated `sorryAx`. R39 was measured before that invocation but
was absent from the initial frozen manifest. Amendment 01 records that
prior-pinning deviation and prospectively authorizes the repair audit; it does
not retroactively authorize the first invocation. These limitations remain
visible in the submission.

## Verified hashes

| Artifact | SHA-256 |
|---|---|
| Baseline receiver | `6452e18c32bd55e49b31a2dcd474d39140ca97b73ce71a0f4fede07d32b4840e` |
| Reviewed receiver | `29fccb4808106f13e761f97c9bda1201f175944dccb916e437edaf1b694609fd` |
| Rust handoff | `eba8078634d385151a8914e3d640be541ef8f1930e57ddbc0095e2acd649290f` |
| R75 Lean module | `e868eb6bc6cba74af4f3096cc7fb2e48503c8183e064071b84022923c2bc6821` |
| Proof handoff | `2fa485cec5db25e428941536bf2bc78982ae0e2dbda9adc9a5cd1fa433033bee` |
| Contract R1 | `bbeb3cc4bf26a8fe29b2144dc086e6e0efa6bd7c0f9d2ec5ab8aeab8401db3fb` |
| Manifest R2 | `518ff1313ecc5c837c5fd97bd958ad879ddf585b18e3783c915b695cef916db6` |
| Amendment 01 | `9f3ecd46bcb2cef58783f8f525502f152310ce8c1df219dbc2f1bac8ba44fd6d` |

Every unchanged manifest input and the pinned Lean executable also matched its
declared digest.

## Checks and remaining boundaries

`git diff --check` passed. I read the existing receiving-residual tests covering
suppression, operation identity, grouped scrutinees and private-envelope
controls. No dedicated test exercises this inventory join. No tests, compiler,
Cargo, Lake, Lean, formatter or build ran during review.

Rust compilation/runtime and normal project-import integration remain
**UNVERIFIED**. The result establishes the private relation-role repair and the
conditional/finite Lean statements. It supplies neither an actual Rust-to-R47
extraction nor a genuine R66 `Root`. Derivation of `sourceProbe` and its unique
source plan, incidence and remaining native ownership/readback evidence stays
open. Original A/B and production closure remain open.

**Reviewer state: STOPPED / WRITES STOPPED.**
