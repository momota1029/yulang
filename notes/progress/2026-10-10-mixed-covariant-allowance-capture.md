# Mixed covariant allowance capture through extrusion (2026-10-10)

## Result

The private live candidate now retains incoming typed bounds for a covariant
effect annotation row that has both a concrete allowance and a symbolic tail.
If a fresh local scheme captures that tail before a later effect lower arrives,
the incoming allowance relation is captured, positively reconstructed by
extrusion, freshened, and applied to the later lower. Listed concrete effects
remain local to the annotated row; unmatched concrete effects reach the
symbolic tail boundary.

The owning representation is append-only incidence metadata indexed by
canonical effect row. Equality/intrusion splices row buckets without copying
incidence records or adding reverse solver/SCC edges. Positive extrusion
reconstructs the incoming allowance with the positively mapped source and the
exact copied tail. Scheme capture deduplicates canonical typed bounds while
preserving distinct annotation views. Transaction rollback restores records,
keys, bucket descriptors and modified links.

## Review and verification

Independent compiler and performance delta reviews found no blocking, major or
minor findings. The semantic review traced the actual source route through
local annotation publication, use-time capture/freshening, later actual
argument solving, and recapture at the resulting annotation boundary. The
kernel test establishes copy → capture → freshen → lower; the source regression
covers a later actual-argument lower before the resulting binding is captured
and consumed. These are complementary orders, not a claim that the kernel test
exercises copy → lower → capture.

Focused checks passed:

- `RUSTC_WRAPPER= timeout 180s cargo test -p yu-solver --features shadow-apply-candidate --test candidate_effect_annotation --offline -j 2 -- --test-threads=1` — 17 passed.
- `RUSTC_WRAPPER= timeout 180s cargo test -p yu-solver --features shadow-apply-candidate --lib positive_extrusion_retains_mixed_allowance_before_capture_and_late_lower --offline -j 2 -- --test-threads=1` — 1 passed.
- `RUSTC_WRAPPER= timeout 180s cargo test -p yu-solver --features shadow-apply-candidate --lib capture_incidence_merge_chain_keeps_one_record_per_relation_and_rolls_back_splices --offline -j 2 -- --test-threads=1` — 1 passed.
- `RUSTC_WRAPPER= timeout 180s cargo test -p yu-solver --features shadow-apply-candidate --lib root_computation_annotation_rolls_back_storage_and_retries --offline -j 2 -- --test-threads=1` — 1 passed.
- `RUSTC_WRAPPER= timeout 240s cargo check -p yu-solver --all-targets --all-features --offline -j 2` — passed.
- Scoped `git diff --check` — passed.

The performance review found incidence registration and bucket splicing
expected amortized O(1), with O(R) retained incidence records for R unique
source/view registrations; capture and positive extrusion visit reachable
records. No timing or allocation measurements ran. Historical source IDs may
retain duplicate canonical relations after coalescing, and failed-capture peak
scratch accounting remains approximate under the existing sampler.

This checkpoint closes only the mixed covariant allowance capture/extrusion
path and its tested source lifecycle. It does not close the user's full
`run_io` callback scheme, contravariant concrete subtraction, complete effect
hygiene, Call semantics, soundness/principality, public/default migration or
F5 replacement.
