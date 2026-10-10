# FunctionPort lifecycle-generation hook

## Scope and authority

This M1 implementation slice follows the private candidate suspension contract,
especially §§4–6. It adds one exact producer hook for dependency-only
`FunctionPort` admission. It does not establish complete mutation registration
or authorize candidate certificates.

## Change

`candidate_context::State::dependency` now advances a private lifecycle
generation only when it publishes a genuinely new exact `FunctionPort`
dependency. The existing dependency set remains the owner of exact identity;
duplicate keys are inert, and `Derived` dependencies remain outside this first
hook. The generation is separate from intrusion equality generation.

Generation exhaustion is checked before reservation or edge mutation. Existing
context checkpoints restore the generation with dependency rollback. The fixed
generation value and its active checkpoint copy are included in retained-byte
accounting. Tests cover dependency-only admission, duplicate inertness,
overflow-before-mutation, route rollback and retry, and an ordinary identity
source that completes without suspension or certificate readiness.

## Review and verification

One compiler-referee M1 review found no issue in the frozen slice. Focused
verification exposed an incorrect test assumption that `State::bytes()` only
contained the new `u64`; the assertion was corrected to account for the
pre-existing fixed state. The reviewer delta-checked that repair and found no
new issue. The test compares `bytes()` with the independent enumerated census.

Passed:

- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-solver --features shadow-apply-candidate --offline --jobs=1 function_port_lifecycle_ -- --test-threads=1`
- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-solver --features shadow-apply-candidate --offline --jobs=1 function_port_identity_incidence_changes_without_new_relations_or_intrusion_generation -- --test-threads=1`
- `git diff --check`

The focused runs emitted three existing dormant-certificate `dead_code`
warnings for `RetainedInput`/`CircuitEvidence` fields and `owned_bytes`. Their
owner is `candidate_context.rs`; the missing consumer is the still-disabled
production certificate path. They remain visible until that consumer gate
closes, since suppressing the warnings now would obscure the incomplete path.

`cargo fmt --check -p yu-solver` was also attempted and failed on existing
formatting drift across the package, including untouched files. No formatter
was applied to avoid a broad unrelated rewrite. No benchmark or broad test
suite was run.

## Open obligations

This hook does not connect generation to source waits, register every mutation
producer or dependent observation, withdraw or recompute observations, retain
lower freshening/restoration/replay/typed-drain/Function/extrusion frames, or
resume atomic SCC publication. Authentic source-owned §7 recognition and
late Function/swap evidence remain open. Readiness, filter, and
dependent-observation witnesses remain unavailable; production certificates
stay disabled. The q113 source-state decision and full Simple-sub/F5 goal also
remain open.

## Next gate

Specify and implement exact observation-support ownership and source-wait
admission, with incomplete producer coverage remaining unable to mint a
certificate. Then continue the retained fresh-use/restoration/typed-child
handoff, ordered withdrawal/recomputation, and atomic SCC publication toward
the authentic §7 regression.
