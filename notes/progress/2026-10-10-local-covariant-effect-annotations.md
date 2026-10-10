# Whole-local covariant effect annotations (2026-10-10)

## Result

The private live candidate now admits whole-local annotations whose nested
effect rows are in composed covariant positions. Admission reuses the existing
whole-definition preflight: root computation rows remain unavailable, concrete
members at composed negative positions remain unavailable, and a row may retain
at most one symbolic tail. Closed empty rows at nested Function ports are
accepted. The existing paired local constructor supplies whole-initializer
checking, positive annotation publication, support/allowance propagation,
local named-tail scope and the established capture/extrusion/intrusion lifecycle.

This is covariant annotation support, not contravariant subtraction. The tests
show fixed `E` support survives a local use and conflicts at an `F`-only
boundary; a symbolic tail carries that support, and its two local effect rows
(the named tail and its Function port) are independently fresh at each use.
Initializer evaluation remains on the one-shot block edge. No source effect
operation producer or handler behavior is claimed.

The old local-effect `Unsupported` fixtures were explicitly temporary limits of
the private candidate. They did not encode a language rejection. The transition
was recorded in `tasks/current.md` before changing those expectations; only
newly admitted cases were replaced with checking/publication assertions, while
root-row and composed-negative concrete refusals remain covered.

## Review and verification

Pre-write spec review found the extension authorized by the existing
covariant-annotation policy and paired constructor, with no new representation
decision. It required the temporary-test-contract transition to be recorded and
root/negative-row exclusions to remain explicit; those conditions are met.
Post-write compiler-referee review found no blocking or major semantic issue.
Its minor fresh-use evidence finding was closed by requiring exactly the two
expected local effect rows in each use and proving every row in the first use
has a distinct identity from every row in the second.

- `RUSTC_WRAPPER= timeout 180s cargo test -p yu-solver --features shadow-apply-candidate --test candidate_annotated_primitive_formals --offline -j 2 -- --test-threads=1` — 20 passed.
- `RUSTC_WRAPPER= timeout 180s cargo test -p yu-solver --features shadow-apply-candidate --test candidate_effect_annotation --offline -j 2 -- --test-threads=1` — 9 passed.
- `RUSTC_WRAPPER= timeout 180s cargo test -p yu-solver --lib local_annotation_first_edge_failure_rolls_back_and_retries --features shadow-apply-candidate --offline -j 2 -- --test-threads=1` — 1 passed.
- `RUSTC_WRAPPER= timeout 240s cargo check -p yu-solver --all-targets --all-features --offline -j 2` — passed.
- `git diff --check` — passed.

No benchmark or timing sample ran. Concrete contravariant subtraction,
contextual residual identity, complete Call, effect operation execution,
soundness/principality, public/default inference and F5 replacement remain
open. In particular, this slice does not establish the requested
`(int -> ['b, io] 'c) -> int -> ['b] 'c` callback scheme or the behavior of
`run_io`.
