# R250 — pinned standard-library module graph

Status: RESULT; graph traversal implemented and exercised. R149 remains OPEN.
This is source-resolution evidence, not semantic name resolution or proof.

## Outcome

The pinned standard-library loader now starts at the implicit `std` module,
follows source `mod` declarations, and follows `std::` header imports through
the longest bundled module-path prefix. It returns each reachable source with
its original relative path, bytes and Git blob ID. A visited set makes repeated
imports and cyclic module edges terminate.

The traversal reaches exactly the 40 sources in the R149 rev10 manifest. Every
declared child module is checked against the bundle. Every `std::` import must
have a bundled module prefix after the `std` root. The resolver does not look up
imported value names or decide visibility; those remain semantic resolution
work. Playground syntax setup now obtains `std::core::ops` through this
resolved graph; the immutable result is cached for subsequent parses in the
same process.

## Checks

- Five focused `pinned_stdlib` unit tests passed: all 40 blob identities,
  `std` and `std::core::ops` path lookup, exact root closure, missing-prefix
  rejection, and termination on a synthetic cyclic graph.
- Focused CLI tests for the six checked-in playground samples passed again:
  identity (1), ordinary islands (6), diagnostics (1), repeated choice (1),
  and polymorphic closure (1).
- `rustfmt --check` passed for `pinned_stdlib.rs`. The edited `lib.rs` check
  reports existing formatting differences; the same check also fails on its
  committed HEAD version, so the file was not broadly reformatted.
- `git diff --check` and `python3 tools/agent_sprint.py check` passed.

## Remaining work

The playground does not yet consume this graph to resolve imported values in
HIR or inference. The unchanged R149 Console sample still lacks imported
`println`, `say`, and role/operation semantics; Types still needs tuple
formation, inference and runtime support. Whole-module evaluation, authenticated
host writes, output publication and source/native proofs remain open. No sample
completion or proof gate follows from this graph test.
