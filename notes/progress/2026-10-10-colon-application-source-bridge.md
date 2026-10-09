# Colon application source bridge (2026-10-10)

## Scope

The existing HIR `LocalSource` projection now admits `ColonApplicationTail` as
an `Apply` tail when it owns exactly one inline `OperatorChain` argument. The
callee, argument expression, source occurrence, source node identity, and range
continue through the existing Apply representation. For
`my test run_io cb = run_io: cb 1`, the colon argument is the nested `cb 1`
application.

This is a source-availability bridge only. It defines no handler, intrinsic
`run_io`, typed Call rule, effect subtraction, hygiene result, or inference
scheme. Multi-direct-child, recovery, and unsupported layout shapes remain
structural projection errors. The parser's explicit sequence owners keep the
outer comma outside this one-argument tail.

## Evidence and review

- Focused `yu-hir` source tests cover the requested nested application and
  identity/ranges, ordinary ML and Call controls, empty Call, recovery and
  indented-body rejection, malformed multiple-direct-child rejection, and root
  / parenthesized sequence ownership.
- `RUSTC_WRAPPER= cargo test -p yu-hir shadow_colon_application --
  --test-threads=1`: 5 passed.
- `RUSTC_WRAPPER= cargo check -p yu-hir`: passed.
- The final staged delta passes `git diff --check`; the final test file was
  formatted and the focused test passed after the range assertion adjustment.
- One independent regression review found no production regression. Its test
  weakness finding was repaired by checking the suffix after the colon tail's
  actual source range and checking end-to-end LocalSource rejection for the
  grouped sequence. A fresh delta review closed that finding.
- M2: one independent regression reviewer; no performance measurement was
  indicated for this constant-size structural conversion.

## Remaining work

This does not close the user's example. The effectful argument still needs its
ordinary Apply argument-effect port to participate in the annotated
contravariant attachment and output projection. The callback's independent
`'b` flow must survive while only the matching attached `io` is subtracted.
The expected scheme remains `(int -> ['b, io] 'c) -> int -> ['b] 'c`; typed behavior,
complete Call, effect hygiene, soundness/principality, public/default migration,
and F5 cutover remain open.
