# Source occurrence to current Q/R capture shadow crosswalk

Date: 2026-10-09
Baseline: `400fa1a910e281131326a4f203141eeb27492c3b`
Scope: default-off structural correspondence for current solver uses only

## Result

The focused observer test uses `my id x = x; my a = id; my b = id` to join
each of the two original `id` expression occurrences to its collection-branded
resolved `DefinitionUse`, finalized current target scheme, and complete current
Q/R capture. The source positions are distinct and both map one-to-one to the
two uses. Each route covers its target scheme's nonempty Q/R inventory with
distinct row identities. The two uses share the same target scheme but have
separate fresh rows; a second successful solve has separate capture-owner
identity. Optional shadow `UseId` projection is absent for this ordinary
fixture, while exact raw source positions remain available.

Both `CurrentToSuccessorQrCorrespondenceUnresolved` and
`UseTimeSharedContractTransportUnresolved` remain asserted. A parse position
identifies a source occurrence; it supplies no slot, successor binder, owned
versus fixed classification, shared-contract transport, or source acceptance.
Internal same-SCC uses and parameters/captured local applications remain
distinct cases.

The exact successor-side missing judgment is source generation from an
original component `C` and its actual enclosing context `Gamma` of the member
roots, eligible owned coordinates, fixed captures/imports, original binder
scopes/order, and complete joint relation/evidence. Only with that partition
can an ordinary source use coherently freshen owned coordinates and keep
imports fixed. The current F5 Q/R inventory does not generate this partition,
and the charter does not require successor binders to preserve F5's Q/R
representation. Adding a current-source row query would not discharge it.

## Review and checks

Regression-auditor review passed with no findings. The reviewer confirmed the
source identity, exact scheme join, complete capture inventory, distinct
per-use row identities, separate solve ownership, and retained unresolved
successor premises. No semantic or production path changed.

Focused test:

```text
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-solver \
  --features shadow-f5,shadow-scc-observer \
  exact_source_uses_join_nonempty_current_qr_captures_without_successor_evidence \
  -- --test-threads=1
# 1 passed
```

The configured sccache wrapper failed before compilation; clearing
`RUSTC_WRAPPER` made the focused run pass. Rustfmt and `git diff --check` passed
for the changed test. One Cargo process, one build job and one test thread were
used; resource measurements were not collected. No broader suite, build matrix,
Frozen Oracle behavior, successor correspondence, semantic adequacy or
production conformance was checked.
