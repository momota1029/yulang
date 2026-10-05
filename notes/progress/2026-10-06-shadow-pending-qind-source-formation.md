# Shadow pending premise for Q-independent source call-view formation

Date: 2026-10-06
Baseline: `02318df71`
Status: M1 shadow implementation slice; pre-write and post-write spec review found no blocking issues
Scope: default-off `yu-hir/shadow` Apply obligations and their structural tests

## Result

Each projected shadow `Apply` now carries a fourth explicit pending premise:
`QIndependentSourceCallViewFormation`. It names the still-unimplemented
source-producer obligation for the shared component's original contract and
receipt. The per-call record references that shared-component formation; it
does not claim an independently formed contract or receipt for every Apply.
The source comparison `Q` cannot discharge it. Typed capture attachment A
remains a separate pending closure correspondence, and the existing callable
role, full Function membership and call-view realization premises remain.

This is inert metadata in the default-off shadow lane. It constructs no
contract, `beta`/`Slots(beta)`, typed path, receipt, joint `(nu,K,D)`, provider,
receiver or semantic solution. Projection acceptance, production HIR,
production solver and inference routing are unchanged.

## Review and expected-output handling

The `spec_auditor` pre-write review approved this structural pending premise
within the explicit shadow-lane authorization. It found one minor count
inventory correction: the flat-chain test has eight Apply nodes, so its count
changes from 24 to 32, not from a hypothetical 18. The producer applied that
correction. A fresh post-write spec review found no blocking, major or minor
issues and verified O/A separation, Q independence, unchanged old premises and
all affected counts.

The updated test arrays/counts record the shadow artifact's pending-obligation
inventory, not language acceptance or semantic output. The pre-write review
confirmed that adding O preserves the old obligation categories and is
consistent with the approved FVIEW source-formation direction, while leaving
the exact constructing judgment open.

Focused checks passed:

- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-hir --features shadow --lib shadow -- --test-threads=1` — 27 passed.
- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-core --features shadow --test shadow_feature -- --test-threads=1` — 3 passed.
- Scoped `rustfmt --edition 2024 --check` and `git diff --check` — passed.

No broad suite, production differential, semantic discharge, or performance
measurement was run. The one additional pending record per shadow Apply keeps
the same linear structural scaling; the feature remains default-off.

## Open obligations

Source producer O remains unproved, including original contract/profile,
`beta`/`Slots(beta)`, Q-independent admission and the whole original joint
`(nu,K,D)`. Capture attachment A, provider/receiver realization, the
provisional Handler formal rule, soundness, principality, source adequacy and
production conformance also remain open. Frozen Oracle supplies no authority
for this placeholder.
