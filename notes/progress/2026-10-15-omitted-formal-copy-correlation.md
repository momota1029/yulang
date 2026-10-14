# Omitted-formal copy correlation probe

Date: 2026-10-15
Branch: `research/simple-sub-intrusion`
Source baseline: `427d1ff5daab866fa7d89cb513a077063cc6454d`
Probe implementation baseline: `319d2766b5c7a0864101cb17a9973625e794e1db`
Status: test-only same-session source evidence; H1/H2/U remain open

## Scope

This bounded H1-C probe correlates authentic omitted-formal constructors with
retained Value extrusion parent/copy records for the source:

```yulang
my outer cb = { my inner x = cb x; inner }
```

The test is
[`omitted_formal_source_domains_correlate_with_retained_extrusion_pairs`](../../crates/yu-solver/src/candidate_context_tests.rs:489).
It runs inside one `InferenceSession`, follows each `FormalConstruction` to its
source Lambda and `HirParameterId`, checks the exact raw negative domain child
and parameter recipe, and compares those same-session `ValueRow` identities
with each retained `Parent.parent` / `Parent.copy`. It logs polarity, target
level, occurrence, comparison pair key and source-set identity. It also counts
retained `FunctionPort::Argument` dependencies and runs the existing bounded
formal/Argument incidence reader for any such child.

No effect profile, protection permission, receiver activity, residual
eligibility or semantic consumer was added. The probe is reversible test code;
it does not change production inference.

## Observed result

One passing focused run recorded the inner `x` formal domain as raw Value row 9
at initial level 2 and the outer `cb` domain as raw row 8 at initial level 1.
Their HIR Lambda/formal identities and the negative Function domain children
were checked against the source constructors in the same session.

The retained Value parent/copy pairs included:

| Parent → copy | Polarity | Target | Same-session formal-domain match | Comparison key |
|---|---|---:|---|---|
| `9 → 10` | Positive | 1 | inner `x` domain | lower `ValueRow(8)`, upper a `NegativeFunction` |
| `5 → 11` | Negative | 1 | none of the retained omitted-formal domains | lower `ValueRow(8)`, upper the same `NegativeFunction` key |

These row numbers describe one run and are not fixed test expectations. The
outer `cb` row was not the parent in the observed copy pair to level 1. Row 5's
source identity remains unknown; equality with neither omitted-formal domain
does not identify it as an application argument or any other source value.

The context dependency list retained zero `FunctionPort::Argument` edges for
this source session. Therefore the probe supplies no authentic Argument
consumer for these copy records. `Parent.comparison` retains a `TypedPairKey`,
while a context consumer has a `RelationId`; matching pair keys only produces
candidate occurrences and does not authenticate a unique contextual
comparison. The retained `Parent` also does not record the parent row's level at
copy time; the test's initial/retained levels are snapshots, not that missing
fact.

## Review and checks

A fresh `compiler_referee` found one minor claim-wording issue: equal pair keys
can belong to distinct relation IDs, so a pair-key match cannot identify the
copying comparison. The test now labels these as candidate occurrences and
records the unresolved relation/consumer correspondence. The primary reran
the exact focused test after this repair.

```sh
CARGO_BUILD_JOBS=2 timeout 300s cargo test -q -p yu-solver --features shadow-f5,shadow-apply-candidate --lib candidate_context::tests::omitted_formal_source_domains_correlate_with_retained_extrusion_pairs -- --exact --nocapture --test-threads=1
```

Result: 1 passed. `git diff --check -- crates/yu-solver/src/candidate_context_tests.rs` passed. No broad test suite, additional playground run, workspace build, timing sample or resource measurement was run. A separate primary playground run on the same source displayed four retained pairs but could not map its `raw5` ordinal to a `HirParameterId`; those IDs come from different spaces.

## Gate status

This distinguishes a copied inner-formal domain from the outer formal's
domain in one native session. It does not establish the origin of every copied
row or the missing Function Argument consumer. It is not evidence of source
rejection, effect-profile introduction, hygiene, Catch coverage, residual
subtraction, or the original U invariant.

The omitted-formal protection-position matrix remains undecided. Source profile
introduction at applicable typed positions and its connection to authentic
Argument incidence remain the first H1 gap. H1/H2/U stay OPEN; H3/P remains
disabled. Full Call, generic rigid opening, soundness, principality and
production/F5 cutover retain their separate gates.
