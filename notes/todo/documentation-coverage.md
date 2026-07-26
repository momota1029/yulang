# Documentation Coverage TODO

Date: 2026-07-26

## Baseline

This is a working inventory of documentation coverage. Its current state is
established from the [Standard Library Catalogue](../../web/docs/reference/std/index.md)
and the reference pages linked from it, rather than from the original
implementation-first audit.

- Every non-aggregator standard-library module in the catalogue now has either
  a fuller reference destination or an explicit provisional entry. The site
  covers `std::time`, `std::testing`, the bytes/character/config/path text
  modules, the Boolean/numeric modules (including `frac`), and Yumark.
- `std::text::config` and `std::text::yumark` have fuller pages marked
  **Provisional**. `std::io::net` is catalogued as **Provisional** but has no
  fuller page; provisional means its spelling and API are not part of the
  stable surface and programs should not depend on them.
- The language reference now covers the parser DSL and CLI, plus OR, alias,
  symbol, and polyvariant patterns; guards, arm-set labels, and `elsif`;
  special lambda forms; tuple structs, enum record payloads, and structural
  projections; string format specifications; module and import grammar;
  the value restriction; and `core::cmp`, `core::convert`, `core::fmt`, and
  `core::seq`.
- The site deliberately describes three audit assumptions differently:
  pattern type annotations are ignored rather than checked, a `case` or
  `catch` label names its whole arm set rather than one arm, and only `enum`
  variants (not `error` variants) support record payloads.
- Writing these pages surfaced implementation defects. They were left alone:
  this note tracks documentation coverage, not implementation repair.

## Work items

There is no active coverage page to add at present.

The catalogue still labels the following aggregator modules **Not documented**:
`std`, `std::control`, `std::data`, `std::io`, and `std::text`. That label
means they have no separate fuller reference page. Their catalogue entries
already state their grouping and re-export roles and point readers to the child
module pages, so they are adequately covered as aggregators and are not work
items. Reassess only if an aggregator acquires behavior beyond grouping,
declaring children, or re-exporting names.

## Deliberate or not-ready gaps

These items are not work items until their stated condition changes. They
remain here so that their absence is explicit.

- Host acts and suspension tiers are deliberately unexposed.
- `std::io::net` is catalogued as **Provisional**, not omitted. Do not add a
  fuller page while its spelling and API remain unstable.
- Parser extensions remain deferred until parser diagnostics stabilize.
- The parser accepts some type annotation forms that the checker rejects:
  explicit `for 'a:`, record type annotations, and polyvariant annotations.
  They are parser-only syntax, not user-facing type-system coverage.

## Follow-up

- Recheck the catalogue and its linked pages when a standard-library module or
  an aggregator changes. A **Not documented** aggregator is not automatically
  a missing page; first decide whether its catalogue entry remains sufficient.
- Keep provisional and deliberate omissions explicit here or in a successor
  note. Promote a provisional module to a stable fuller page only when its
  surface is ready to promise.
