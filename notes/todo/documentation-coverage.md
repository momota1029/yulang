# Documentation Coverage TODO

Date: 2026-07-26

## Baseline

The coverage audit started from the implementation, then compared that inventory with `web/docs/**`.
It did not derive the inventory from the reference pages.

- The standard library has 40 modules: 16 are documented usably, 5 are named only in passing, and 19 have no module path anywhere on the site.
- The work is roughly 14 to 18 page-equivalents: 7 to 9 new pages and extensions to the existing reference pages.
- A site page can pass every per-page writing and mechanical check while the feature it ought to teach is absent from the whole site.

The absent standard-library paths are `time`, `testing`, `io::net`, `text::bytes`, `text::char`, `text::config`, `text::yumark`, `num`, `num::frac`, `float`, `core::cmp`, `core::convert`, `core::fmt`, `core::seq`, and the aggregator modules.
`io::net` remains in this measured bucket, but its literal spelling is deliberately not a documentation gap; see [Deliberate or not-ready gaps](#deliberate-or-not-ready-gaps).

Each target below names the English page.
The corresponding Japanese page belongs to the same item.

## New pages

### Standard-library catalogue — `web/docs/reference/std/index.md`

- Document the aggregator modules and show how the standard-library module groups fit together.

### Time — `web/docs/reference/std/time.md`

- Document `time`.

### Testing — `web/docs/reference/std/testing.md`

- Document `testing`.

### Text modules — `web/docs/reference/std/text.md`

- Document `text::bytes`, `text::char`, `text::config`, and `text::yumark` together as the text-module family.

### Numeric modules — `web/docs/reference/std/num.md`

- Document `num` and `num::frac`.

### Floating point — `web/docs/reference/std/float.md`

- Document `float`.

### Parser DSL — `web/docs/reference/parser-dsl.md`

- The existing documentation shows only the entry point.
- Add capture semantics, quantifiers, alternation, rest capture, and lazy capture.

### CLI reference — `web/docs/reference/cli.md`

- Document `build`, `test`, `parse`, `install std`, `realm freeze`, and the remaining CLI flags.

## Extensions to existing pages

### Patterns — `web/docs/reference/patterns.md`

- Add OR patterns, `as` aliases in patterns, type patterns, symbol patterns, and polyvariant patterns.

### Control flow — `web/docs/reference/control-flow.md`

- Add `case` and `catch` guards, arm labels, and `elsif`.

### Functions — `web/docs/reference/functions.md`

- Add the special lambda forms `\sub`, `\case`, and `\catch`.

### Structs — `web/docs/reference/structs.md`

- Add tuple structs and enum and error variants with record payloads.
- Add tuple projection `.()` and record projection `.{}`.

### Strings — `web/docs/reference/strings.md`

- Add the string-format grammar: width, precision, alignment, alternate form, and debug form.

### Modules — `web/docs/reference/modules.md`

- Add `mod` declarations and test modules.
- Add the import grammar: group imports, globs, aliases, `without`, versions, realms, and bands.

### Types — `web/docs/reference/types.md`

- Add the value restriction and its generalization rules: syntactic values generalize, computed right-hand sides do not, recursive function SCCs are allowed, and computed cycles are rejected.

### Core standard-library modules — `web/docs/reference/std/core.md`

- Add `core::cmp`, `core::convert`, `core::fmt`, and `core::seq`.

## Deliberate or not-ready gaps

These items are not work items until their stated condition changes.
They remain here so that their absence is explicit.

- Host acts and suspension tiers are deliberately unexposed.
- The `io::net` spelling is deliberately unexposed; do not add it only to make the module-path count complete.
- Parser extensions remain deferred until parser diagnostics stabilize.
- The parser accepts some type annotation forms that the checker rejects: explicit `for 'a:`, record type annotations, and polyvariant annotations.
  They are parser-only syntax, not user-facing type-system coverage.

## Follow-up

- Re-run the implementation-first inventory when a documentation item closes.
- Keep a deliberate omission in this note or a successor note with its reason; do not leave it implicit.
