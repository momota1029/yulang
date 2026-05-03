# Yulang Todo

This is a local working note. It is intentionally short-lived and should be
updated as the project direction changes.

## Current Direction

Yulang now has a public repository, a working playground, and examples that show
the language's main shape. The next goal is to make the language easier to try,
debug, and trust.

## Priority 1: Error Messages

Goal: when a playground visitor writes a broken program, the compiler should
point to the right place and say what went wrong in language-level terms.

- Parser errors should identify the unexpected token and nearby expected forms.
- Type errors should name the surface expression, not only internal variables.
- Role resolution failures should say which role/method was searched for.
- Method/field errors should distinguish missing field, missing method, and
  ambiguous role method.
- Effect errors should explain unhandled effects and handler mismatch.
- Runtime lowering errors should not leak "residual polymorphic runtime IR" to
  ordinary users without a higher-level explanation.
- Playground diagnostics should show line/column and a compact code frame.

Useful first tests:

- missing `else` / broken indentation
- unknown variable
- `1 + true`
- missing method such as `1.foo`
- unhandled `console::read()`
- bad handler arm payload
- polymorphic value that runtime cannot monomorphize

## Priority 2: Stabilize Examples

Goal: examples are the public contract while the language is experimental.

- Keep every playground example runnable from CLI.
- Mirror important examples into VM/source tests.
- Add one small example for each public-facing feature before expanding docs.
- Prefer short examples over one huge demo.
- Track examples that infer but do not run as bugs, not documentation caveats.

Current key examples:

- Tour
- Struct
- Optional Args
- References
- List Update
- Sub Return
- Nondet List
- Nondet Once
- Junction
- Types
- Effects

## Priority 3: Refactoring

Goal: reduce places where one change requires touching unrelated modules.

- Split diagnostic construction from inference/lowering logic.
- Keep playground sample data separate from DOM wiring if it grows again.
- Audit duplicate "export to core IR" helper code around ref projections.
- Keep monomorphization responsibilities separate from effect/thunk lowering.
- Move hot-path ad hoc rules behind named passes with clear inputs/outputs.

## Priority 4: Language Semantics Still Needing Work

Goal: finish semantics that are visible and likely to become examples/docs.

- Optional records:
  - default evaluation order
  - interaction with subtyping
  - runtime behavior for missing fields
  - error messages for bad patterns
- References:
  - nested projections such as `&xs[0].field`
  - string index update, if intended
  - clearer explanation of `$x` and `&x`
- Effects:
  - handler type examples
  - unhandled effect diagnostics
  - hygiene/id stack documentation
- Runtime:
  - remove remaining internal errors from user-facing paths
  - keep list/tree/string runtime behavior documented by tests

## Priority 5: Public Docs

Goal: make the repo understandable without reading implementation notes.

- README should stay short and point to playground, examples, overview.
- Overview should describe what works today, not future intent.
- Add a diagnostics page once error messages improve.
- Add a "known limitations" section that is honest but not discouraging.

## Suggested Next Step

Start with error messages. They are the highest leverage now because the
playground is public and more people are likely to try broken code than perfect
examples.

Concrete first task:

1. Collect 6-8 current bad diagnostics from small snippets.
2. Pick the most common/embarrassing one.
3. Add a regression test for the intended diagnostic.
4. Improve only that diagnostic path.
5. Repeat until the main playground failure modes are acceptable.
