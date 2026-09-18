# First HIR slice: operator-chain association

Status: Authoritative

Scope: the first `yu-hir` slice required by Gate 3 of
`2026-09-17-syntax-freeze-and-vertical-implementation-amendment.md`. It defines
the association-phase input/output and the minimal HIR product for one accepted
fixture. It does not define the module graph, stable `DefId`s, name resolution,
type/effect representation, solver, or core IR.

Approved-by: user
Approved-at: 2026-09-18
Drafted-by: primary agent
Reviewed-by: architect (independent review and delta review, 2026-09-18)
Supersedes: none

## Authority and current state

- `docs/yulang3-architecture.md` (Authoritative) fixes the phase model
  (`Resolve / Lower: ParsedFile + semantic imported interface -> HirModule`,
  phase table) and gives `yu-hir` ownership of "source file, module, stable
  `DefId`, resolved name, HIR". Its dependency graph is
  `yu-syntax -> yu-hir -> yu-types`, so `yu-hir` is expected to depend on
  `yu-types`.
- `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` (Authoritative),
  "Association phase contract", fixes this phase:

  ```text
  ParsedFile + exact OperatorAssociationEnvironment
      -> associate_operator_chains
      -> HirModule containing precedence-shaped applications
      -> type inference / solving
  ```

  The same section states: "association owner は `yu-hir` の syntax-to-HIR
  lowering、または `yu-hir` が唯一呼ぶ dedicated pre-HIR module とする"
  (L4807); "prefix / infix / suffix 全 role を一つの association authority で
  扱う。infix だけを後段化しない" (L4823); and "BindingPower は type ではなく
  declared syntax fact なので、type inference が association を選ぶ余地はない"
  (L4841-4843). Together these mean `yu-syntax` and the solver hold no second
  association authority.
- `crates/yu-hir` and `crates/yu-types` are empty boundaries. There is no
  concrete HIR node schema or `HirModule` shape in `notes/` or `docs/`.
- Gate 2 is implemented: `ParsedFile` retains the exact effective
  `Arc<OperatorTable>` the parser used and exposes `operators()`.

## Why this is the bounded first slice

The full `HirModule` (module graph, `DefId`s, name resolution, declarations) is
a large durable decision. Gate 3 asks for the smallest accepted fixture that
exercises source -> Rowan CST -> HIR so implementation can expose missing
design. The association contract is the one piece with an already Authoritative,
bounded, testable specification.

The slice is a whole-CST walk, not a declaration lowering: it visits every
`OperatorChain` in the Rowan tree and associates it. Declaration structure,
names and types stay unlowered, so the slice needs no `DefId` model and does not
guess the eventual `HirModule` shape. This mirrors the Gate 1 shadow walk: a
total structural pass with source provenance.

## Decisions required before implementation

- **D1 crate boundary.** The architecture graph is `yu-syntax -> yu-hir ->
  yu-types`.
  - D1a: add `yu-syntax` as a `yu-hir` dependency now and leave `yu-types` for
    the next slice.
  - D1b: add both `yu-syntax` and `yu-types` now, even though association
    produces no types yet.
  - D1c: place the associator in a temporary module outside `yu-hir` until the
    `yu-hir` public surface is designed.
- **D2 first public product.**
  - D2a: introduce `HirModule` immediately as the phase product, initially
    holding only the associated chains.
  - D2b: introduce a narrower pre-HIR product (e.g. `AssociatedChains`) and
    defer `HirModule` until declarations and names exist. The contract's
    "dedicated pre-HIR module that `yu-hir` alone calls" (L4807) permits this.
- **D3 associated expression representation.**
  - D3a: a recursive owned tree (`HirExpr::Apply { operator, operands, range }`)
    with source ranges.
  - D3b: an arena/indexed representation with stable node ids.
  The contract requires a deterministic precedence-shaped tree with provenance,
  not ids.
- **D4 operator environment and fixture.** The fixture must declare its own
  operators: `ParsedFile::operators()` is built only from the imported
  `SyntaxEnvironment` plus local header declarations, and there is no builtin or
  prelude operator seeding in `yu-syntax`, so `std`-importing stable-core
  fixtures have an empty effective table and an undeclared `+` becomes generic
  recovery, not infix association.
  - D4a: `tests/contracts/phase2-parser/v0/cases/header-operator-order-plus-then-star/main.yu`
    (3 lines: `infix (<+>) 40 41 = left`, `infix (<*>) 60 61 = right`,
    `my value = a <+> b <*> c`). Declares two infix operators with different
    binding powers and exercises a non-trivial association.
  - D4b: `tests/contracts/phase2-parser/v0/cases/infix-operator-header/main.yu`
    (2 lines) declares one infix operator but the body has no operator use.
  - D4c: a one-line `1` fixture. A bare expression statement is still a root
    `OperatorChain`, so it exercises the walk but no dynamic operator.
  - D4d: vendoring an external std prelude is out of scope for this slice.

## Proposed default for review

D1a, D2b, D3a, and D4a.

Rationale: keep the first durable public surface small and reversible, avoid
guessing the eventual `HirModule` shape, and exercise dynamic infix association
with a real tree (`a <+> (b <*> c)`) using only a fixture's own header
declarations.

## Observable contract for the slice

Taken from the association contract (L4822-4839) and restated for this slice:

- the same flat item sequence and association environment deterministically
  produce the same tree;
- prefix, infix and suffix are all handled by one association authority; infix
  is not deferred to a later phase;
- call / index / field / projection / path and `MlArgument` are reserved
  structural postfix handled at the current cursor before dynamic comparison;
- `TypeAnnotationTail` reduces every pending dynamic segment before the
  annotation and uses the result as the next continuation's left seed; a
  terminal outer tail applies to the same reduced left and ends the chain;
- nested `MlArgument` chains are associated first and applied left in source
  order (`f x y` becomes `(f x) y`), without writing that nesting back into the
  CST;
- the `OperatorUse` source range is passed directly to the associated
  application and HIR provenance; ranges are never recovered by a later CST
  search;
- a `MissingOperand` or operand-position `Error` maps to one typed error
  expression, consumes every item and yields a total result;
- recovery-noise `Error` stays in source order and provenance but is not
  double-operandized with a following retry operand;
- parser-issued recovery diagnostics are not reissued; no duplicate syntax
  diagnostic is produced from the same malformed source;
- an operator entry that cannot be resolved in the exact environment is not
  disguised as an unknown operator; a revision/key mismatch is a compiler
  invariant failure and an existing syntax recovery item becomes an error
  expression;
- the association result is never written back into the CST; no green-tree or
  surface-AST parent/child relation is mutated;
- `NullfixOperatorUse` is a `Value` operand (surface-grammar role at
  L4579-4589) and participates in association like any other operand.

### Nested-chain composition

Structural-postfix children (`MlArgument`, call/index elements, parenthesized
elements, and other accepted nested positions) can themselves contain an
`OperatorChain`. The rule for this slice: associate each nested chain before its
enclosing chain consumes it as an operand, and associate every chain exactly
once. The walk is therefore recursive, not a flat single pass.

## Walk scope

The walk visits every `OperatorChain` in the CST, including chains inside
conditions, case/catch scrutinees and guards, for-iterables, pattern record
defaults, call/index arguments and parenthesized elements, not only statement
bodies. Declaration structure is traversed but not lowered.

## Out of scope

Declarations, patterns, types, effects, name resolution, `DefId`s, module graph,
constraint collection, solver, diagnostic publication, an external std prelude,
and any CST or `syntax-v0` change.

## Rollback / stop conditions

Return to design, naming the concrete counterexample, if any of these occurs:

- the association environment cannot be derived from `ParsedFile` alone (for
  example a fixture's operators require a prelude or module graph that does not
  exist in-workspace);
- an encountered `OperatorChain` shape is not covered by the contract above
  (unspecified structural tail, unspecified nested position);
- association cannot be exercised meaningfully without a declaration, name or
  `DefId` model;
- implementing association would force a `yu-syntax` CST or `ParsedFile` change;
- association defects do not converge after the normal round limit.

## Approved decisions

The user approved the proposed default on 2026-09-18:

- **D1a** — add `yu-syntax` as a `yu-hir` dependency now; leave `yu-types` for
  the next slice.
- **D2b** — introduce a narrower pre-HIR product (for example `AssociatedChains`)
  and defer `HirModule` until declarations and names exist.
- **D3a** — a recursive owned expression tree with source ranges.
- **D4a** — `tests/contracts/phase2-parser/v0/cases/header-operator-order-plus-then-star/main.yu`.

The slice stops at association: it produces no type and does not touch
`yu-types`. The question of how a type attaches to an associated expression is
captured in `2026-09-18-hir-type-attachment-open-questions.md` and is not
decided here.
