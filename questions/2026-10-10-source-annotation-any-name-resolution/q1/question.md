# Question: resolve the written type name `Any`

Question ID: `source-annotation-any-name-resolution`
Question revision: `q1`
Predecessor/history: `questions/2026-10-10-source-annotation-typed-root-bridge/q1/d1` (approved source-owned detailed-design scope)
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): `2434abf06` (current branch); `95b27279b` (scoped resolution-owner audit); `1c185235c` (Any-root construction attempt)
Task/thread locator: current conversation; no stable external thread identifier is available
Governing source/section: approved annotation bridge q1/d1; `notes/theory/2026-10-10-source-owned-annotation-any-design.md` §§2–4; `notes/progress/2026-10-10-source-annotation-any-resolution-owner-audit.md` §§1–4

## Requested scoped decision

For the selected one-case source annotation `my widened = 0 as Any`, choose how the written Type identifier `Any` resolves. Current selected Yulang3 sources retain the syntax but provide no scoped written-Type resolver or Any builtin/prelude registration. Ordinary HIR lowering rejects this annotation wrapper before solver collection. The approved design authorizes detailed design only; it does not select a name-resolution policy or authorize implementation.

This question decides only the written-name introduction/lookup rule for this occurrence. It does not choose the semantic Value(Any) relation, construct its complete ordinary root or Top law, change annotation boundary behavior, or authorize compiler implementation, production routing or F5 cutover.

## Background and current premises

- The approved annotation answer selects source-owned expression annotation formation with conditional Direct consumption, including a detailed-design case for ordinary Any. It explicitly leaves type-name resolution and implementation open.
- `crates/yu-syntax/src/expression/tails/type_annotation.rs` retains one full Type subtree. HIR associates the annotation with its completed operand, but `ResolvedExpr` has no annotation variant and `lower_simple_chain` rejects the wrapper before typed collection.
- The inspected selected current rules define Value(Any)/Top consumers only when an actual typed ordinary root and law are supplied. They do not resolve an identifier spelling to that root.
- The frozen legacy resolver had no `Any` builtin arm; ordinary declarations/imports/aliases could resolve that spelling, while an unbound spelling failed. That is historical correspondence, not current authority.
- The user's broader priority is that practical type inference works. No exact wording in the current conversation selects reserved-builtin versus ordinary scoped-name behavior for this annotation.

## Options and consequences

1. **Introduce `Any` as a built-in Type name.** The Type resolver recognizes the spelling without a declaration/import, and source declarations cannot shadow it. This makes the one-case example self-contained, but adds an observable Type-namespace rule and commits to builtin precedence.

2. **Resolve `Any` only as an ordinary scoped type name.** The name must resolve through an actual declaration or import whose completed contract is Value(Any); an unbound spelling remains unresolved. This reuses ordinary namespace ownership but does not make the example self-contained until a real Any declaration/import and root producer exist.

3. **Choose another bounded rule explicitly.** State its lookup precedence and whether declarations/imports may shadow or provide `Any`.

No option supplies the complete Value(Any) root, membership guards/evidence, hereditary Top law, Direct proof or runtime behavior. Those remain separate obligations under the approved detailed-design scope.

## Affected work

Blocked scope: completing written-Type resolution for the selected `0 as Any` design and any dependent root-construction design that assumes a resolution result. Independent complete-Call work and other inference gates continue; the pending Call-Reify q1/q2 are separate questions.

Required answer: select Option 1, Option 2, or another bounded rule, with explicit shadowing/lookup behavior. No implementation or cutover authority follows from the answer.

Pending publication: keep this entire question directory unstaged and uncommitted until the questioning primary discovers and validates an explicitly approved local answer and commits the matching bundle. The answering primary never mutates Git. Posting does not pause the goal; dependent work waits while independent work continues.
