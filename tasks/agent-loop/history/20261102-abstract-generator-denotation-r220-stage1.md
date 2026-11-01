# R220 stage 1 — structural leaf and original-source interface

Status: **candidate structural result; original source interface still OPEN**.
This is an intermediate receipt inside active sprint R220, not sprint closure.

## Parent and accounting

The unchanged parent is `YulangClosure.SourceProblem.InferenceSoundness` at
`Contracts.lean:128–130`. It retains all original source quantifiers, scope,
assignment and one shared witness. Current parent-premise delta is **0**;
roots remain **0/4**, packages **0/5**, effect-hygiene theorem delta **0**.

## Frozen lane evidence

- Constructive handoff: `tasks/agent-loop/inbox/abstract-generator-denotation-r220-proof.md`, SHA-256 `e5201bd86bde686aed220c3fc0f91f58b83c2d7868400d752a3e4da8ececd930`.
- Independent falsifier: `tasks/agent-loop/inbox/abstract-generator-denotation-r220-falsifier.md`, SHA-256 `e237662bb869f982cdb069a08ffe97ee91e9940d9740b6532bfbcbf8fa2c0b35`.
- Both authors froze their only paths and stopped writes; no build, cache, Lean theorem, tests, Cargo, runtime experiment, or Git mutation occurred in either lane.

The precise fragment uses two Value clauses, `atom(code l) ≤ var(q)` and
`var(q) ≤ atom(code l)`, and the one-sided Effect clause
`var(e) ≤ bottom`. Under the pinned regular graph interpretation, the Value
pair forces the referenced node to have exactly the requested atom shape/code;
it does not force reference-index equality. The upper Effect bound forces the
referenced Effect node to bottom. The opposite `bottom ≤ var(e)` by itself
does not constrain it. Neither conclusion is yet an original source readout.

## Exact open parent premise

The store/reference semantics has no `OriginalSource.Endpoint`,
`SourceAssignment`, descriptor, value, root or event equation. In particular,
no admitted definition maps the literal's synthesis coordinate to the
generated Value/Effect references and then constructs the L1 row and Return
at the original `(q,r,e₀,ξ,ω)`. `SourceAssignment.row` currently reads
`finalRoot`; source generation distinguishes `synthesis`, `finalRoot` and
`writtenTarget`. L1 fixes the original row and pure Return but expressly does
not supply this Simple-sub embedding. `LiteralAtom` still consumes its
declaration and ground facts from a supplied kernel.

This is missing model evidence, not a counterexample to L1 or soundness. The
next admitted proof step is to kernel-check the structural fragment theorem
and, in the same review, test whether the actual source embedding follows
from the frozen definitions without adding a premise. If it does not, retain
this exact owner equation as the blocker; do not infer source correspondence
from the structural theorem.

## Runtime receipts

Both lane handoffs record the pinned dependency hashes, inspected definitions,
budgets and stopped-write status. The independent falsifier also records a
dispatch-only contract-hash typo; the on-disk contract and current-state hash
were correct and all semantic dependency hashes matched. No artifact or source
dependency changed as a result.
