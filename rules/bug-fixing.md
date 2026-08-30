# Root-cause bug fixing

## Diagnose before changing code

Before a fix, answer:

1. Why does the behavior occur, at the causal level rather than the visible symptom?
2. Which responsibility and layer should own the rule?
3. What sibling cases can arise from the same cause?
4. Is the proposed edit at the causal owner or at a convenient downstream observer?
5. Does one general rule repair all inputs with the same structure?

If the cause cannot yet be explained, continue bounded diagnosis or escalate to architecture; do not write a plausible patch.

## Forbidden repair shapes

Do not:

- reject only the known failing input with an `if`;
- hide the case behind early return or fallback;
- rewrite a computed result downstream to match expected output;
- add an exception for one caller, module, symbol name, fixture, or test;
- repair inference/normalization/formatting when the cause is parser, lowering, resolution, scope, symbol-table, or constraint generation;
- leave an invalid intermediate representation and compensate at output;
- add fresh variables, blocking/protection machinery, or local state without a governing invariant.

## Good repair shape

A good fix has a one-sentence root cause, lives at the owning responsibility, repairs sibling cases automatically, and can be described as a language/IR/constraint invariant. The regression test demonstrates the general cause as well as the reported example.

The first question in review is: **does this repair the cause or only the observed symptom?**

## Temporary downstream workaround

A symptom-side workaround is allowed only when all are true:

- the correct owner-side repair is materially outside the approved scope;
- the workaround is explicitly marked temporary;
- the cause and intended owner-side repair are recorded;
- the effect is narrowly bounded;
- a task/design record tracks removal.

A passing reproduction after a workaround is not completion of the original defect.

## Scope discipline

One repair corresponds to one cause. Do not mix unrelated refactoring, naming, formatting, abstraction, or cleanup. If required cleanup is independent, make it a separate coherent change and commit.

Do not blanket-stash or reset an in-progress tree to inspect base behavior. Existing changes may already contain hang or regression fixes; use a separate worktree or narrow comparison.

## Review closure

A bug fix normally requires:

- direct reproduction before/after where practical;
- a generalized regression or sibling case;
- independent root-cause review;
- relevant focused checks;
- explicit remaining uncertainty.
