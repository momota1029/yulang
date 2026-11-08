# T17 defect 2: representable indentation stress depth

Status: resolved 2026-11-08 by the supervisor (a test-design fact, not a language decision): option 1 is adopted. 100,000 literal indentation levels need more than 4 GiB of source and cannot be represented by the 32-bit CST range.

The requested 100,000 *strictly increasing* indentation levels require at least
`100000 * 99999 / 2 = 4,999,950,000` indentation bytes, before statement text.
Tabs count as one column in the current parser, so they do not compress this.
Rowan uses a 32-bit `TextSize`; this input exceeds the representable CST range.

```yulang
say:
 say:
  say:
   x
```

Options, least additional work first:

1. Test 1,024 real indentation levels (already far beyond either build's stack
   budget), plus 100,000 levels of each compact recursive family. Recommended.
2. Add support for sources exceeding 4 GiB in a separate task, then exercise the
   literal 100,000-level indentation input with an explicit resource budget.
3. Replace this case with 100,000 nested braced statement blocks; retain real
   indentation tests immediately below and above the guard threshold.

Work on all other acceptance cases continues independently of this decision.
