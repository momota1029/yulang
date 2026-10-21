# R281 — evidence for escaped quotes in unchanged Yulang2 strings

Status: checkpointed parser evidence, provisional and unreviewed.

## Exact source and obstruction

At baseline `39de8f156`, the exact pinned `lib/std/core/fmt.yu` has two syntax diagnostics: `Missing/StringEscape` at byte 5800 and a root `ErrorGroup` at 5801..5813. Both point to the unchanged escaped-quote strings on source line 202. The escape parser detects a quote after the backslash as a close sentinel before simple-escape scanning, leaving the rest of the expression outside the StringLiteral. Existing tests also pin recovery for a backslash followed by a lone quote without a later close.

## Required distinction

A complete backslash-quote-quote sequence has a simple quote target and a subsequent closing delimiter. A backslash-quote sequence with no following quote preserves the current sentinel recovery. R281 tests this distinction without modifying pinned bytes.

## Parent application

Removing these parser errors can allow exact fmt syntax publication, but it does not prove StringLiteral runtime value, HIR semantics, role selection, unchanged Types/Console output, source/native correspondence or R149 theorem closure. The converted unified design and proof companion remain governing. `[io]` in a contravariant position remains open `[io,'e]`.

The focused escape/sentinel tests, all 38 literal tests, all 12 string-literal recovery tests, exact pinned fmt census and playground check pass. The unchanged pinned fmt module now parses with zero syntax diagnostics. This establishes parser acceptance only; R149 HIR correspondence, role resolution, Types/Console output, source/native correspondence and theorem closure remain OPEN.
