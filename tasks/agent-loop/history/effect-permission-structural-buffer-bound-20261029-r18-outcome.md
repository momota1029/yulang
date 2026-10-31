# R18 outcome: structural tuple buffer bound

Status: **CLOSED_COMPLETE_CONDITIONAL** under the unchanged inference/executor soundness goal. This closes the local conditional trace packet, not a native counterexample, parent theorem or production gate.

## Delivered result

`YulangClosure.FormalPermissionStructuralBufferBound` reuses the R17 physical six-slot `Option` buffer and the R16 ordered intern protocol. Under one `Conditions i` record, it derives the exact six intern events and their occupied buffer layout. A structural-owner event appended after successful intern reaches `assertionFailure 6 6`, before a normal wrapper return or drain. `no_normal_seven_pushes` states that the computed seven-attempt suffix has no normal bounded `Appends` execution.

The four public roots are `intern_events_exact`, `intern_length`, `conditional_seventh_assertion`, and `no_normal_seven_pushes`. Their fully printed types remain in the authenticated raw audit stdout. The first two use `propext`; the latter two use `propext` and `Quot.sound`.

Artifact SHA-256: `f9bfd9ea556128b27e850b5ca66934d46fd86d73a77bdfdbb3846142ad37abd7`. Proof handoff SHA-256: `09792fb4ea8870145021e95d47faf1325f3554b98e3a49c24751c4033c06f4ed`. Source handoff SHA-256: `2deb722afa72c76aeb09e5768de9803123ca1178e991c52e488f14e5ac8cd62c`.

Primary audit: pinned Lean 4.35.0, all 77 ordered roots (73 inherited R12/R13/R15/R16/R17 roots plus 4 R18 roots), 77 unique BEGIN/END/PASS records, complete printed theorem types and axiom reports, exit 0, empty stderr, 16.793 seconds, maximum RSS 1,016,240 KiB. The roots use only `propext`, `Classical.choice`, and `Quot.sound`. The R18 module built with no new warnings; existing warnings in inherited dependencies remain. Input authentication found zero missing/mismatched entries among 197 manifest items and matched all 261 project-copy entries. Full raw output and receipts remain under `/tmp/yulang-effect-permission-structural-buffer-bound-20261029-r18/attempt-1/`; the evidence record links their hashes and per-root axiom inventories.

Fresh independent compiler-referee review: **CONDITIONAL**, with no blocking, major or minor correctness defect. The reviewer inspected the frozen source/artifact and primary audit evidence read-only. It confirmed the exact event order, the assertion-before-write boundary, the physical six occupied slots and the separation between a local conditional trace and actual Rust reachability. The reviewer specifically checked that each reserve premise combines successful result and observed capacity change; neither successful allocation nor reserve-result fields authenticate native execution. `internInput` hardcodes R16's irrelevant `childrenValid`/`cacheHit` fields, but R16's `protocol` ignores these fields and R18 separately retains tuple child validity and cache miss as conditions. Review was returned by message; no review file was written or claimed. Reviewer writes and processes stopped.

## Remaining gates

The local trace requires a nonempty positive tuple with valid collected children, empty event entry, cache miss, active journal, page-needed state, successful structural reserve, five successful intern/page reserves each with an actual capacity inequality, successful page allocation and claim, and successful inner intern. These are supplied observations in the Lean model. The proof does not authenticate that one real `candidate_formal_value_pair` call has the same arena/cache/journal and all five simultaneous growths, nor that its allocator and page claim succeed. A source invariant excluding that conjunction is also not established.

Thus R18 identifies an obstruction candidate, not an authenticated Rust panic. Full caller reachability, primitive allocation/reserve/snapshot authenticity, source/native correspondence, the original parent, effect hygiene, consumer residual, soundness, principality, termination and production remain **OPEN**. The panic-before-drain case is distinct from normal `Result::Err`; no repair or semantic change is authorized by this result.

No tests, Cargo, Rust execution, instrumentation, source edits, Git staging/commit/push or dependency changes were performed. Existing quarantines and deferred Git disposition remain in force.

## Next evidence seam

The next packet should authenticate the missing same-call candidate route and primitive outcomes, or prove a precise source invariant that excludes their conjunction. It must keep all current premises and original source scope visible, and leave native and parent claims OPEN until that bridge exists.
