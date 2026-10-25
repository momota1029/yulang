# R57 outcome — exact audit harness elaboration failure

R57 on `yulang3` is FAILED at the strict audit call. The corrected root import was in the leading import block; default root `lake build` passed. The unchanged candidate SHA-256 is `0a1834040a0201c0c472f66138f6501094f7138dd3614f2bc4439a8be0cda1c8`.

Call 4 failed while elaborating the reused exact-name audit harness: missing `OfNat MessageData 0`, `OfNat MessageData 34`, `BEq MessageData`, and `HAdd MessageData Nat MessageData`. The exact source is preserved with SHA-256 `3056fded75008665f893c26bf6485cdd2672e1e14683631a813ad10bc3102cb7`. The 34 declaration audit did not complete. This is a primary audit-template failure, not a theorem counterexample. Per contract, no retry, independent review, candidate integration, or theorem acceptance occurred.

Four calls total; first three passed, root build took 48.880379530 seconds, audit took 1.740203162 seconds; total checker time 50.620582692 seconds and primary elapsed 129.762883870 seconds. Full raw outputs, exact argv/cwd/timings and hashes are frozen in `/tmp/yulang-r57-yulang3-type-beta-audit/notes/theory/lean/.lake/` and summarized in `tasks/agent-loop/inbox/paper-type-beta-r57-yulang3-primary.md`. Type-beta, source/native realization, full executor, inference A/B and production remain OPEN. External proof arrivals must be preserved and separately audited.
