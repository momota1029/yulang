# R26 mapOperation transport repair — primary adjudication

Sprint/contract: `FULL-PAPER-TYPE-SUBSTITUTION-20261026/r26`, r6, SHA-256 `b133b2c1ddca59847013e8da58a3a8eca13ed088d4c61c98f762558387928954`. Baseline `036e97ef905a50bcd6a5257709ee8f6d1228ff1e`. Primary continuation commit `e10b0755e641f3b65220cb4316a21066546a8c92`; worker handoff commit/state `0c11dd55377623dc116e4f3155567e0cb2fc9f79`.

## Result

**R26 FAILED_CHECK at primary verification.** The worker's mapped `mapOperation` candidate passed its focused Integration build and 13-theorem audit. The primary's repeated focused build also passed. The subsequent primary audit command was explicitly capped at 2.8 seconds and exited 124 (timeout). The contract stops at the first failed check; no retry, repair, extra checker, independent review, or proof integration was performed.

Worker: `/root/r26_mapoperation`, registered `lean_prover`; observed model/effort UNKNOWN; no children. Worker used 4/6 Lake invocations and 26.569420685 checker seconds (worker full 180-second active allowance conservatively charged). Actual worker receipt: writes STOPPED, no active process or descendants.

Primary verification: two invocations; focused build PASS in 0.53 seconds; audit timed out at 2.80 seconds, exit 124. Primary checker time 3.33 seconds; no remaining check was attempted. Full log: `tasks/agent-loop/inbox/paper-typing-subst-r26-primary-verification.txt`, SHA-256 `8e1d545ec10419e2b21c3a2e8014b05d0ce0396d108851378328010cbe07ee15`.

Frozen worker artifacts in `/tmp/yulang-r26-mapop`: source `PaperExecutionTypingSubstitution.lean` SHA-256 `83a8f005bf49e3394feebb0b13466e525e6c607d3fc46ac72f1efadce2c8f5bb`; audit `R26Audit.lean` SHA-256 `4bef8fc3c8df7a38a66eab1d7d4448239159722a208adb0e8e51396f50c00c1f`; worker log SHA-256 `c13b8d60a7a95199a7d267706bcc595e3abf8ced7fc5e81fa964bb2aaa61d38f`; handoff r1 SHA-256 `6a5bd7930780190b75bfec965914830ed50dbac55273b21889084245ad8b26c9`. Dedicated cache manifest remained unchanged at SHA-256 `3a8180fa9bfe3c3197bcc78901fdc86ba57885a634ae6e96509e32ae64ff2c94`. The candidate remains isolated and unpromoted.

## Scope retained

No theorem is adjudicated from the worker log because primary verification did not complete. R24 remains an accepted separate mapper prerequisite; R25 remains FAILED_CHECK; R23/R18, full mapOperation/substitution, inference/executor, original A/B, and source/native/Rust obligations remain OPEN. No production or implementation authority follows.

All R26 writing and checking is stopped. The next action is a dispatcher decision at this failed-check boundary.
