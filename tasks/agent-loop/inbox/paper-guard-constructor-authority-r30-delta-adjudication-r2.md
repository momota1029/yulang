# R32 delta-review adjudication — R30 constructor authority

Disposition: **the two R31 MAJOR findings are closed in substance; R32's three minor report-accuracy findings are sustained and repaired**.

The M1 found that recursive unfolding was written as `T[T/α]` instead of `F[T/α]` for `T=μ α.F`; the nominal row mixed up the constructor payload template and result template; and the continuation row incorrectly suggested the typing rule was absent. These are source-report accuracy defects, not semantic or implementation findings.

The primary report now names `F` separately for each recursive type and derives the data introduction at `F[T/α]=T` before explicit `roll`. The nominal declaration now has result template `D⟨α⟩` and one payload template `α`, with both formation premises conditional. The continuation row cites the actual introduction rule and leaves finite-heap admission and guard classification unestablished. No `μ` formation rule, wrap edge rule, or continuation guard rule is invented.

The exact corrected report is frozen at `tasks/agent-loop/history/paper-guard-constructor-authority-r30-primary-r3.md`. All manuscript guard, graph, typed observation, source/native, A/B and production parents remain OPEN. Eight UNKNOWN reservations remain quarantined. R32's M1 grant is fully charged because cumulative active time is UNKNOWN. A new review, if selected, requires its own bounded packet and grant.
