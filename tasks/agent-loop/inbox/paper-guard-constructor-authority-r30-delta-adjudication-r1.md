# R31 delta-review adjudication — R30 constructor authority

Disposition: **findings sustained; repaired source report queued for a separate fresh review**.

The fresh M1 review found two artifact-level MAJORs: the initial data-cycle examples lacked roll-typed node derivations, and the polymorphism discussion lacked a concrete finite heap with node typing and a repeated graph reference. The findings were valid. No implementation defect or semantic change was established.

The primary report was revised at `tasks/agent-loop/inbox/paper-guard-constructor-authority-r30.md` and frozen as `tasks/agent-loop/history/paper-guard-constructor-authority-r30-primary-r2.md`. It now gives finite heap maps, location types, constructor/roll derivations, and explicit cycle paths for candidate recursive data cases; these derivations remain conditional because the cited manuscript fragment does not state general recursive-type formation. Unsupported typed instances are labeled unestablished. The polymorphic case is a concrete two-node heap with `Xi(r)=Bool`, `Xi(s)=∀β.Bool`, node derivations, and the freshness side condition. No omitted guard rule is filled in.

A separate fresh M1 review-only packet is admitted to verify those corrections. It has its own 150 active-second reviewer grant and no transfer from the consumed R31 grant. R30/R31 do not close the paper guard, `wrap`, full graph extension, typed observation, source/native, A/B, or production gates. Eight UNKNOWN reservations remain quarantined. No checker, test, Lean, build, runtime, or semantic work was performed.
