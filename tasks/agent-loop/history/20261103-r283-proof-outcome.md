# R283 Sol outcome — candidate invariant refuted

Sol's frozen handoff is
`tasks/agent-loop/inbox/extrusion-row-validity-r283.md`, SHA-256
`63e79d8e52243eccd6e83ddf4eef4c11d72e40e91a3f0fcea551e58084b72428`. Its Lean
module is
`notes/theory/lean/YulangClosure/OriginalExtrusionRowValidityR283.lean`, SHA-256
`31c83006c8d9b411b00d045fd16c9e5875e8a73d5baead989c7a55315f3a3f10`.

The pinned Lean 4.35.0 focused build, direct file check and bundled theorem/axiom
checker all exited 0. Ten declarations were kernel-checked; the complete types
and axiom lists are in the frozen inbox. The lists contain only standard
`propext` and `Quot.sound`; no `sorry`, `admit`, project axiom or checker bypass
was found. An early direct-check attempt exited 1 and was preserved with its
repairs in the inbox.

The candidate `RowsValid` is non-tautological and covers canonical
representatives, stored row references, term cells, memo keys/images, all eight
Work constructors in both queues, tuple ports, Parents and pending Parent
indices. It omits capture-incidence source validity. `captureGap` satisfies this
candidate invariant, but actual `step funded` publishes a pending Visit for
effect row 99 while the post-state has two effect rows. The same counterexample
refutes fuel-1 `runPrefix` preservation. Thus the exact universal preservation
claims for this candidate invariant are kernel-refuted. This does not prove that
no stronger constructor-derived invariant exists.

`Computed.rowInput caller` satisfies `RowsValid` without added assumptions, but
the counterexample means no preservation claim applies to its
`row_bound_produced` prefix. The first repair premise is validity of capture
incidence source rows consumed by `incomingJobs`, plus preservation of that
clause through capture/canonical-map mutation. A separate native/source bridge
must establish it for actual Rust storage. Other Work/result preservation cases
remain open. The original R70 W, Rust initialization, source/native
correspondence, Simple-sub A/B and original soundness remain open; Parent/A/B
stays 0->0 and implementation stays NO_SAFE_CODE_SLICE.

Sol identity `/root/sol_r283_extrusion_row_validity` froze writes and reported
no processes/descendants. First explicit clock sample: 2026-11-02 18:49:55 UTC;
STOP: 18:56:02 UTC; exact earlier start unavailable. Charge the full 1,800s
allocation. One initial capacity-only launch attempt failed before work and is
recorded separately at `20261103-r283-sol-launch-attempt-1.md`; retry 2 produced
this result. No renewal. Fresh independent review remains pending.
