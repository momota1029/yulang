# R313 — source-owned Callee Return and Name argument

Baseline `2bcca0707`; original objective and unchanged R159 scope remain
fixed. R312 proved conditional allocation/capture/Force constructions but
did not authenticate actual source instruction ownership or actual Return.
Its executed Request fixture uses `NameConsumption::Execute`; the existing
Name carrier theorem requires `lexicalObserve = true`. Do not conflate modes.

Native lane: use an accepted source pipeline and same actual HIR/RuntimeProgram
to obtain an initialized Value-Name argument in Observe mode, with a callee
that can Request then return a Closure. Authenticate source owner/Apply and
Name occurrences, actual Apply/Name code and both operand labels, lexical
resolution/consumption, caller environment, saved Callee frame, real Return
value/view/provider, Delay code/environment/view and subsequent Name readout.
Capture actual Return immediately before Callee dispatch, not a fabricated
same-event record. Preserve the existing Execute fixture and explicitly
distinguish modes. No stubs or runtime semantic changes; reject foreign HIR,
swapped labels/owner/environment, early argument execution, fake Return,
different Delay/view and resumed-suffix replay. Exclusive files:
`tools/inference-playground/src/runtime/program.rs`,
`tools/inference-playground/src/runtime/machine.rs`,
`tasks/agent-loop/inbox/source-callee-witness-r313.md`,
`/tmp/yulang-r313-native`. Test-only observation, 1800s, locked offline.

Proof lane: reify the frozen actual source/instruction and Return evidence and
establish exact original occurrence, both label decodes and saved-frame
ownership; prove actual lexical Observe rather than asserting it. Instantiate
R312 `Preparation`, allocation/capture/readback, and the real R311/R293
consumers to the extent justified. Do not take the entire History, desired
carrier Meaning, source typing or resulting packet as an input, nor infer a
general semantics from one run. All-Reach world/license/observation/future,
callee membership, source-to-original-event correspondence, q_c/arms,
Checking and R159 admission remain independent until proved. Preserve
arbitrary source and every original alternative at the unchanged parent.
Exclusive `notes/theory/lean/YulangClosure/OriginalSourceCalleeWitnessR313.lean`,
`tasks/agent-loop/inbox/original-source-callee-witness-r313.md`,
`/tmp/yulang-r313-proof`; pinned Lean 4.35, all theorem types/axioms, 2700s.

Direct input SHA-256: program
`9c280992897b5664fef12e38df8161c4f1561a2d69654b1f5e1146339a3ca903`;
machine `caa627ce1829122a22034d83eecdb258a161410444a390d786d4e7a3a8ac281c`;
R312 history `c2e5aef86baa66304c6c575c67dd9b3cfb83f539f796e4832ffe6aa88c05dff8`;
R312 application `4bab607556ba9d0f89cb61db17ce8894fd87b9c0d14d44bc98437be9c03d4a26`.
One heavy checker at a time; independent source, Lean and parent-edge review.
No Git, child workers or production authority; primary integrates. Unknown
historical paths remain quarantined.
