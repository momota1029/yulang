# Sprint EFFECT-PERMISSION-CANDIDATE-CALL-JOURNAL/20261030-r19

Status: ADMITTED, conditional research only
Branch / baseline: current yulang worktree; baseline input manifest copied from R18
Authority: ongoing inference/executor soundness goal; R18 selector recommendation
Contract revision: r1; primary approval in `current.json`

## Original outcome and success evidence

Original parent: inference/executor soundness and effect correctness remain OPEN
for the original supported source domain and accepted semantics. This sprint
does not narrow that domain or promote a candidate implementation.

Outcome: determine whether one ordinary selected candidate root schedule with
an outer tuple of collected scalar formal-annotation leaves and no top-level
effect annotation can reach its positive-tuple `intern_structure` call with an
active route mutation journal. The selected route is
`Session::execute -> execute_scc_plan -> execute_candidate_graph_plan ->
execute_candidate_source_root -> execute_candidate_action ->
candidate_formal_annotation -> candidate_formal_value_pair`.

Success evidence is a source-grounded transition trace from session creation
through the exact selected `Action::FormalAnnotation`, including every prefix
action and transitive journal writer, plus a checked Lean transcription that
derives the journal state rather than assuming it. Apply the result to exclude
or retain the active-journal premise of R18 `Conditions`. A five-attempt bound
without the two journal-growth events is allowed only if the source trace and
proof justify the exact same call and all remaining R18 premises.

Falsifiers: a selected prefix action begins or retains a journal; the claimed
ordinary schedule is unsupported; an intervening call can mutate journal state;
or the proof needs an assumed caller-state frame. In that case report the first
missing source edge and keep the R18 condition unresolved.

Known gates: native caller authenticity, allocator/capacity observations, other
callers, original parent, hygiene, consumers, principality, termination and
production remain OPEN. No compiler semantics or Rust implementation changes.

## Lanes and exact leases

Primary Luna/high, read-only source trace: write only
`tasks/agent-loop/inbox/effect-permission-candidate-call-journal-r19-source.md`.
Proof worker `lean_prover`, 600 seconds, writes only
`notes/theory/lean/YulangClosure/FormalPermissionCandidateCallJournal.lean`
and `tasks/agent-loop/inbox/effect-permission-candidate-call-journal-r19-proof.md`.
Fresh nonauthor `compiler_referee`, 250 seconds, read-only and returns its report
by message for the authenticated primary receipt. Primary owns current state,
audit, adjudication, outcome, Git and any status synchronization.

Frozen dependencies: R18 artifact
`f9bfd9ea556128b27e850b5ca66934d46fd86d73a77bdfdbb3846142ad37abd7`, R18 input
manifest `4a7f3a8e1e75ba0b761b7c927a7b6eaaf87b559df041a6d52915cd360ce63439`,
`candidate_source.rs` SHA-256
`96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`, and
`candidate_scheme.rs` SHA-256
`31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707`.

Verification: isolated project `/tmp/yulang-effect-permission-candidate-call-journal-20261030-r19/`;
Lean 4.35.0 only; at most two audits, each <=90 seconds and <=120 seconds
combined, with all changed and inherited root types and complete axiom reports.
No tests, Cargo, Rust execution, instrumentation, compiler edits, network or
Git operations by workers. One fresh independent compiler-referee review after
the primary freezes and authenticates the proof artifact and audit.

Sprint envelope: 1,200 active seconds total (primary 150, source trace 200,
proof 600, review 250); zero Astra, zero descendants; no background service.
Stop on falsifier, exact budget, user STOP, or session end. Unknown writers keep
their exact leases quarantined. Review acceptance requires no blocking/major
correctness finding, complete evidence authentication, and accurate conditional
limitations. A conditional local caller exclusion is not parent closure.

Primary source trace is complete before proof integration. The other lane does
not add a production implementation slice: all authorized work is source and
mathematical evidence for the unchanged parent goal.
