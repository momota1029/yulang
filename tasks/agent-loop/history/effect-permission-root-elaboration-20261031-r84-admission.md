# R84 admission — repair declaration elaboration for the existing R66 Root

Luna admits `EFFECT-PERMISSION-ROOT-ELABORATION/20261031-R84` under the
unchanged `research/simple-sub-intrusion` goal. This is a bounded proof
continuation, not semantic approval or production promotion.

- Contract: `tasks/agent-loop/sprints/effect-permission-root-elaboration-20261031-r84.md`.
- Input manifest: `tasks/agent-loop/sprints/effect-permission-root-elaboration-20261031-r84-inputs.json`.
- Baseline: branch `yulang3`, commit `a3f8b4a40e57b6053663e0de69b9ebdd3e0c6c49`.
- Frozen R83 repaired-prefix receipt: stdin 92,550 bytes, SHA-256
  `65d6e1c9ccd282bd905203da157135bd9eccf8f0cb1a22a55672c34b52caa302`;
  stdout 83,756 bytes, SHA-256
  `39b395b0a68dae8af921d6e2f93e652dfc48efe465283f88d5229177352bb3ae`;
  exit 1, no timeout. The independent closeout reviewer located the first
  invalid `simp [unique]` at R77 source line 223 and the same pattern in R81
  source lines 151, 155 and 159. The normalized declaration repair remains
  unproved and must be independently reviewed before any audit.
- All 20 pinned local module source byte lengths and SHA-256 values, plus the
  R83 proof handoff, authorization and outcome pins, were rechecked against the
  current checkout and matched.
- Proof lane: `/root/r83_proof` may write only the R84 candidate and proof
  handoff listed in the contract. Its bounded envelope is 1,600 seconds.
- Review lane: `/root/r83_review` is read-only, receives the frozen candidate,
  exact normalized declaration map and receipt set, and returns an independent
  verdict. Review budget is 1,000 seconds. Luna owns the durable review receipt.
- Primary envelope: 1,000 seconds, including 500 seconds for closeout. Total
  sprint envelope 3,600 seconds; Astra 0.
- Hard Lean ceiling: four separately authorized invocations, each at most 120
  seconds and 480 seconds total. Audit 2 is a single diagnostic-directed prefix
  repair; audit 4 is a single candidate repair only after accepted prefix and
  failed candidate audit. No identical retry and no fifth invocation.
- Rust remains read-only. The source/native extraction premise and original
  R66 parent remain open, so no safe in-scope Rust implementation change was
  identified for this packet.

The proof author, reviewer and primary may not expand the claims, source domain,
leases, runtime ceiling, memory limit or production authority. Each Lean call
requires its own exact-input authorization commit and push before invocation.
No theorem status changes without independent review and Luna adjudication.
