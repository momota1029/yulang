# R81 admission — repair existing Incidence proof

Admitted by Luna after R80 closeout and independent review. Baseline is `661b40348a712120f921cc4dbcbbbce2e467821e` == `origin/yulang3` at admission. Contract SHA-256: `33e8f586a6c033af19050d5855c2976058a102c400a4105807097639f199bff4`. Input manifest SHA-256: `b70d608d22e0544c9171462bf704a7142f2ee113cecb2c54783b08c1a860ec87`.

R80 is closed with both exact Lean audits failed and no accepted R66 Incidence theorem. Its Rust candidate passed only bounded static review. R81 fixes the first proof gate only; no Rust edit or execution/build lane is admitted. R80’s failed evidence and candidate remain frozen and pinned.

Exact authority: registered constructive proof owner may write only `notes/theory/lean/YulangClosure/ConstructedSourceIncidenceR81.lean` and `tasks/agent-loop/inbox/effect-permission-incidence-repair-r81-proof.md`, within 1,200 seconds. Luna may authorize no more than two exact-input in-memory Lean audits, each <=120 seconds and <=240 combined, with a separate pushed authorization before each. Fresh independent reviewer may read and report only; review budget 600 seconds. Luna owns remaining 600 seconds including closeout, state synchronization, explicit-path commit and push.

No assumptions, semantic changes, input weakening, environment/worktree/build/cache/target/scratch or Cargo/tests/Lake/compiler. Preserve all 32 pending records, UNKNOWN observations and quarantined paths. Audit2 failure or changed target closes the packet without theorem acceptance.
