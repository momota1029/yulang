# Amendment 01 — isolated Lean verification scratch

Sprint: `EFFECT-PERMISSION-NATIVE-DECODE/20261029-r3`  
Approved by Luna: 2026-10-29T11:12:41Z

This amendment adds one isolated generated-output location required to run the
already admitted focused Lean audit without writing to the shared Lean build
cache. The R3 outcome, source domain, approved semantics, two shared Lean
deliverables, assignment budgets, one-audit limit, and all stop conditions stay
unchanged.

The exact scratch project is
`/tmp/yulang-effect-permission-native-decode-20261029-r3/lean-project/`.
Luna creates it from the twelve `notes/theory/lean/` entries already pinned in
the R3 input manifest. The copy omits the existing `.lake` directory. Luna
records the copied files' exact byte counts and SHA-256 values in R3 primary
evidence. No dependency update, network access, default-target build, or shared
`.lake` write is authorized.

The `lean_prover` owns this scratch root while assigned. It may write the new
module copy, Lake-generated files under the scratch project's `.lake/`, and the
single audit's raw output/resource receipts under
`/tmp/yulang-effect-permission-native-decode-20261029-r3/lean-receipts/`.
The only shared source and handoff outputs remain those named by the R3
contract. Luna freezes the proof source, exact theorem list, copied-input
inventory, and exact command before issuing the one audit release of at most
90 seconds. Dependency compilation is included in that single invocation.
There is no retry or second Lean command after release.

The R3 Rust invocation allowance remains spent. This amendment grants no
compiler, semantic, parent-theorem, Git, or production authority; all parent,
source/native, effect-hygiene, consumer, unequal-transport, and production
gates remain OPEN.
