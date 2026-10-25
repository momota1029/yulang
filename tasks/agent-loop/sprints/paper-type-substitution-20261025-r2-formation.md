# FULL-PAPER-TYPE-SUBSTITUTION-20261025/r2-formation

Status: Luna-authorized, primary-only research continuation. The r1 artifact and
handoff remain frozen and unreviewed. Eight pre-existing UNKNOWN assignments
remain quarantined; no worker, reviewer, Astra, implementation lane, or lease is
started or released.

## Original goal and parent application

The unchanged goal is complete Lean proofs of Yulang type inference and executor
semantics, with the paper/specification as semantic authority and source/native
correspondence and original Simple-sub A/B quantifiers intact. This packet moves
the substitution premise of the paper typing lemma at
`docs/yulang-operational-type-safety-ja.tex:957–977` toward `thm:safety`
(`:1140`). It does not close inference, executor preservation, source/native, or
any A/B obligation.

## Fixed outcome

In a new standalone Lean module, define paper-faithful type and sequence
formation, explicit required/optional record presence, and operation declaration
instantiation where identity, argument arity, payload, and response come from
one declaration and one shared type substitution. Prove formation and
instantiation preservation under capture-avoiding substitution and apply the
result to the paper's `perform` payload/response premise. Keep r1 unchanged.

Required falsifiers: required/optional collapse; malformed sequence tails form;
wrong arity or undeclared identity instantiates; payload and response use
different arguments; substitution captures declaration parameters.

## Exact leases and frozen dependencies

Primary `/root` only, all outputs frozen at handoff:

- `notes/theory/lean/YulangClosure/PaperTypeFormation.lean`
- `tasks/agent-loop/inbox/20261025-paper-formation-r1.md`
- this contract
- Luna-owned `tasks/agent-loop/current.json`

No root import, README, generated file, production Rust, tests/expectations,
configuration, manifest, question, or other shared artifact is leased.

Frozen direct dependencies: r1 substitution module SHA-256
`a2faf4dc7765724cd033fd1014b0acb0e87c58902ac71ede157d2e268ba7ad83`, paper
SHA-256 `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`,
r1 handoff SHA-256 `00e8f1b2f3df7e9c66f94eb3c5fa7f0d1e33d666848a6530e60ce047a34d41e3`,
and baseline `e8f133657b98d47d789a52fa64aee8f102393452`.

## Resources and review

At most 300 additional primary active-work seconds, at most 12 serial Lean
checker calls and 120 cumulative checker seconds. The prior r1 primary receipt
records 161 active seconds against its 600-second cap; this grant does not reset
that expenditure. Stop earlier if remaining session/resource capacity is lower.
No Cargo/native work. Runtime owners `runtime/program.rs` and
`runtime/machine.rs` remain `NO_SAFE_CODE_SLICE` pending their separate
cell/capture/replay relation.

The outcome is primary-authored and cannot self-review. Freeze r1 and r2 together
for fresh nonauthor review when capacity permits. Until then, both remain
unreviewed research; no theorem or production gate is promoted. Consult again at
a material obstruction, dependency/lease/resource change, integration seam, or
sprint end.
