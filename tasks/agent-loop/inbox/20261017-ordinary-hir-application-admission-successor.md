# Frozen handoff: ordinary-hir-application-admission-successor

Sprint: `ordinary-hir-choice-a-contract-20261017`, contract revision 4.
Contract SHA-256: `88f9674294f001e33bc9c29803d329f2d76c1059c21bbd9362c35ab1d84d7f93`.
Assignment/handoff: `ordinary-hir-application-admission-successor`, revision 1.
Design artifact: `notes/design/2026-10-17-ordinary-hir-application-admission-successor.md`.
Design SHA-256: `a1bf05f113c3b870cf15045f398c6d1d243ea65db80e746fa2951aac37135d70`.
Source audit: `notes/theory/2026-10-17-choice-a-call-cst-source-key-audit.md`,
SHA-256 `e8a320be0e78ecc2c5ee5210338476740c03a1fae61fb2747ec39636286ad501`;
handoff SHA-256 `68d43689a506a7c22152ecbe90d49c55b83390489541837956b34f397e9ce88a`.
Source baseline: `0c0fda3974d1db2c91256667f93c46effa18c8d0`; latest contract
checkpoint: `1a7560e9de6d4df8e037cdd8cf9e04254f4f7576`.

Parent: original Yulang inference/execution goal, original quantifiers and all
source/native obligations preserved. Original theorem conditions closed: 0.
HIR-APP-CST-1: candidate discharge pending the combined fresh independent
review/adjudication. HIR-APP-ADMISSION-1: OPEN; concrete direction-A proposal
awaiting fresh reviews and explicit final user approval.

Role/author: Luna primary `/root`, current-session. Requested Luna/high;
observed model/effort UNKNOWN. Exact output leases: the design artifact and this
handoff only. No descendants. Writer STOP after freezing these bytes.

Outcome class: successor-design proposal, not adopted. The general grammar is
recursive over associated `MlArgument`/`CallTail` with Atom and comma-free Group
forms; unsupported/recovery-bearing subtrees refuse atomically. Ordinary Apply
retains structural operands without Call typing; opt-in local-source placeholders
remain separate. Error, identity, allocation, source-key, consumer and resource
contracts plus exact supersessions and future regressions are in the artifact.

Source to compiler boundary: fixed literal bytes -> pinned raw scanner/header/
declaration/association constructors -> source-branded CST keys -> current
ordinary lowerer rejects both application bodies with `UnsupportedExpression`.
The proposal would retain the associated Apply tree and suppress only the
structural admission error for its grammar. It does not establish generated
constraints, propagation, solver consumer, source T, Call typing, soundness,
principality, termination or production behavior.

Frozen source audit is a candidate AST/source correspondence result; all 48
manifest pins match on the current checkout. Candidate derivation uses ordinary
Rust/combinator/Rowan/ASCII-library contracts, not runtime tree observations.
Its parser/recovery coverage is limited to the fixed unfenced single-line ASCII
literal and explicitly named branches. The combined compiler review must
adjudicate it before Luna marks HIR-APP-CST-1 discharged.

Review target for sequence: this design + source audit + their exact pinned
dependencies, frozen together, fresh spec auditor then compiler referee then
architect. The design author does not self-review. Resolve blocking/major
findings by versioned repair and delta review. Only after that, ask the user to
approve this exact contract and its named supersessions. No compiler/test lease
is authorized before that answer.

Checks: `python3 tools/agent_sprint.py check` passed after artifact freeze;
`git diff --check` passed before freeze. No tests, builds, compiler/runtime
probes or Cargo were run. No implementation behavior was executed. The three
inherited UNKNOWN leases remain quarantined.

Mutual TODOs: compiler reviewer checks the 48-pin source derivation, key/range
claims, Apply consumer split and resource/failure behavior; spec reviewer checks
that only the named clauses are superseded and semantic/theorem quantifiers
remain unchanged; architect checks API/error/identity integration and whether
the proposed finite resource model permits atomic publication. Final user
approval remains a separate TODO after all review findings close.

Budget: Astra source audit conservatively charged its full 480s reservation;
selector/coordination charged 240s. Luna's design lane conservatively charges
its full 420s reservation because exact active seconds were not instrumented;
remaining Luna budget is 0. Review budget remains 300s, coordination 240s
charged, reserve 60s. Sprint total cap remains 1500s. No code/test authority or
unconsumed worker lease is created by this handoff.
