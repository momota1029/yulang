# PROVIDER-SOURCE-SOLUTION-REALIZATION-20261027/r1 — amendment 01

Status: Luna-admitted immutable delta, 2026-10-27. Parent, semantics, total
budget and exact proof/source leases remain those of the pinned r1 contract.

## Frozen source-lane result

Source handoff:
`tasks/agent-loop/inbox/provider-source-solution-20261027-source.md`,
SHA-256 `af5a24838d5ce9a58a077a8f4e31b9deefd8e656096e3d757a82a906d2ed0f3a`.

Adapter:
`tools/inline-authentic-extraction/src/bin/original_provider_reify.rs`,
SHA-256 `5ed03633e8a37775847d7c28fc08d2d7acc98965299e0dbe27568b266fd2b8ed`.

Trace status: **ABSENT**. The executable did not reach provider parsing/lowering
and emitted no HIR trace or schema. Do not hand-author or imply an executed
trace. The adapter compilation failures are implementation failures, not
semantic counterexamples. Source writes stopped; both Cargo processes exited.

Both authorized attempts are spent: Cargo 2/2. No retry, direct-binary
workaround, changed fixture/parser admission, or new Cargo command is permitted
in this sprint.

| Receipt | SHA-256 |
| --- | --- |
| source owner pin list | `fc823e39493dfaeb266b1aab2c516963bfe31c2dce6783a7e71de4b2d16cb728` |
| attempt 1 metadata | `0f0ce9dddb0f47a3ddfd86d2a9da089daa50106ef1df2cc46c8e166f6878e290` |
| attempt 1 stdout | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| attempt 1 stderr | `65b8709849b20941ffd0eb01244bbb69a70b7fb8419855c72ec7e7510f1dcb95` |
| attempt 1 status | `39b8dc3fc8b44765c8e6f1adee04c5b465e555ab791cc42d0d9e810d5b64297c` |
| attempt 2 metadata | `0f0ce9dddb0f47a3ddfd86d2a9da089daa50106ef1df2cc46c8e166f6878e290` |
| attempt 2 stdout | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| attempt 2 stderr | `060ae6e9ba89952f4041dc275a8890d522261c30cbd4719727f2022027f3b951` |
| attempt 2 status | `39b8dc3fc8b44765c8e6f1adee04c5b465e555ab791cc42d0d9e810d5b64297c` |

The 38 r1 dependency pins independently rehash unchanged. The source handoff
records both failures before provider execution: attempt 1 failed on adapter
module visibility, error conversion and borrow/type mismatches; attempt 2
failed on `SourceText.as_ref()` inference and a borrow/move conflict. Full
receipts remain in `/tmp/yulang-provider-source-solution-20261027/source/`.

## Proof gate amendment

Replace the r1 proof-side scheduling condition “Lean after the source trace is
frozen” with:

> Lean may start after the source result (including a truthful no-trace
> failure report) is frozen, its hash is acknowledged by Luna, and every Cargo
> process/write in that lane is stopped. If no trace exists, the proof must not
> import, fabricate, or assume one; it proceeds from the unchanged pinned
> original Source definitions and labels Rust owner authentication as unproved.

The existing proof worker `/root/provider_source_proof` retains its same exact
three-file lease and the same remaining allowance: **0/8 Lean calls and 0/600
seconds used before this grant; at most 8 calls / 600 seconds total**, each
process 1 CPU / 1 GiB / 180 seconds. No budget resets. The last Lean call stays
reserved for all delivered theorem types and complete per-theorem axiom audits.

The sole verification slot is clear: both Cargo attempts terminated and the
source worker gave a write-cessation receipt. Luna grants the existing proof
worker the next verification interval. No replacement worker, path lease,
resource or reviewer is added. Do not assume provider judgment preservation in
the candidate graph; the same-graph proof remains the central target. Useful
checked source-constructor algebra must appear in theorem conclusions and
state its missing semantic inputs. Generic map overwrite alone is insufficient.

Reviewer timing is unchanged: fresh review starts after the proof handoff and
proof outputs freeze. It must distinguish checked source algebra, explicit
semantic assumptions, unexecuted Rust provenance, absent trace and actual
fixed-map/provider-judgment construction. Full import-root elaboration and all
parent gates remain OPEN.
