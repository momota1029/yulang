# Demand-root transport correspondence sprint closeout

Sprint `npair-demand-transport-correspondence-20261018`, rev1, closed
REVIEWED-PARTIAL. Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`
remains OPEN; original conditions closed 0.

## Proof result

The frozen constructor theorem received CLEAN independent proof/spec review.
Under its exact captured-bound, owned-input, postcanonical-root and ordered
Replay hypotheses, it relates one FreshUse's source demand to its copied root
and all four ordered Function ports, then to the Replay upper fiber. It supplies
a conditional local P3/P4 constructor fragment only. It does not establish the
fixture's source-to-Replay lineage or original fixed-c association.

Proof artifact SHA-256 `426b1bf969eb9628b73f5bcddec38b2f169d41341479dda4019965b34fad1244`;
handoff `f7101ac49c578f37f56c5d786900deaa3442f7b32fc6e86ff32accd584326e05`.
Proof review CLEAN; reviewer STOPPED.

## Implementation candidate and review

Frozen candidate artifact hashes:

- `candidate_scheme.rs`: `c1a5619633826ffd266b9dbe61c8a3b8d66b22fe708982c622d048ae457f1d30`
- `shadow_apply.rs`: `bbece5f6afd328df5829d507210cdcba7384bacf48603727a408bf674bcbdeef`
- `candidate_graph_call.rs`: `3b615f324e25d1a65fd8b4f886b6e882ec4551020ddf46242a479b65d3064b7f`
- `research_scoped_formal_replay.rs`: `0c813c194147fd1ef552a0047d9d80a91374261c004936adc320575352c1bf66`
- progress note: `10d7e60322aba054ff286dd664c670085b1eb430925ceef1adddb313d2493c3c`
- implementation handoff: `4e3c241bedbaf8beadb56466ece808014ffbdc37744fc569b958748f40473332`
- unchanged `candidate_context.rs`: `46f0b74c8aa942c629a456272c3ae601827f1794b25d7034479edee62bc13e4f`

Compiler review BLOCKING: the observer checks the original demand against one
retained FreshUse tuple/map, but does not carry or verify the selected Replay's
lower/upper relation IDs, BoundKeys, `Transport`/`Derived` ancestry, current
upper/root equality, or actual `FunctionPort` dependencies. A matching demand
tuple can be unrelated to the Replay row. MAJOR: `four_typed_function_ports_reject_every_pairwise_swap`
expects `[false;4]` after swapping two elements; only those two positions are
false. The focused `candidate_graph_call` filter omits this helper test.

No runtime was released. `git diff --check` passed. No Cargo/test/example command
ran. Raw `native_root_matches` remains unmodified. The candidate is unapproved
and does not close any theorem condition.

## Exact next work

Authenticate the actual chain from source demand and captured source snapshot,
through the correct retained FreshUse map and restored `Transport` witness,
through each allowed `Derived`/`Transport` root rewrite, to the selected Replay
upper and all four ordered `FunctionPort` dependencies. Reject matching but
unrelated relation metadata. Correct the pairwise swap expectation and add a
prescribed command that actually runs `authentic_demand_capture_tests`. Then
review exact bytes before one-shot runtime commands. Keep source semantics,
solver behavior, original quantifiers and fixed-c claim unchanged.

Conservative resource accounting: 1800/2400 seconds charged, 600 seconds unused
but expired without rollover. Astra0. All authors and reviewers STOPPED.
