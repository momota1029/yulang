# R288 — Carry pinned fmt role and impl declarations through HIR

Status: solo continuation under the unchanged Y2 sample goal; no subagents by user instruction.
Baseline: `69704582a57db3b73517a2fab7e385b2864deba2`.

## Outcome

Use the already pinned, blob-checked `std::core::fmt` ParsedFile and its exact ModuleIdentity. Lower that real source through the ordinary local-source HIR path, then verify its `Display` role members and tuple implementation body retain exact source ranges, order, and parent-qualified IDs. This tests the R286/R287 carrier against the actual source required by Types.

## Limits and falsifiers

No import linking, semantic role selection, type/member validation, constraints, runtime, or theorem closure is implied. Fail if HIR lowering rejects the exact module, an expected declaration/member/where entry is absent or reordered, any retained range differs from original bytes, or IDs lose their exact module/declaration owner.

## Exact paths and checks

`tools/inference-playground/src/lib.rs`; this contract; R288 outcome note; `tasks/agent-loop/current.json`. Run the focused playground test, ordinary HIR check, `python3 tools/agent_sprint.py check`, and `git diff --check`. Solo-authored, unreviewed.
