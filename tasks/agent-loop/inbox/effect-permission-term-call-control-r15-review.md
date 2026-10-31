# R15 independent review — PASS, conditional proof-repair scope

Sprint: `EFFECT-PERMISSION-TERM-CALL-CONTROL/20261029-r15`.
Reviewer: `/root/effect_permission_term_call_control_r15_review`, fresh nonauthor `compiler_referee`; 250-second cap. The reviewer returned this handoff inline because its higher-priority role instruction prohibited file writes. Primary Luna persisted the message after writes stopped. No descendants.

## Verdict

**PASS for the R15 proof-only repair, conditional research scope.** No BLOCKING, major or minor findings.

Independent inspection started from the contract, archived/current Lean files, definitions and dependencies before consulting the producer handoff. The only artifact delta against archived R14 is the proof body of `control_test_fields` at lines 229–240. The declaration, quantifiers, hypotheses, definitions, imports and every other module byte are unchanged. Applying `loop_test_fields` before reducing the drained-state instrumentation projection addresses the exact failed proof obligation. Both accounting branches retain the same statement.

The reviewer inspected Rust `with_term_events` (`crates/yu-solver/src/lib.rs:10594`), its sampler (`lib.rs:10804`), event draining (`term.rs:955`), relevant callers and existing event/failure tests. Constructor-then-drain order, first sample failure precedence, suffix termination, and production/test instrumentation separation agree with the stated model boundary. Empty events, either constructor outcome, and either accounting flag introduce no repair-specific gap.

## Authenticated snapshot

| Input | SHA-256 |
| --- | --- |
| R15 contract | `eff6b4718b194b07e807db84872926565448b4baa86ae2fd02d3b052fcfcfc50` |
| R15 source handoff | `7500b0fe883f354387ed9298e2f7aa5b125bb8b89256769b5da3f9f9bb64a7ed` |
| R15 proof handoff | `1526bc3f0e426f3f08401a5190b494d6097d784599fbe8dc0ad61b305354f634` |
| Archived R14 artifact | `fde5e86c3540646b778856dda985b51db201a20ab7a38ca3e34485257c2dbfdc` |
| R15 artifact | `73bface0963c65eb76933ff8116594b161e78f1733b66e6be25cc174d1eb2dd7` |
| R15 input manifest | `a57e78421e678f86c7c8aa225bb48970930a2984eb2198f5d5f0630482a30f96` |
| Audit plan | `0abc9f90133b334351092d2f3f8c54993af8f63a6f47254759a5c26cad9f6e87` |
| Aggregate audit receipt | `02eca0b48d30dd438a696cab015975bdcc89cc997e6e41df1108b453cb28378b` |
| Project copy receipt | `d75bd8f4846c94a73975165a42b783a49728e50d20ec889de396a7c30bea3e3d` |
| Raw stdout | `3d5e511301e821af6a1c6a79f19f0ed515315fa341466e6d555ba5849b1a5eeb` |
| Raw stderr | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| Raw status | `9a271f2a916b0b6ee6cecb2426f0b3206ef074578be55d9bc94f6f3fe3ab86aa` |
| Resource receipt | `d3b7481dc5ee0f54b7e0be93348805c67356303d24cd87149e12237a67d6d498` |

All 168 manifest entries authenticate. All 17 project copies, Lean/Lake/checker files and binaries match the frozen plan. The raw output contains 38 ordered, unique BEGIN/END/PASS roots exactly matching the plan: R12 nine, R13 ten and R14 nineteen. All printed types and complete transitive axiom lists were inspected. Axiom inventory: 14 roots with no axioms, 21 using only `propext`, and three using `propext`, `Classical.choice`, `Quot.sound`. No `sorryAx`, project axioms or checker bypass appeared in the dependency search.

Authenticated tool result: Lean 4.35.0, exit 0, 17.235 seconds, maximum RSS 990096 KiB. The reviewer ran no Lean, Lake, checker, Cargo or tests.

## Limits retained

- Constructor/event generation, sampler counter states and availability remain explicit inputs; actual Rust execution/state correspondence remains unproved.
- `testFields` preservation models production instrumentation identities; `cfg(test)` instrumentation execution is excluded.
- `exact_tree_r9_from_term_control` still requires row-length agreement, `Aligned`, `Reservations` and `SourceCalls`, and covers the selected fixed tree.
- Primitive/alias authenticity, native publication, complete source/consumer correspondence, original parent preservation, effect hygiene, soundness, principality, progress and termination remain OPEN. This review grants no production promotion.

Reviewer writes stopped; no descendants or descendant leases.
