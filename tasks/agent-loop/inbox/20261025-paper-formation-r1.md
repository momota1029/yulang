# FULL-PAPER-TYPE-SUBSTITUTION-20261025/r2-formation — primary handoff

Contract: `tasks/agent-loop/sprints/paper-type-substitution-20261025-r2-formation.md`, SHA-256 `4b016518cd8c17974ef1892d79adaa9dabf9aed6df8d3af935d40d9cf7b3d26d`.
Parent: paper typing-substitution lemma (`docs/yulang-operational-type-safety-ja.tex:957–977`) and `thm:safety` (`:1140`). Original inference A/B and executor safety remain OPEN.
Baseline: `e8f133657b98d47d789a52fa64aee8f102393452`.
Outcome class: partial conditional Lean proof, primary-authored, NOT independently reviewed. No child/reviewer/implementation agent ran. Eight prior UNKNOWN reservations remain unchanged and quarantined.

## Frozen artifact and dependencies

- `notes/theory/lean/YulangClosure/PaperTypeFormation.lean`: SHA-256 `e090a4674fcdac27dc73b50b8a0f32c65618c81d1ccd350648319ecfb4a1f454`.
- Frozen r1 substitution module SHA-256 `a2faf4dc7765724cd033fd1014b0acb0e87c58902ac71ede157d2e268ba7ad83`.
- Paper SHA-256 `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`.
- Frozen r1 handoff SHA-256 `00e8f1b2f3df7e9c66f94eb3c5fa7f0d1e33d666848a6530e60ce047a34d41e3`.

## Checked result

The module defines scope-indexed formation for variables, base/top/bottom,
unions/intersections, tuple and argument sequences, records, variants, nominal
argument sequences, `mu`, thunk, callable and `forall`. Tuple/argument sequence
tails must have the corresponding sequence shape. Record and variant labels are
unique. Record presence is represented explicitly as `required | optional` and
mapped bijectively to r1's legacy two tags; this is only an encoding, with no
claim that paper fields have mutability semantics.

`formed_mapVars` and `formed_subst` prove that scoped formation is preserved by
scope-respecting renaming and simultaneous capture-avoiding substitution,
including under `mu` and `forall`. Operation declarations carry one identity,
arity, payload template and response template. A realized instance computes
both payload and response from the same argument list and substitution;
`operation_instantiation_preserves_formation` proves both resulting types are
formed, and `perform_operation_formations_from_declaration` derives those types
from an instance tied to a declaration in the declaration list.

Checker receipt: `cd notes/theory/lean && lake env lean -j1 -M1024 YulangClosure/PaperTypeFormation.lean`, exit 0. The standalone module is not imported into `YulangClosure.lean`; no full `lake build`, Rust/native check, or axiom audit was run for r2.

## Exact remaining gaps

This is not the success predicate in full. In particular, no theorem yet shows
that declaration-derived operation instantiation is preserved when an existing
instance, declaration and arguments all undergo an ambient substitution. The
module defines the lifted declaration substitution and proves lift-index helper
facts, but does not connect them with an instantiation-commutation theorem.
Nominal type identity/declared arity is also not indexed by a nominal declaration
environment in `Formed`; nominal nodes currently require only a formed argument
sequence. These gaps must be closed before applying this result to the complete
paper typing-substitution induction.

No original typing, inference, executor, source/native or A/B parent closes.
No production authority follows. The independent reviewer remains unassigned
because eight UNKNOWN reservations exceed capacity; self-review is not a gate.
The r2 active-work cap was 300 seconds; the exact elapsed runtime is UNKNOWN and
the primary stopped at the budget boundary. No commit or push occurred.
