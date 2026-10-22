# R311 — pinned generic `say` LocalSource formation

Status: RESULT, solo primary, unreviewed. R149 remains OPEN.
Baseline: `51f18e9b9`.
Contract: `tasks/agent-loop/sprints/r311-pinned-say-local-source-20261022.md`.

## Governing documents reread

Re-read the converted unified design §§4.1–4.5 and 9 stages 2/4, and the proof companion §§2.14–2.16 and 7.2–7.5. The carrier must preserve source occurrence and constructor premises; the proof plan does not equate carrier retention with generation or execution. Method selection stays delayed until the relevant bounds and stability condition are established. Tests are implementation evidence only.

## Triggering evidence

`cargo test -p yu-playground --lib` initially ran 40 tests: 39 passed and `pinned_public_export_route_retains_source_owned_edges_and_names` failed. A serial rerun reproduced the failure. The ordinary pinned `say` binding resolved to the expected provider binding, but its `local_source` lookup returned `None`. The exact carrier outcome was `Unsupported(SourceCarrierFailure { reason: UnsupportedForm, ... })`.

The pinned declaration has a generic formal, explicit unit result annotation, a `where 'a: Display` block and a body containing `out::write: value.show + "\n"`. The failure was at source formation, before candidate typing. R311 now associates the exact operator-use range with the parser-produced `HirOperator`, retains its imported declaration receipt and parse-owned operator `SourceNodeKey`, and forms the ordinary carrier while preserving the exact formal, result, where clause and operand occurrences. Preceding receiver `FieldTail` nodes are retained only for this exact supported chain shape; recovered or other operator-chain shapes still fail closed.

The new candidate-collection and runtime matches explicitly return unavailable for `InfixOperator`: source retention does not yet provide an authenticated operator value owner. No spelling-based lookup, typing, execution or sample closure is claimed. The pinned bundle and expected outputs remain unchanged.

## Result and checks

- `cargo test -p yu-playground --lib`: 40 passed, 0 failed, including `pinned_public_export_route_retains_source_owned_edges_and_names`.
- `cargo test -p yu-hir --lib`: 161 passed, 0 failed, including `pinned_generic_say_header_and_operator_body_form_a_source_carrier`.
- The focused unchanged Types and Console boundary tests remain passing with their expected fail-closed outcomes: `DeferredSelectionUnavailable` and the imported-name candidate boundary, respectively.

R311's source-carrier outcome is satisfied. The next implementation seam is an authenticated operator-use-to-value-owner bridge through candidate collection and runtime construction. Member use-local FreshUse/stable selection remains an independent open R310 seam. R149, source/native adequacy, A/B, principality, termination, independent review, unchanged sample execution and production remain OPEN.

R310 work remains separately recorded: exact Member candidate graphs capture receiver/result/effect rows and nested FieldTail, but no stable selection or per-use member FreshUse exists. Types still fails closed at `DeferredSelectionUnavailable`; Console is not complete.
