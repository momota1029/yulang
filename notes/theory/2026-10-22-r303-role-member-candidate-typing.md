# R303 — source-backed role member typing for the unchanged Types sample

Status: RUNNING, solo primary, unreviewed. Parent R149 unchanged Types+Console goal remains OPEN.
Baseline: `6afa11887`; contract: `tasks/agent-loop/sprints/r303-role-member-candidate-typing-20261022.md`.

## Governing design and proof material read

Re-read unified design §§4.3–4.5, 5.1, 6, 9–10 and proof companion §§3.1–3.6, 4.5, 7.1–7.5 for this iteration. The effect annotation rule remains the user's correction: contravariant `[io]` denotes `[io,'e]`, so passing `[state]` is not itself a violation.

## Starting evidence

R302 is checkpointed and pushed. FieldTail identity and its receiver/result Value+Effect rows survive Capture and one FreshUse map; authenticated role/member IDs attach to the deferred FieldTail; the unchanged Types receiver has an observed ordered `(int,str)` lower bound; source inventory has exactly one ordered-pair Display target among 14 implementations. These checks establish candidate-bound and source-inventory observations only.

HIR currently carries role and implementation declarations as nonshipping sidecars. Their member IDs preserve module and declaration `SourceNodeKey`, while role/impl bodies are retained as source snippets. Ordinary HIR items are only Binding, Expression and Error; source roots and candidate scheduling are built around actual definitions/expressions. The candidate FieldTail path therefore has authenticated IDs but no inference root for the original role/impl member body. Creating a fake top-level definition would break source ownership and is not an acceptable bridge.

## R303 target and falsifiers

Carry an original role/implementation member body into candidate inference with its authentic member ID, source node and module owner. Check that malformed/recovered or missing source fails closed, that same-spelled members from a different role cannot cross-route, and that target matching is delayed until receiver bounds settle. Preserve tuple element order and exact row identities. Advance the unchanged Types route through body inference; runtime execution is a stretch only if body formation, selection and typing have landed without weakening semantics.

The proof lane traces source constructors, source keys, new HIR/candidate roots, generated constraints, propagation and body consumer. The implementation and proof work are both solo and unreviewed. Passing tests, exact candidate inventories and selected source matches do not close the source/native theorem, Console, A/B, or production gates.

## Expected application

If the source-to-candidate bridge holds, apply it only to the original Types sample's `Display.a.say` prerequisite and ordered tuple `show` candidate, then continue toward ordinary execution. Keep Console and all original R149 quantifiers open. If the bridge cannot be represented without manufacturing a binding or losing source identity, preserve that as the exact obstruction and choose a different source-root representation before selection code.
