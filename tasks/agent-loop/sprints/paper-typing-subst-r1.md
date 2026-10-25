# Paper execution typing substitution — r1

Status: active, primary-only constructive proof sprint.

## Parent goal and theorem

Continue the unchanged goal: complete Lean proofs for Yulang type inference and
executor semantics, treating the paper/specification as primary and Rust as a
secondary correspondence. Immediate parent is `docs/yulang-operational-type-
safety-ja.tex:953–977`, item 2: one simultaneous type substitution on
declaration instances, environments, plans, payload/response types and result
preserves syntactic execution typing. The downstream parent is `thm:safety`
at line 1140. This sprint does not close item 1 term substitution, item 3 name
renaming, source-to-plan generation, native correspondence or the original
inference A/B claims.

## Frozen inputs

Branch `research/simple-sub-intrusion`, baseline
`7e003e05ac4173258e92fc328a8193b1ffa86e37`.

- Paper `docs/yulang-operational-type-safety-ja.tex`:
  `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`
- `PaperTypeSubstitution.lean`:
  `a2faf4dc7765724cd033fd1014b0acb0e87c58902ac71ede157d2e268ba7ad83`
- `PaperTypeFormation.lean`:
  `e090a4674fcdac27dc73b50b8a0f32c65618c81d1ccd350648319ecfb4a1f454`
- r5 `DeclSubst.lean`:
  `f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258`

Recheck the actual bytes before construction. The paper rules and rule-to-Lean
coverage map in the handoff govern; restricted `CoreSyntax`/`ControlTyping`
modules are useful only where their exact constructors correspond.

## Stages and success evidence

1. Encode the full paper raw value/computation, handler/plan, continuation,
   declaration/code-table, graph/context objects and mutually dependent
   syntactic typing judgments. Freeze a constructor-to-paper-rule coverage map.
2. Define simultaneous type substitution on every type-bearing object,
   including declarations, operation instances, environments, plans, graph
   types and metadata. Use the existing de Bruijn lifting algebra under `mu`,
   `forall`, and rigid polymorphic arms. Prove lookup and binder-commutation
   support lemmas. Apply r5 to operation premises.
3. Prove the type-substitution theorem by induction on the actual mutually
   defined derivations. Compile the complete modules and inspect theorem axioms.
   If full closure does not fit this envelope, freeze the exact first omitted
   rule, the failed induction case and its dependency; keep the theorem OPEN.

Success requires every constructor/rule listed in the handoff, including all
administrative forms, to be represented and covered. An assumed preservation
field, arbitrary primitive signature, weakened handler instance, lost
environment identity, or omitted typing constructor falsifies the result.

## Work ownership and resources

Luna primary only. Eight prior UNKNOWN reservations remain quarantined. No
child, Astra, reviewer, Rust/Cargo or native process is admitted. The
implementation lane remains `NO_SAFE_CODE_SLICE`; existing runtime publication
and lexical-recursion owners have a separate native correspondence obstruction.

Envelope: at most 900 additional aggregate primary seconds and 120 cumulative
serial Lean checker seconds; preserve prior charges. At most six serial Lean
calls. Stop on the bound, a changed dependency/lease, or an exact semantic
obstruction. Any successful result is a candidate until fresh nonauthor review
of the frozen full rule coverage and proof.

Exact outputs:

- `notes/theory/lean/YulangClosure/PaperTyping.lean`
- `notes/theory/lean/YulangClosure/PaperTypingSubstitution.lean`
- `tasks/agent-loop/inbox/paper-typing-subst.md`
- this contract
- primary-owned `tasks/agent-loop/current.json`
- checker receipts `/tmp/yulang-paper-typing-subst-r1-check.log` and
  `/tmp/yulang-paper-typing-subst-r1.olean`

Next boundary: a complete frozen proof, a paper/representation obstruction,
lease or dependency change, or this envelope's end.
