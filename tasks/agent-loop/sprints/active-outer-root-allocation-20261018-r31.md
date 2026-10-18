# Sprint R31 — active outer-root allocation under adopted Generalize rules

Status: ACTIVE; bounded research only; no new source law or production behavior.
Branch / baseline: `research/simple-sub-intrusion` / `4bf67d9113e877b7cc3c3a35c5982c233f971fdc`.
Parent goal: complete Yulang type inference and executor with proofs. This sprint targets the necessary source-allocation bridge for intrusion preservation, required principality and N-Transport; it does not close `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` or change that theorem's scope.

## Fixed outcome

For the approved single local-recursion behavior, let a nested nonrecursive helper `g` be formed while its enclosing recursive `f` initializer remains active. Determine from the already adopted registration, source Call, parent-copy intrusion and Source Generalize rules whether the **complete demand coordinate `C` generated through the active open `f` root**, together with its corresponding equality clause, is shared across independent `g` description frames or allocated per frame.

Try a constructor-directed derivation over the actual source rule telescope and all complete clauses. Independently test the concrete shared-`C` and frame-local-`C_i` allocations against every adopted source rule, original scope and event identity. Success evidence is either (a) a complete derivation selecting one placement, or (b) a complete pair of lawful rule interpretations with a precise nondeterminacy witness. If neither can be established, freeze the first missing judgment/owner and why each alternative fails. Merely repeating that the rule is absent, a scalar satisfiability calculation, or a proposed new rule discharges no parent condition.

Preserve the original source, binder, provider, scope, occurrence, event, event telescope, residual clauses, active single `f` root, complete helper Call, every independent `g` use, qualified signed pairs/equalities, and all existing quantifiers. Do not freshen or duplicate `f`, drop a Call/effect clause, choose allocation based on successful typing, narrow accepted source forms, or assume source-law success. The R30 `j0/a0` obstruction remains independent.

## Governing evidence and pinned dependencies

- Authoritative [Source Generalize definition](../../../notes/design/2026-10-08-source-generalize-definition.md), especially §§2–4; its local L1–L5 laws remain premises, not conclusions.
- Authoritative [local self-recursive binding](../../../notes/design/2026-10-10-local-self-recursive-binding.md), especially §§1–3 and 56–91.
- Reviewed bounded [nested active-root derivation](../../../notes/theory/2026-10-13-nested-live-root-generalization-derivation.md), especially §§3–7; prior scalar calculation alone is insufficient.
- Existing [intrusion event qualification](../../../notes/design/2026-10-12-intrusion-value-type-association.md) and [parent-copy SCC operation](../../../notes/design/2026-10-10-parent-copy-scc-intrusion.md).
- Native source scheduling: `crates/yu-solver/src/candidate_source.rs`.
- Native root capture, publication and FreshUse allocation: `crates/yu-solver/src/candidate_scheme.rs`.
- Lexical identity/resolution: `crates/yu-hir/src/module/local_source.rs`.

SHA-256 pins:

```text
46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38  notes/design/2026-10-08-source-generalize-definition.md
38d42183fdc4f2c0136112d8b305816241d8f449367b473e4de3a5135dc49895  notes/design/2026-10-10-local-self-recursive-binding.md
f72404c661736ee9e0b6226dfc471724795836510c7aa3a0582d209be47f8dd9  notes/theory/2026-10-13-nested-live-root-generalization-derivation.md
531a9efae0ab7e03bfbd2f41cd7da86078e2fc8e67675d2c5c941972409f4e89  notes/design/2026-10-12-intrusion-value-type-association.md
6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b  notes/design/2026-10-10-parent-copy-scc-intrusion.md
66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c  crates/yu-solver/src/candidate_source.rs
03b44d0f8280c1ae79f66b5528f1bd0b0ffebac46b312ef7ffce605f702f48dd  crates/yu-solver/src/candidate_scheme.rs
ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5  crates/yu-hir/src/module/local_source.rs
```

## Lanes and exact leases

### Constructive derivation — Sol/high, cap 360 seconds

Exact writes:

- `notes/theory/2026-10-18-active-outer-root-allocation-derivation-r31.md`
- `tasks/agent-loop/inbox/20261018-active-outer-root-allocation-derivation-r31.md`

Unfold the complete adopted source rules from binding registration through active-root Name resolution, Call generation, intrusion qualification/equality, Generalize publication, and two independent helper uses. Construct full binder/event telescopes and source-owned records. Either derive the placement of `C` and its equality clauses at their original scopes or stop at the first missing rule with exact conclusion/owner. Apply any valid lemma directly to the original intrusion/principality/N-Transport dependency; do not claim closure from a placement sublemma.

### Independent falsifier and source/native map — researcher, cap 300 seconds

Exact writes:

- `notes/theory/2026-10-18-active-outer-root-allocation-falsifier-r31.md`
- `tasks/agent-loop/inbox/20261018-active-outer-root-allocation-falsifier-r31.md`

Independently compare both proposed allocations against every applicable adopted constructor and complete source clause. Check lexical/provider identity, original parameter scopes, event witnesses/telescopes, retained extrusion pairs/equalities, active `f` root, whole Call, aliases versus independent uses and the actual source/native map. A countermodel must satisfy the actual adopted judgment; the earlier scalar model is only a discriminator. Report whether one placement is forced, both are admitted, or a precise source law is missing. No third allocation or new rule.

### Review and integration — Luna

After both outputs freeze, assign one fresh compiler referee (cap 180 seconds) to audit rule coverage, scopes, source/native correspondence and the classification. Luna integrates (cap 120 seconds), applies only a complete reviewed result to its parent, records the exact remaining premise, and updates compact state.

## Implementation and resource boundaries

Current implementation status for this source law is `NO_SAFE_CODE_SLICE`: existing native code retains a single active initializer root, records recursive `Link` actions, captures the published graph and shares low-level rows under FreshUse. It does not establish which source-Generalize dependency record owns `C`. No compiler edits, tests, builds, executable probes or Astra. No implementation lease is granted. Existing independently approved work remains unaffected.

Total R31 cap: **960 seconds** (proof 360 + falsifier 300 + fresh review 180 + integration 120). Astra0; no carried budget from R30. All source writes remain exact-path exclusive. Children do not edit contracts/current/task ledgers or use Git. Stop immediately at a missing adopted source-law judgment; do not draft/adopt a replacement rule inside this sprint.

## Stop and parent application

Freeze one of: complete placement derivation; complete two-placement nondeterminacy proof; or exact first missing constructor/judgment with source owner, original scope and falsifier. A new-rule proposal is not an outcome. Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN/closure0 unless an independently reviewed result actually discharges an original quantified condition. Same-root `Z.V/Z.Car`, fixed-`c` license, `Initial`, full Call, F1/FK1, soundness, principality and termination remain distinct gates.
