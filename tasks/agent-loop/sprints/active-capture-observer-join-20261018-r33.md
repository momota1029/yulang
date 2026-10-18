# Sprint R33 — active-capture observer join and allocating lift

Status: ACTIVE. Branch `research/simple-sub-intrusion`; baseline
`4122234969ee791af583e6538c303b606f3b3557`.

## Original outcome and success evidence

Unchanged parent goal: implement Yulang type inference and executor with proofs.
Original parent conditions remain OPEN at `0 -> 0`; preserve the original source,
provider, binder, scope, event, complete Call/effects, both helper-use frames,
signed pairs/equalities, and every quantifier. R30's `j0/a0`/same-event action
remains an independent blocker.

Fixed outcome: take the exact active-root nested-helper source witness and use
the existing `intrusion_observation()` records plus private source test-module
records to establish (or precisely fail to establish) the join:

`active initializer Link -> checking/source event -> signed demand/pair incidence
 -> nested-helper publication -> both retained FreshUse maps`.

In parallel, reuse R32's reviewed reference-retention result to attempt one
explicit research-only allocating C/D introduction derived from the actual
joined incidence. Prove the complete erasure and universal lift over the
unchanged joined Call tree, or return the exact first failed constructor/field.
Do not infer source declaration authority from native identities, and do not
adopt a new semantic rule or change production allocation policy.

Success evidence is either a reviewed authentic native join plus a test result
that asserts both use maps and every claimed incidence, or a reviewed complete
allocating lift/qualified source counterexample. An observer partial join,
candidate definition, proposed rule, or passing test alone does not discharge
an original condition.

## Governing sources and pinned dependencies

- Source Generalize definition `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38`;
  construction proof `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`.
- Local self-recursive binding `38d42183fdc4f2c0136112d8b305816241d8f449367b473e4de3a5135dc49895`;
  nested-root derivation `f72404c661736ee9e0b6226dfc471724795836510c7aa3a0582d209be47f8dd9`.
- Intrusion qualification `531a9efae0ab7e03bfbd2f41cd7da86078e2fc8e67675d2c5c941972409f4e89`;
  parent-copy operation `6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b`.
- Source contract `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186`.
- Native `candidate_source.rs` `66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c`;
  `candidate_scheme.rs` `03b44d0f8280c1ae79f66b5528f1bd0b0ffebac46b312ef7ffce605f702f48dd`;
  HIR local source `ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5`.
- Existing public observation owner `shadow_apply.rs`
  `5bbcf27d51906814ba38b2cca2066807d285d0b1817f0ea6e04d70c4a5c8a5cb`;
  nested intrusion observation regression
  `04a876b9fe0a3a45f2d1996446a11d0b36dce3bb26ad02537118e4853e4b78e1`.
- Existing nested recursion regression
  `a6406f3eef2b25844272da9cbe121277001760d004f733029dcc3f600aa79c7a`.
- R32 reviewed proof `fa0e0f25dfd454a51c924b505e847b02133a37b38689e033d34ae5796b24eb8b`,
  native boundary `7f17c297866236db3d0b6eaa1e1e26d6b030216280add558bc2fda124e652655`,
  closeout `01f3e21402d6b5df9e85579f3d763af3fc750c23f347dea4f6921ac1c458f1cb`.

## Lanes and exact leases

### Native provenance join — Luna implementer, cap 420 seconds

Writes only:

- `crates/yu-solver/src/candidate_source.rs` **existing `#[cfg(test)]` test module only**
- `crates/yu-solver/tests/candidate_local_self_recursion.rs`
- `notes/progress/2026-10-18-active-capture-native-join-r33.md`
- `tasks/agent-loop/inbox/20261018-active-capture-native-join-r33.md`

Extend the nested-helper fixture to two independent helper calls. Join the
exact active-root Link/checking occurrence through existing intrusion event,
signed parent/copy, representative and FreshUse records. Private `Action` and
retained test-module state may be used for proof of provenance; add no production
observer/API. The test must reject a source occurrence substitution, an
unrelated equal representative, an empty/vacuous pair set, and a single-use
map. Distinguish the active recursive Link (no FreshUse) from the two helper
FreshUses; assert pair and use image identities only where the existing data
actually proves them.

Authorized focused check, one sequential Cargo process owned by this lane:

```text
cargo test -p yu-solver --features shadow-apply-candidate active_outer_root_two_helper_uses
```

No production code, public observer/API change, allocation-policy edit,
expected-output change, other test/build, probe, or second Cargo process. If the
join cannot be made with these private existing records, stop at the exact
missing edge; do not invent an observation value.

### Allocating source lift — Sol/high, cap 600 seconds

Writes only:

- `notes/theory/2026-10-18-active-capture-allocating-lift-r33.md`
- `tasks/agent-loop/inbox/20261018-active-capture-allocating-lift-r33.md`

Start from R32's reference-only erasure/lifting lemma and the frozen R33 source
incidence witness if available. Attempt one explicit candidate owning
introduction for C/D with authentic sorts, original scopes/telescopes, owner,
typed dependency edges, signed-pair transformations and all equality/residual
incidences. Prove erasure and lift for every unchanged complete Call witness
over both independent uses and arbitrary original client context. If no
existing constructor can introduce it, say so at the exact constructor
inversion; if a candidate semantic choice is needed, preserve it as an
unadopted candidate and identify its effect on original admission/Call.

## Review, resources, and integration

After freeze, assign fresh compiler and spec reviewers, 180 seconds each. The
compiler reviewer attacks occurrence/pair/use joins and checks the test only
uses authenticated identities. The spec reviewer checks full original scopes,
Call/effects, both directions, and candidate-versus-adopted status. Luna
integration cap 120 seconds. Total cap 1,500 seconds: proof600 + native420 +
reviews360 + integration120. Astra0. One focused Cargo process maximum, run
sequentially by the native lane. No carried R32 budget.

Any production observer, new source declaration law, allocation change, extra
test scope, resource increase, or source-domain narrowing requires a separate
Luna contract decision. Keep R30 independent and OPEN. Stop on test failure,
unjoinable exact identity, missing source constructor, review defect or cap.
Next consultation: a complete reviewed join/lift, authentic counterexample,
new semantic choice, or material dependency/resource change.
