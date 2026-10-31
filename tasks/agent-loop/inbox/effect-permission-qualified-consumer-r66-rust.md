# R66 Rust handoff — occurrence-qualified Internal/root request view

Sprint `EFFECT-PERMISSION-QUALIFIED-CONSUMER/20261031-R66`, contract
revision 1, SHA-256
`e3bad12e18f09bc01992c68f0f1f5c02bdcb5f6c7ed4b508cd814a5c2409fd38`.
Assignment `/root/r66_rust`, handoff revision 1. Parent: unchanged
effect-hygiene obligation under `research/simple-sub-intrusion`; source domain,
lawful histories, scopes, A/B quantifiers, permission semantics and production
authority are unchanged. Baseline HEAD
`5e57e7f1376a32c6d2c88a10582f6a1ff4a160c1`.

## Runtime, lease, and inputs

Role requested: implementer, Luna/high. Requested model/effort:
`gpt-6-luna`/high. Effective model, effort, session launch receipt and exact
active-work telemetry: UNKNOWN in available runtime metadata. Assigned bound:
1,200 seconds; elapsed and remaining assignment time are UNKNOWN. No
descendants. Exact write leases used: `crates/yu-solver/src/candidate_receiver.rs`
and this handoff only.

Frozen input hashes rechecked before editing and at handoff:

- R65 receiver baseline: `a729f7ae68b421073b36e26d687ef7ef69e79f5d5674a7e1884b4058c37431e3`.
- `crates/yu-solver/src/lib.rs`: `25498cc1be404b12d060cbd47f77e78c23ad27b2b99113e15823bc8b6fa92ca4`.
- `crates/yu-solver/src/candidate_context.rs`: `962af7c44b2e57ba50b7738e82785bd68b517e881ba08ea41c544c9314d60021`.
- R65 `OccurrenceQualifiedFactReadersR65.lean`:
  `3253e00f9b523446363507ae39567bab0a4ca69a2fc84cc128f8952c43bb700b`.
- R62 `InternalRootPolicyR62.lean`:
  `e76e41a853673e75555cc5e603f1f84c456332794980613c554a2d69af8d976e`.
- R60 `NativeLocalDecodeR60.lean`:
  `3eccc41902a8a8768a55cac020efd4936517da3feb2d91a7ec158994a133ca20`.
- R61 `BoundedAncestryR61.lean`:
  `9e1c783016bc14487dd0a4ebc2839dfab0dc3daf911ee88fa02f3624e2ad60a4`.
- R49 `AuthenticatedResidualConsumerR49.lean`:
  `4fc4380f3ad1827ecf155f982e5186b32d6d91909039fb118063d8f1e2df2`.
- R66 sprint contract: `e3bad12e18f09bc01992c68f0f1f5c02bdcb5f6c7ed4b508cd814a5c2409fd38`.

## Outcome and parent application

Extended the private R65 `InventoryPackage` reader with
`InventoryInternalRootView`. The view keeps borrowed records from the selected
owner package and validates one joined chain:

1. The exact collected source call, source owner, expression checking
   occurrence, selected `DefinitionUse`, and R66 schema call coordinates.
2. R65 occurrence-qualified slot-0 Internal and slot-2 lambda fact rows,
   including their original provenance edges and selected semantic facts.
3. The unique matching Internal route, actual formal registration and lambda
   recipe, and selected raw permission entry with its annotation/source-row
   coordinates.
4. The R47/R49-facing Internal root request, registered-root join, root
   component plan, retained root relation, and the exact indexed emission and
   admission records.

Construction rejects missing or repeated source-call/route/fact candidates,
coordinate or owner mismatch, permission substitution, inconsistent
registration/recipe/root joins, and emission/admission index or relation
mismatch. The package capture now requires this view to be constructible. It is
private evidence only; it does not route, propagate, subtract, consume a
permission, or change execution. Catch slot 51 continues through the existing
R65/R57 reader.

This provides source-to-owner-record evidence for the R66 policy/consumer
adapter: the R65 reader selects the actual records and R60/R61/R62/R49 inputs
remain frozen for the proof lane. The Rust change does not itself connect or
execute the R49 consumer and does not establish a Rust-to-Lean owner/token/index
correspondence. The compiler path from source constraints through ordinary
inference, propagation, routing and execution is untouched by this bounded
view contribution.

## Evidence, checks, and limits

- Final receiver SHA-256: `253c0e469b91a30580a65ec57569a20ed7ad53fd7d7e82c0dc7d2e71102fad1a`.
- `git diff --check -- crates/yu-solver/src/candidate_receiver.rs`: PASS.
- Manual source and diff inspection only. No build, test, Cargo, formatter,
  Lean checker, Git mutation, cache, target, environment, worktree, scratch or
  persistent generated output was run or created. Compile behavior is
  unverified by the fixed contract.
- Prior evidence reused: R65's reviewed owner-local occurrence/slot reader,
  provenance inventory and source-call/schema package; the R65 final review
  confirmed same-key duplicate rejection, preservation of distinct keys sharing
  a FactId, and the absence of a global FactId uniqueness premise. R64/R65
  compilation remained unverified and was not treated as compiler evidence.
- No withdrawn Simple-sub bypass, global identity uniqueness assumption,
  changed inference expectation, diagnostic, source domain or semantic rule was
  restored or introduced.

## Open correspondence and next related step

TODO `R66-RUST-LEAN-OWNER-VIEW-1` (request only; not a central-state update):
the R66 proof lane or Luna must connect these exact selected Rust records and
source/schema coordinates to the R65 `readAt`/R62 root-policy/R49 authenticated
Context objects. Inputs are the frozen hashes above and this receiver's
`InventoryInternalRootView`. Falsifier: a duplicate at one occurrence/slot
must reject; distinct occurrences sharing one FactId must both remain retained;
foreign roots, changed raw permission entries, or mismatched consumer Context
projections must not be accepted. Source-owner authentication across Rust and
Lean remains OPEN pending that correspondence.

Original A/B, successful outer Run, source-to-Native completeness, native
pointer/token/index authenticity, actual native multiplicity, full effect
hygiene, soundness, principality, termination and production remain OPEN. No
finite proof witness or private source view is an executed native counterexample
or production result.

Worker state: **STOPPED / WRITES STOPPED.** No descendants or disposable
scratch paths remain. Frozen handoff revision 1; Luna owns intake, review and
integration.
