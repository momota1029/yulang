# R92 source-lane handoff: formal admission and App effect hygiene

Status: `FROZEN` for this source pass. Source review and primary adjudication are pending.

## Scope and result

This pass traces the existing original-source owners for formal registration, the App `ViewLogic` binder, the lambda-body `EventProof` binder, Shared delivery, and the decoded formal contract. It does not change compiler behavior or establish a safe Rust edit.

**Result: `NO_SAFE_CODE_SLICE`.** The source model has a constructor-backed selected contract and a real formal Shared delivery, but no source-owned equation currently connects the App-local and body-local logical admissions to preservation of that contract through the actual App Name readout. The generic admission model can express payloads that overwrite descriptor/interface entries; that is a model discriminator, not evidence that such a payload is admitted by the original checker for a source program.

## Source-owned facts

1. **Registration and selection preserve the full pre-invocation input.** `OriginalParameterWorld.Parameter` contains the declaration, ambient scope, context, lambda site, formal, pattern, and body. Its `FormalAssignment` is indexed by the exact parameter, outer route, and ordered `ScopeValues` for `parameter.typeScope`; `select` stores those inputs and the selected contract. `Parameter.coordinate` is the declaration/outer-route/formal-site descriptor coordinate. See `OriginalParameterWorld.lean`, declarations `Parameter`, `Parameter.coordinate`, `FormalAssignment`, `select`, and `selected_before_invocation`.

2. **The original source builder already contains the formal Shared delivery.** `Parameter.generate.tree` is exactly `sourceRules parameter.context parameter.source`, and `Parameter.generate.deliveries` is exactly `[entryDelivery parameter.registration]`. `generated_parameter_existing_owner` and `generated_parameter_delivery_matches_owner` tie that delivery to the owner in the generated original source tree. Value and computation entry positions differ (`route ++ [0,0]` versus `route ++ [0]`); retain both cases. See `OriginalParameterWorld.lean`, `Parameter.generate`, `generated_parameter_delivery`, and the adjacent delivery lemmas.

3. **The local formal-admission policy protects only the lambda's own ViewLogic binder.** `OriginalFormalAdmission.localAdmissions` recognizes a constructor-produced `ViewPacket` at `viewBinder intro.parameter`; it passes `.eventProof` and `.publishedInstance` unchanged to `base.logical`. Its theorems prove the local packet has no descriptor/interface writes and preserves the contract. They do not constrain another ViewLogic binder or the inherited EventProof admission. `admitted_view_is_produced` applies only at that exact `viewBinder`.

4. **Source generation has distinct intervening binders.** In `OriginalSourceGeneration.sourceRules`, App introduces `.existsE ⟨mark.site, .viewLogic, 0⟩` immediately before its `.rule .app`. Lambda introduces its own formal `.description` and `viewLogic` binders, and its checked body later contains `.existsE ⟨body.site, .eventProof, 0⟩`. These are source constructors with distinct routes/sites in the usual case; any equality or repeated-site case must be handled from route/occurrence identity, not presumed away. `run` also has an EventProof binder, so it must not be conflated with the lambda-body binder.

5. **Logical frame decoding really writes contract-bearing fields.** `Decoded.logical` applies `put` to descriptor and interface maps and replaces `viewMeaning`, eta, and witness. `decodeFrame` invokes it for every `.logical _ data`, regardless of the binder's logical kind. The actual contract read is `formalContract` in `OriginalFormalAdmission.readContract`/`formalContract`. Thus preservation follows for the constructor-backed local ViewPacket, but it cannot be inferred solely from the fact that a payload is `.logical` or carries an event proof.

6. **Actual event keys keep occurrence and raw identity, but do not prove admission.** `OriginalSourceEvents.ActualKey` contains origin, route, binder, parent path, occurrence, and raw event operands. The assignment is a function from that key to `Joint`; `different_routes_different_keys` is available. `ActualKey` and its assignment do not encode membership in the generated source rule, nor an admission witness. Distinct routes are separated; exact repeated-route and source occurrence construction still needs the actual traversal theorem.

## Missing source equation

For both entries (`.value` and `.computation`), derive from the actual original checker/source constructor and exact event path—not from an unrestricted `LocalAdmissions` oracle—the following chain:

```text
Parameter + outer route + complete pre-invocation ScopeValues
  -> Selected.contract at Parameter.coordinate
  -> Parameter.generate's original formal Shared owner and delivery
  -> actual lambda body EventProof / App ViewLogic frames with source route,
     parent path, binder and occurrence
  -> decoded state at the actual App
  -> both resolved Name atoms and the contract tuple those atoms read
```

The needed invariant is an equation on the **same full tuple**: descriptor for Value, interface for Computation, together with relevant name/binding, installed Shared object, scope telescope, and any dependent annotation/entry fields. Prove preservation only for intervening frames whose actual source constructors admit them. Establish that the App's callee and resolved Name use this selected tuple. Keep annotation-equality branches and same-site/different-route cases explicit. Do not claim that fixed-frame prefixing, the `ViewPacket` theorem, raw-key injectivity, or the R91 App/Name seam supplies this missing transition law.

## Falsifiers and Rust boundary

- A source-valid distinct introduction mapping to the same complete key falsifies the proposed occurrence identity.
- An actually admitted App `ViewLogic` or body `EventProof` changing the selected descriptor/interface falsifies preservation.
- A resolved Name reading a different formal coordinate or a Shared delivery other than the registered owner falsifies the target connection.
- An unconstrained payload accepted only because the model's `base.logical` is arbitrary is not an original-source counterexample.

Until the source checker produces the preservation/readout equation, no change to Rust candidate effect/registration code is authorized by this result. Leave A/B, effect-hygiene closure, and production promotion open.
