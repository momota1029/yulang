# R131 source handoff — session-owned permission adapter

Sprint: `R131 / effect-permission-session-owned-adapter-20261102-r131`
Contract: `tasks/agent-loop/sprints/effect-permission-session-owned-adapter-20261102-r131.md` (frozen by primary; see contract for its digest)
Admission: `tasks/agent-loop/history/effect-permission-session-owned-adapter-20261102-r131-admission.md`
Assignment / handoff: `R131-source-adapter / revision 1`
Parent: original Simple-sub A/B source-preservation and effect-hygiene objective; source/native/production closure remains OPEN.
Author role/requested runtime: Luna / high implementation lane as assigned. Effective model, effort and worker/session identity are UNKNOWN in the available runtime evidence; no model claim is made.
Exact author output lease: this handoff file only. No Rust source, other artifact, index, or scratch path was written.

## Result class and behavior

`source-native-evidence`, exact in-memory patch candidate. The adapter now takes `&InferenceSession`, `route_index`, and `incidence_index`. It selects both route and retained incidence from that session's candidate graph; derives the term arena from `session.store.terms`, effect state from the selected graph's `intrusion.effect_algebra`, formal registrations from `session.batch.candidate_calls.formals`, and registration/Lambda occurrence from the selected retained incidence. Its returned `FormalEntryPermissionUse<'a>` borrows from the same session for `'a`.

The existing positive Function / child-1 / graph-row / FreshUse / native positive Function-field checks remain in `extract_native_lambda_argument_effect_incidence`. The existing source permission checks remain in `State::bind_formal_entry_permission_use`. The adapter remains read-only, unused, and non-consuming; this does not change inference behavior or produce constraints, handler selection, subtraction, provider behavior, or execution.

## Frozen inputs and byte evidence

All six direct source inputs matched their contract SHA-256 values at inspection. Only `candidate_scheme.rs` is the patch target.

| Input | SHA-256 | Bytes | Use |
|---|---|---:|---|
| `crates/yu-solver/src/candidate_scheme.rs` | `4494ba879a05f90767779e12c9ca8e1364f2203f2f60eb63239a544c0d0da470` | 510,137 | target and route/incidence owner |
| `crates/yu-solver/src/candidate_effect.rs` | `4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15` | 381,143 | source permission binder and permission view |
| `crates/yu-solver/src/lib.rs` | `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be` | 1,662,249 | `InferenceSession` / `ConstraintStore` ownership |
| `crates/yu-solver/src/candidate_call.rs` | `fdc39e01fa3665b4dc14e167973de63b275eb0280b831e340b6cdcee5ed0fc3f` | 32,230 | formal registration input type |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` | 31,786 | graph intrusion/effect-algebra ownership |
| `crates/yu-solver/src/term.rs` | `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1` | 82,419 | term arena/view owner |

Target old SHA-256 / bytes: `4494ba879a05f90767779e12c9ca8e1364f2203f2f60eb63239a544c0d0da470` / 510,137.
Target candidate new SHA-256 / bytes: `896c6e987658ea4d53531ecc74169ba6503dc44840fb12d26463b8219e1f63fa` / 510,418.
The candidate bytes were constructed in memory from the verified target bytes by one exact function-body replacement. The full unified patch follows.

## Exact unified patch

```diff
--- a/crates/yu-solver/src/candidate_scheme.rs
+++ b/crates/yu-solver/src/candidate_scheme.rs
@@ -503,18 +503,22 @@
 /// adapter: it neither stores a consumer nor changes constraints or inference.
 #[allow(dead_code, reason = "permission binding is evidence only; provider and Catch consumption remain open")]
 pub(super) fn bind_native_formal_entry_permission_use<'a>(
-    route: &'a FreshRoute,
+    session: &'a InferenceSession,
+    route_index: usize,
     incidence_index: usize,
-    store: &BranchTermArena,
-    effect_state: &'a candidate_effect::State,
-    registration: usize,
-    registered_formals: &'a [candidate_call::FormalRegistrationInput],
-    occurrence: &'a HirOccurrenceId,
 ) -> Option<(
     NativeLambdaArgumentEffectIncidence,
     candidate_effect::FormalEntryPermissionUse<'a>,
 )> {
+    let graph = session.candidate_graph.as_ref()?;
+    let route = graph.routes.get(route_index)?;
+    let retained_incidence = route.retained.lambda_argument_effects.get(incidence_index)?;
+    let registration = retained_incidence.registration;
+    let occurrence = &retained_incidence.lambda;
+    let registered_formals = &session.batch.candidate_calls.formals;
     let registered = registered_formals.get(registration)?;
+    let store = &session.store.terms;
+    let effect_state = &graph.intrusion.effect_algebra;
     let incidence = extract_native_lambda_argument_effect_incidence(route, incidence_index, store)?;
     if incidence.registration != registration
         || incidence.lambda != *occurrence
```

The hunk's unchanged tail is exact baseline text and remains:

```rust
        || incidence.definition_use != route.use_id
        || incidence.context_use != route.retained.context_use
    {
        return None;
    }
    let permission = effect_state.bind_formal_entry_permission_use(
        registration,
        registered,
        occurrence,
        incidence.entry_effect,
        incidence.mapped_argument_effect_row,
        &route.use_id,
        route.retained.context_use,
    )?;
    Some((incidence, permission))
}
```

Patch anchor: unique function identifier `bind_native_formal_entry_permission_use` at baseline line 505; replacement is bounded by that function's opening signature and closing brace. This is one hunk and changes only its signature and owner derivations.

## Ownership table

| Former independent input / evidence | New source in the one borrowed session | Selection / validation |
|---|---|---|
| `FreshRoute` | `session.candidate_graph.as_ref()?.routes.get(route_index)?` | route index interpreted only within this graph |
| incidence index and its registration | selected route's `retained.lambda_argument_effects.get(incidence_index)?` | registration read from that selected retained incidence |
| Lambda occurrence | selected retained incidence's `lambda` | borrowed directly; no parallel caller occurrence |
| `BranchTermArena` | `session.store.terms` | passed unchanged to native field extractor |
| `candidate_effect::State` | selected graph's `intrusion.effect_algebra` | same graph reached through the session's candidate graph |
| formal-registration slice | `session.batch.candidate_calls.formals` | registration index comes from selected retained incidence |
| source permission | selected graph effect state's binder | original uniqueness, computation role, entry, row kind, owner/formal/scope/occurrence, nonempty concrete payload checks stay in place |
| FreshUse/native correspondence | selected route and its retained maps | original positive Function, child-1, row-map, FreshUse and native field checks stay in extractor; definition/context identity checks stay in adapter |

The index arguments cannot name owners from another session. Every indexed lookup and all returned borrows originate from `session`. Colliding numeric indices in sessions A and B therefore cannot be combined through this API's arguments: B's state, term arena, or formal slice is not an argument and cannot be substituted for A's fields. This is a source-level API construction argument, not compiler-checked evidence.

## Call-site and source-to-Lean relevance

An exact-identifier search over all six pinned source files finds only the definition in `candidate_scheme.rs`; there is no call site. It remains dead, read-only candidate evidence. The source-owned producer and source permission checks remain the preexisting owners. The adapter patch does not cross into the actual consumer/execution path.

The governing user-selected annotation policy remains unchanged: a contravariant concrete annotation grants local subtraction permission, and the actual handler performs subtraction; covariant concrete annotations allow effects, while symbolic variables and their constraints remain. R112/R114 still leave the original App/Lambda source admission, normalization, and full derivation-transport obligation open. In particular, this patch supplies no Lean theorem or Rust-to-Lean relation for route selection, registration/occurrence correspondence, mapped-row identity, Shared/telescope preservation, provider arrival, or Catch handling. R114's conditional binder analysis remains useful: a caller still must authenticate the source-owned constructor and selected route. R129's capped kernel attempt yielded no theorem/kernel result. No prior Simple-sub bypass is restored.

Exact cross-lane TODO for Luna to route: prove or source-qualify the original App/Lambda admission and derivation transport with unchanged source constructors, selected annotation policy, checking evidence, Shared witness, full telescope, and one lawful joint strategy; then identify the source-owned consumer/handler path that uses its permission. First missing evidence: an authenticated relation from actual source construction and retained registration through this route incidence/mapped effect row to the actual event/provider/Catch consumer. Source owner is not identified by R131; the primary must lease that owner. Falsifier: exhibit two same-HIR sessions with colliding route/formal indices where any argument accepted by this API can combine A's route with B's state, terms, or registrations, or show that the existing extractor/binder no longer checks one of the enumerated guards.

## Checks, evidence boundary, and resources

- Rechecked all six source SHA-256 values and byte counts against the R131 contract.
- Constructed the replacement in memory and independently calculated the target old/new SHA-256 and byte lengths. No source materialization or scratch file was used.
- Read the exact session/graph/formal/effect/term owner definitions, the existing adapter and binders, R112/R114/R127/R129 prior evidence, and the governing annotation policy.
- Exact-identifier call-site search over all six pinned files found only the target definition; no invocation was found.
- No compiler, Cargo, build, test, formatter, Lean, checker, environment/storage probe, Git mutation, or quarantined `machine.rs`/`receiving.rs` read occurred. Cargo/check allowance remains unused (0/1).
- Resource limit: 600 seconds maximum; work stopped after the in-memory candidate and this handoff. Exact CPU/RSS/wall telemetry is unavailable; no invocation was allowed to consume a compiler/test allowance.

Prior evidence reused: R114's conditional binder-owner analysis; R112/R114's still-open source/Lean transport premises; R129's recorded resource-capped kernel failure; R127's explicit source-push/compilation boundary. No prior proof or green check is treated as theorem closure or execution evidence. No evidence was rejected as contradictory; none licenses cutover.

## Boundary and handoff

Candidate is provisional source-native evidence only. Independent compiler-referee review of this frozen handoff and the six input pins is pending. Compilation, runtime behavior, Rust-to-Lean correspondence, R112/R114 transport, effect hygiene, original A/B claims, and production readiness remain OPEN. R111's source compile/push decision remains separately pending; R131 grants no source-push authority.

Writer state: this single handoff is frozen at revision 1; no source or additional output lease was used. Requested model/effort: Luna/high. Observed model/effort: UNKNOWN. Review and integration are for the primary to assign. Next related in-envelope step after review: resolve any handoff finding against these frozen bytes; then primary may continue with an independently leased source-owner transport step only if its exact authority and inputs are admitted. This author does not self-certify the candidate.
