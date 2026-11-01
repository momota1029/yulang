# R165 source handoff — native scope evaluator

Status: **SOURCE-NATIVE-EVIDENCE**, Luna primary, read-only Rust inspection.
Baseline: `92b7b726e35476254b4772dc59a7881667e65916`.
Contract SHA-256: `6b40ab89d3956c4e7967a3c6a303fb4db9597e8f70df6103d4a7bfdee7e15062`.

## Frozen source inputs

- `crates/yu-solver/src/candidate_scope.rs`:
  `4d4ea4847ca09d53ea49ef3c411617b5a33a9e3f2d95b887842f74a12e2b7c03`.
- `crates/yu-solver/src/candidate_context.rs`:
  `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905`.
- `notes/theory/lean/YulangClosure/NativeScopeTransformer.lean`:
  `68f37763bcaab831ec6248a28144e7b76ede42b7813681850f7c67b0d8df10f6`.
- Annotation policy:
  `notes/design/2026-10-10-annotation-effect-hygiene-integration.md`.
- Compose scope rule:
  `notes/design/2026-10-15-compose-scoped-effect-release.md` and its finite
  construction `notes/theory/2026-10-15-compose-scoped-release-construction.md`.
- Relevant reviewed boundaries: R144 scope-remap source/review; R145 fresh-map
  outcome and R2 review; R147 real-consumer outcome/review.

## Rust implementation correspondence

The native private model is in `candidate_scope.rs`:

1. `InputRouteId` and `EffectScopeId` are distinct ordered numeric ID types.
   `ScopeTransformer` stores stamped input IDs and sorted scope entries.
   A scope entry contains `keep_initial` and a `Missing(tags)` disjunction.
   Effect members and capture grants are explicitly outside this representation.
2. `identity`, `stamp_input`, `protect_body`, and `release` produce empty or
   singleton canonical vectors. `release` retains a false-keep tombstone even
   with an empty addition guard.
3. `then` merges sorted-unique stamped and scope vectors, processes scopes with
   two indices, composes the keep bit, removes first additions when the second
   entry releases, and removes second-guard tags already stamped by the first
   transformer. It omits only a fully neutral scope entry.
4. `remap` gathers the transformer's own stamped/guard support, sorts and
   deduplicates input IDs, invokes each input map once per distinct support ID,
   rejects collisions within that input support, maps/sorts scope entries, and
   rejects duplicate mapped scope IDs. These local checks do not establish
   injectivity against arbitrary external IDs or the complete FreshUse support.
5. `evaluate` takes immutable slices. It copies and sorts/deduplicates both
   initial slices. It unions normalized initial inputs with stamped inputs.
   Its protection loop merges sorted initial protections and sorted scope
   entries: an initial-only scope is copied unchanged; a transformer entry
   computes whether the same scope was inherited, retains it iff
   `keep_initial && inherited`, or adds it iff `Missing(tags)` holds against
   normalized **initial_inputs**. Stamped/final inputs do not satisfy a guard.
   On success the produced input/protection vectors are sorted and unique.
   Fallible reserve/checked-capacity failures return before a `ScopeState` is
   exposed; they are outside the mathematical success-result theorem.

The representation precondition needed by the loop is: `stamped` is strictly
increasing; `scopes` is strictly increasing by scope ID; and each `Missing`
tag vector is strictly increasing. The singleton constructors establish it,
`then`'s ordered merges plus `union` preserve it, and `remap` sorts mapped
support and rejects duplicate images. Fields are private to this module, so
the evaluator has no public unchecked constructor. The Lean refinement should
state this invariant explicitly, prove the constructor/`then`/`remap` facts it
uses, and avoid treating arbitrary malformed Rust-internal vectors as reachable.

Existing Lean `NativeScopeTransformer.lean` defines finite list membership as
set membership, `Missing`, identity-default entry lookup, `encode`, transformer
composition, and the denotation `Transformer.evaluate`. Its comments explicitly
exclude Rust sorting/allocation/loop execution. The R165 proof must bridge the
actual sort/dedup and two-cursor loop to this denotation rather than treating
Lean reduction as execution of Rust.

## Callers and evidence boundary

`candidate_context.rs::evaluate_observation` evaluates a retained transformer
from empty inputs/protections. The constructor checks at the scoped-function
boundary identify argument-effect flow with `stamp_input` and result-effect
flow with `protect_body`; source admission can attach `release` to the selected
argument route. `candidate_source.rs` has a corresponding release/protect
construction. These observations identify intended local producer forms, not
whole source attribution or an authenticated arbitrary incoming state.

The theorem may quantify over arbitrary finite incoming slices because the Rust
method itself accepts those arguments. Applying that theorem to every actual
source/native caller still requires evidence that its concrete state and route
are the ones represented by the method inputs. R145/R147 leave same-map
incoming-state authentication, complete joint support bounds, the actual Catch
consumer, and whole source/native effect-hygiene parents open.

## Disposition

No Rust source or tests changed. No Cargo, build, benchmark, or test was run.
This source note is an owner-qualified code map, not proof that the Lean model is
already equivalent or that effect hygiene is complete. Source writes stopped:
yes (primary retains Git/source authority).
