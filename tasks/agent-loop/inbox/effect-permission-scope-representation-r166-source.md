# R166 Rust/source mapping — native scope representation

Status: **SOURCE-NATIVE-MAPPING**, Luna primary, read-only inspection.
Baseline: `3d8ba0b91c720cce142c6b0e19984c5efd938360`.
Contract SHA-256: `85fb9acc51d8e2ce470fc28b4d9054cdea71ecbf28a9edf6f7a751f1201c1037`.

## Frozen direct inputs

- `crates/yu-solver/src/candidate_scope.rs`:
  `4d4ea4847ca09d53ea49ef3c411617b5a33a9e3f2d95b887842f74a12e2b7c03`.
- `crates/yu-solver/src/candidate_context.rs`:
  `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905`.
- `NativeScopeTransformer.lean`:
  `68f37763bcaab831ec6248a28144e7b76ede42b7813681850f7c67b0d8df10f6`.
- R165 Lean evaluator:
  `07f93963e223a1d8ad55b91fed94f4efe3e73459b94b96e1b7051b41a810bc2b`.
- R165 proof handoff:
  `8398752890ad0976f5f9d6f9725f62de5b7dbb2a4c53fa5760a32dcd2249a21b`.

## Native construction map

`InputRouteId(u32)` and `EffectScopeId(u32)` are ordered distinct ID types.
For either wrapper, the value-to-`Nat` encoding `n ↦ n.toNat` preserves `<` and
equality. `ScopeTransformer` is private to `candidate_scope.rs`; no unchecked
public field constructor is exposed. Its required representation facts are:
strictly increasing `stamped`, strictly increasing scope keys, and strictly
increasing `Missing` guard tags.

- `identity` constructs empty vectors.
- `stamp_input` constructs one stamped ID via fallible `singleton`.
- `protect_body` constructs one scope key and one-tag `Missing` guard through
  `singleton`; its `keep_initial` is true.
- `release` constructs one scope key, false keep bit, and empty guard. The
  release tombstone is retained even though its addition predicate is false.
- `then` calls `union` on canonical stamp vectors. `union` is an ordered
  two-index merge with an equal-head coalesce. It merges the two sorted scope
  lists by minimum head; each scope can occur in either or both inputs once.
  For a shared scope it composes keep bits, drops first additions if the second
  entry releases, filters second guard tags already stamped by the first, and
  unions the remaining sorted guard streams. It omits only neutral entries.
  All allocation arithmetic/reservations are fallible; failure returns `Err`
  before an output transformer is returned.
- `remap` gathers distinct IDs from `stamped` and all guard vectors, calls each
  input map once per gathered ID, and rejects duplicate mapped input images.
  It maps each guard through that lookup and sorts it. It sorts mapped stamped
  IDs. It maps scopes, sorts entries by new scope ID, and rejects equal adjacent
  images. Successful output is ordered even for order-reversing maps. The
  collision check covers this transformer's own finite support, not arbitrary
  external state or all FreshUse support.

`AddCondition::holds` searches every guard tag in the normalized initial input
slice with `binary_search`; the result is Missing iff at least one is absent.
`evaluate` obtains this slice through `sorted_copy` (copy, sort, dedup). R165's
Lean predicate uses finite list membership. The needed bridge is the standard
sorted-slice binary-search contract: on a slice sorted under the same total
order, `binary_search(x).is_err()` iff `x` is not a member. This source note
identifies the contract; it does not claim to formalize Rust's standard library
implementation in Lean. Input and scope wrapper orders agree with their `Nat`
encodings.

## R165 model connection and caller boundary

R165 `Canonical` requires ordered stamped values and ordered scope keys. This
is weaker than the full native normal form because it does not require ordered
guard vectors. Guard order is needed for `then`'s ordered guard union and is
preserved by construction. The finite-list `Missing` meaning itself is
order-insensitive. Binary searches run over normalized `initial_inputs`,
first-transformer `stamped` values, and gathered `input_ids`, all of which are
sorted; guard vectors are iterated, not searched. Applying R165 therefore
needs an explicit encoding from each successful native value to `Transformer`
that preserves stamp, scope, keep and guard membership, plus the sorted-slice
search contract above. The Rust clauses have a direct case-by-case model in
the clean source, but that encoding is not constructed by this source
inspection.

At `candidate_context.rs::evaluate_observation`, retained transformers are
evaluated from empty input/protection state. Scoped-function constructor checks
use `stamp_input` for argument-effect flow and `protect_body` for result-effect
flow; release is built from selected source admission. These call sites do not
authenticate arbitrary external support, incoming-state ownership, FreshUse
capture identity, or the full Catch consumption route.

No Rust source/test/build was changed or run. No unrelated dirty or quarantined
path was read. R166 source writes are stopped; primary retains integration and
Git authority.
