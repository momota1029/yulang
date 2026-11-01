# R167 Rust/source execution map — candidate scope transformer

Status: **SOURCE-NATIVE-MAPPING**, Luna primary, read-only.
Baseline: `f5af010783f8bd7c748b2e2838078a08283be496`.
Contract SHA-256: `ce025f3a5315a054b2c10ca7edf68c674faa4b70162ad4a587b5aad41f179779`.

## Frozen inputs

- `candidate_scope.rs`: `4d4ea4847ca09d53ea49ef3c411617b5a33a9e3f2d95b887842f74a12e2b7c03`.
- `candidate_context.rs`: `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905`.
- `NativeScopeTransformer.lean`: `68f37763bcaab831ec6248a28144e7b76ede42b7813681850f7c67b0d8df10f6`.
- R165 evaluator: `07f93963e223a1d8ad55b91fed94f4efe3e73459b94b96e1b7051b41a810bc2b`.
- R166 representation model: `bee9bc1d052d05cc39e43da8614f52d09eac4c117d58b040e4eab3334be25e7f`.

## Native call paths and operational facts

`ScopeTransformer` fields are private. No unchecked public constructor exists.
Successful constructor paths are `identity`, `stamp_input`, `protect_body`,
`release`, `then`, and `remap`. Each can return allocation/overflow error
before any output transformer is exposed; this packet models only successful
return values.

### Constructors

- `identity`: default empty stamped/scope vectors.
- `stamp_input`: one-element stamped vector via `singleton`.
- `protect_body`: one `ScopeEntry` with `keep_initial=true` and a singleton
  Missing guard.
- `release`: one false-keep entry with empty Missing guard. The tombstone is
  not removed because it changes inherited protection.

The `u32 -> Nat` encoding preserves equality and strict order. One-element
construction preserves ordered distinct stamps, scope keys and guard tags.

### `then`

1. `union(first.stamped, second.stamped)` allocates an upper bound and advances
   two cursors: emit left smaller, right smaller, equal once. Both remaining
   suffixes are appended when the other list ends.
2. The scope loop picks the minimum current key from either sorted scope list,
   detects a matching left/right entry by equality, and advances a cursor iff
   its matching entry exists. Thus each shared scope is processed once.
3. `keep_second = no second entry || second.keep_initial`; result keep is
   `keep_second && (no first entry || first.keep_initial)`.
4. First guard contributes iff `keep_second`; second guard always contributes
   when present after filtering out tags already in `first.stamped`.
5. Remaining sorted guards are merged with `union`. A result entry is retained
   iff it releases inherited protection (`!keep_initial`) or its Missing guard
   is nonempty; only neutral entries are omitted.

The Lean R166 `thenModel` formula is extensionally the same per-scope formula;
its `unionCursor` is a model of the source ordered `union` transitions. It does
not model reserve calls or Rust execution.

### `remap`

1. Build `input_ids` from `stamped` followed by every Missing guard; sort and
   deduplicate. Call `input_map` once per distinct sorted `input_id`, in that
   order, materializing `mapped_inputs`.
2. Sort/deduplicate a copy of `mapped_inputs`; unequal lengths reject input
   collisions. `lookup(id)` binary-searches sorted `input_ids` and indexes the
   matching image. The same sampled image is used in stamped and guard lanes.
3. Map/sort stamped IDs. Map and sort each guard vector through `lookup`.
4. Iterate original scope entries, call `scope_map` once for each distinct
   scope in that order, and retain its mapped entry. Sort mapped entries by
   scope ID; `windows(2)` rejects equal adjacent mapped scopes.
5. On success, mapped vectors remain ordered. Because input IDs and scope keys
   are distinct on this private finite support, each closure sample defines a
   finite table on that support. These two tables preserve the actual returned
   outputs but make no claim that a stateful `FnMut` closure is extensionally
   pure outside the finite trace. Separate closures may share captured state;
   their actual call sequence is `input_map` samples first, then `scope_map`
   samples. The source trace must retain both ordered sequences.

The Lean R166 remap model represents already sampled tables as pure maps. Its
`remap_representation` proves consequences of successful collision checks;
R167 must derive those finite maps from the call trace, not assume final field
equality. Rust standard-library contracts used are: `sort_unstable` returns a
sorted permutation, `dedup` removes equal adjacent values from a sorted list,
and `binary_search` on a sorted slice succeeds exactly for members. The Lean
proof may formalize these mathematical contracts but does not verify std
machine code.

### Consumer boundary

`candidate_context.rs::evaluate_observation` calls `evaluate` from empty state.
R165 independently proves evaluator/denotation equivalence for arbitrary
initial states. R167 must preserve that theorem's quantifier; the actual
observer's empty state does not justify narrowing the model theorem.

No Rust source/build/test or expected output changed or ran. No unrelated dirty
or quarantined path was inspected. The mapping is primary-authored; independent
compiler review remains pending.
