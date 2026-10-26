# Native fresh scope transport from actual allocation

Status: Lean-checked successful ID-allocation projection; original full Effect
hygiene and source-to-native correspondence remain open. Independent review
receipt is kept beside the lane handoff.

## 1. Boundary being closed

The previous `NativeScopeTransformer.evaluate_rename` proves native scoped
evaluation commutes with jointly injective maps on scopes and input-route
tags. Injection merely on a transformer's private support is insufficient:
`release 0` must not delete an unrelated incoming protection `1` after names
are changed. The actual caller has to cover the incoming state as well.

The actual map in `candidate_scheme.rs` is lookup-or-identity in the maps
returned by `candidate_source.rs::ScopeInventory::fresh`. It cannot satisfy
global injection on every natural number. For an inventory of length 2,
copying key 0 gives the map `0 ↦ 2`, while the out-of-inventory number 2 still
maps to itself. Strengthening the native algorithm to globally rename every
possible number would not describe the implementation.

The useful exact property is injection on the **entire existing inventory**,
with copied local names separated from fixed external names. This module
constructs that property from the concrete allocation recurrence.

## 2. Exact successful ID projection

For each of scopes and tags independently, a state is `(next, remap)`.
Initially it is `(n, identity)`. Copying key k computes

\[
  next' = next + 1,\qquad
  remap'(x) = \begin{cases} next & x=k,\\ remap(x)&x\ne k.\end{cases}
\]

The keys are the ordered concatenation of the corresponding lists in the
owned source regions. This is the ID portion of the native loop: allocate at
the current vector length, append, then `HashMap::insert`. Default lookup on
an uncopied key is identity. Repeated keys are handled by overwrite, exactly
as in the map; no `Nodup` condition is needed by the theorem.

The model intentionally does not represent region-parent pointers, source
origin payloads, allocator failure or integer conversion. A successful native
execution with the specified old counts and enumeration has this projection.
The mathematical theorem is more general than valid native enumerations;
it does not assert malformed keys can execute successfully in Rust.

## 3. Constructing the invariant

After any prefix of copies:

1. Every old ID x < n has `remap(x) < next`.
2. There exists an injective ghost map p on Nat with `p(x) = remap(x)` for
   every old ID x < n.

Both hold initially for identity. At an allocation of key k, define

\[
 p'(x) = swap(p(k),next)(p(x)).
\]

The swap is an involution, hence injective. For an old ID x equal to k, it
maps to the new fresh ID. For a distinct old ID, injectivity gives
`p(x) ≠ p(k)` and the old bound gives `p(x) < next`; therefore the swap leaves
it unchanged. This argument also works for repeated keys and keys outside
the old domain. The ghost map only witnesses a proof; it is never substituted
for the native map outside the domain actually read by the program.

Induction constructs `fresh_extends`. Its consequences are:

| Checked theorem | Constructed result |
| --- | --- |
| `fresh_next` | Final count is n plus the number of copy operations. |
| `fresh_injective_on_old` | Equal images of two old IDs imply equal old IDs. |
| `fresh_untouched` | An unlisted key keeps its identity image. |
| `fresh_touched_range` | A copied key's final image is at least n and below the final count. |
| `fresh_copied_disjoint_from_fixed` | A copied key cannot alias an old unlisted external key. |
| `native_map_not_globally_injective` | The concrete native map need not be injective outside the old inventory. |
| `repeated_key_overwrites_without_old_collision` | Copying `[0,0]` at count 2 yields `0 ↦ 3`, `1 ↦ 1`, final count 4, and still injects the old inventory. |

## 4. Evaluation commutation and next-use validity

`TransformerValid ns nt F` requires all F's scope keys below ns and all stamped
and missing-guard tags below nt. `StateValid ns nt S` requires all incoming
protection scopes and input tags in those same old inventories. These include
external names, not just copied locals or a particular transformer's support.

Evaluation constructs only tags from the old input/stamped lists and scopes
from the old protection/entry-key lists. `evaluate_valid` therefore derives
output validity from the two explicit input validities.

The actual native maps and their constructed injective extensions agree on
every location read by F, S and F(S). Renaming congruence on those supports,
together with `NativeScopeTransformer.evaluate_rename`, gives

\[
  (rename\ F)(rename\ S) \simeq rename(F(S)).
\]

Here \(\simeq\) is membership equivalence in both coordinates, as in the
existing finite-set content algebra. It does not identify native vector
sorting, byte representation or loop execution with list reduction.

`fresh_evaluate` has no supplied injection premise. `fresh_state_valid` and
`fresh_transformer_valid` construct validity in the new inventories.
`fresh_evaluate_and_reuse` packages commutation with transformer/output
validity for the next copy. It imposes no fixed global bound on how many
later copies may occur; it is not a termination theorem for that sequence.

The checked external-protection discriminator uses old count 2, local
`release 0`, incoming protection `[1]`, and copy keys `[0]`. The local release
becomes `release 2`; external protection 1 remains. This discharges the
particular gap exposed by the older private-support counterexample for the
actual allocation projection.

## 5. Original parent status

This construction removes an arbitrary-map assumption from the native scoped
transport proof. To apply it to the original full Effect hygiene theorem,
the parent still has to construct the original source-to-inventory invariant
and the same immutable map association for each actual incoming witness,
transformer, demand and Context/Call route. The actual receiver, provider,
receipt, authority, current world, continuation, and complete Call semantics
remain required and are not established by changing two finite coordinates.

No source form or accepted effect is excluded. No test, compiler behavior,
source semantics, toolchain pin or dependency changed. Private availability
limits are neither a new language restriction nor a proof of global inference
termination. The original whole theorem remains open until those independent
obligations are constructed.

## 6. Reproduction

From `notes/theory/lean`, using the pinned installed Lean 4.35.0 toolchain:

```sh
lake build +YulangClosure.NativeFreshScopeTransport
lake env lean -j1 -M1024 AuditFreshScopeTransport.lean
```

The audit enumerates every originating theorem constant, including private
and generated helpers, prints complete types and axiom lists, requires ten
public roots and rejects project axioms and any axiom outside the standard
Lean whitelist. The exact count, input hashes and independent review verdict
are recorded in `tasks/agent-loop/inbox/20261026-whole-fresh-scope-r2.md` and
its separate review receipt. Raw execution logs remain scratch artifacts.
