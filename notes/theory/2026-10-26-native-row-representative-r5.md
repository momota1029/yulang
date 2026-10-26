# Constructing native representative laws

Status: checker-accepted construction, awaiting independent review.
Parent: `MERGE-EXPANSION-COVER-1` and original native inference correspondence.
Source baseline: `97788357754a57562607dd8ff41ac55ffcb3c9b8`; the intervening
`82b8fb669c5b51c6c99771cd2208c9730ebc85c3` adds unrelated Value-port proofs.
No Rust source, native inference behavior or original source scope is changed.

## 1. The premise removed

`NativeReplayCurrent.operand_transport` and `currentPair_absorb` previously
accepted two arbitrary row maps and the equation

```text
current (old row) = current row.
```

`NativeRowRepresentative.generated_transport` now constructs those maps from
an empty forest and a finite history of the actual successful parent-pointer
writes. It derives the equation and applies it directly to the existing
Effect operand and full-key current-pair theorems. The root map is not selected
independently of the pointer lookup, and neither idempotence nor absorption is
a field of the local invariant.

This removes a concrete algebraic premise at that native storage boundary.
It does not establish that a separately supplied complete compiler history
is the real Rust execution, or that its accepted constraints satisfy the
original source typing judgment.

## 2. Actual source operations

| Native owner | Checked construction |
| --- | --- |
| `candidate_intrusion.rs`, `representative` | `Lookup` is the finite execution relation of the parent-following loop. `find` is the identical loop with proof-side fuel; `lookup_terminates` derives finite execution, and `lookup_result` proves its unique result. Out-of-range lookup returns the input row. |
| `retain_extrusion_parent`, the `values`/`effects` extension loops | `birth` adds the next self-root. `vector_birth` proves equality with the exact vector append `parents ++ [parents.length]`, including all outside indices. |
| `merge_candidate_rows` | The native operation looks up the copy and parent roots, returns unchanged if equal, and otherwise writes the copy root to the parent root. `merge` preserves that directed choice. `merge_constructs` derives a valid new certificate and absorption after the actual root lookup. |
| `compress_candidate_forests` | `compressPath` first saves the old parent, writes the selected root, then follows the saved old parent. Its checked construction terminates with the same representative map and ghost rank. `vector_write` identifies each successful slot mutation with `List.set`. |
| `State.value_rep`, `effect_rep`, `rep` | The construction applies separately to each kind's parent vector. A mixed-kind merge remains rejected by the source owner; no cross-kind alias is introduced. |
| Existing `NativeReplayCurrent` consumers | `run_current_pair_transport` and `run_operand_transport` instantiate the old generic equations using the constructed history laws. Rigid endpoint IDs and the original key's Context/source/transformer fields are unchanged. |

The projection models successful mathematical row indices. Native reservation,
checked integer conversion and table-bounds guards are still owned by their
source operations. A no-op merge is an erased stutter. No failure/cancellation
event is falsely represented as a forward union.

## 3. Construction argument

A raw forest is a size and a parent function, with `ofList` giving the exact
native vector interpretation. A certificate has a candidate root function,
a decreasing natural rank, a finite upper bound for that rank, and only local
pointer equations: a self-root represents itself; following one pointer
preserves the root; every nontrivial pointer decreases rank; inside/outside
indices obey the vector bounds. From these clauses, induction over available
fuel constructs the actual lookup result, its terminal self-root, and a rank
bound. Therefore the raw loop terminates and the representative is idempotent.
Two certificates for the same raw forest have the same root function because
the deterministic lookup relation has a unique result.

For a root link `source -> target`, the new root function redirects precisely
the old source component. Its rank is increased on precisely that component;
the amount exceeds the old target rank. The new parent edge and every old edge
therefore decrease the constructed rank. This proof does not assume numeric
row ordering, union-by-rank, an old source preceding the target, or a fixed
maximum native recursion depth.

For compression, the existing selected root is strictly lower in rank unless
the input is already a root. Writing it preserves every root result and the
same rank function. The recursive compression loop follows the *saved old*
parent, so the induction follows the source implementation's actual control
flow. The certificate height used to prove sufficient fuel is a conservative
ghost bound, not a runtime counter, allocation, new rejection policy, or
complexity claim about the compiler.

`Step` contains only raw lookup traces, actual inside-index guards and the
successful birth/link/compression writes. `run_constructs` derives the
certificate for every finite sequence from its initial certificate.
`generated_certificate` constructs the initial certificate from the empty
forest. Absorption composes through all such writes, and
`generated_transport` applies the result to the original dependency's Effect
operand equation with no caller-supplied map law.

## 4. Exact remaining obligations

- Authenticate a complete committed native parent-vector history in the
  original combined operation/frame/journal history. This theorem does not
  erase rollback into a successful merge: cancellation can undo equivalences,
  so forward absorption does not hold across arbitrary rollback cuts.
- Connect the same derived representatives to every other native table and
  canonical key consumer, including Value dispatch and lifetime checks.
- Prove full original Context/Value/record/Call semantics and the same-scoped
  source reconstruction from accepted native inference.
- General inference termination and principality remain open. Termination of
  parent lookup and path compression is a local algorithmic theorem, not a
  statement that the full solver stops or that source programs terminate.

## 5. Verification

The isolated project is pinned to Lean 4.35.0. Final module build (check 08)
exits zero without warnings. The existing `check_lean.py` helper (check 09)
builds the exact module and checks all **26 authored theorem roots**, including
their complete printed types and transitive axiom dependencies. A separate
origin census (check 10) checks all **180 originating declarations**, including
**98 theorem constants**, with no missing private/generated declarations.

The theorem-constant axiom sets are: 35 none; 8 only `propext`; 53
`propext, Quot.sound`; 2 `propext, Classical.choice, Quot.sound`.
No project axiom, `sorryAx`, native-evaluation axiom or checker bypass occurs.
The standard axioms are reported explicitly; this is not an axiom-free claim.

The final module SHA256 is
`91b29ddd33db8b8b67308dff14b655619763d5ecb153b715f03b02c031371ee2`.
The complete origin log is 115,557 bytes, SHA256
`b728cb9a812fbc34220d13ad4feb6e4cf5ffd49206c7d1d638787654bc48cf43`.
All commands, material failure/repair logs and the complete authored-root
type/axiom output are retained in the paired handoff and owned scratch.
