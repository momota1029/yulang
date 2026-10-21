# R196 — Source levels and physical Capture owners

Status: constructive source-transition audit; original frontier law remains OPEN.

## Exact source pins and scope

The audit examined the production writers of `value_levels`, `effect_levels`,
`LiveVariableMetadata::non_generic`, forest representatives, and physical bound
ownership. Worktree hashes at inspection:

| File | SHA-256 |
| --- | --- |
| `candidate_source.rs` | `937ce62065be19473fcb37a104f1aaf68e9a9431b8683d8e9a33d221c9e6c26a` |
| `lib.rs` | `24f480355979ee5d96305a08abf6aab67025ede32c2a1575b779e46f5e23b436` |
| `candidate_extrusion.rs` | `7c9a46d327a5e2e3f9e6f8d79f36f11fe21b4a3f68426526e85424a39e2c6332` |
| `candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `candidate_context.rs` | `a08ff10637f1ff9a67005f96c5e1bc26a44778f911944054a25cf28bec5ce733` |
| `candidate_effect.rs` | `c1d7ce19ef5192a46d605faabae34e4437b1f1a15819b5657ec1d70eda7900d1` |
| `candidate_scheme.rs` | `48094aff85175ef7b30d1ef8be0e8fc42d6e5282d0c4d562c4a730c13d401b25` |

No code, tests, or scratch files were changed or run in R196.

## Production transition inventory

1. **Source-level initialization.** Collected rows start at level 1. Candidate
   source initialization then assigns the levels in the source schedule to
   component and parameter rows. A computation formal's entry effect is
   allocated at the parameter's assigned level. The direct Name/Lambda
   constructor audited in R183 gives its paired source rows the same level;
   this fact does not cover every later transition.
2. **Fresh rows.** `fresh_value_at_level` and `fresh_effect_at_level` append the
   requested level and `non_generic=false`.
3. **Typed extrusion.** `lib.rs::extrude` only lowers a row whose current level
   exceeds the target. Before lowering, it journals the row; then it follows
   both direct adjacency directions, exact non-variable bounds and all
   Function children. Thus every already-installed row neighbor reached by
   this traversal is lowered to the same target. It does not visit a bound
   inserted later in the work item.
4. **Bound insertion.** Candidate Apply chooses a physical owner from the two
   endpoint levels and side, inserts the bound and attaches its source evidence.
   Source relation and physical key stay separate. An edge created after an
   extrusion can therefore connect a row at the selected target with an
   endpoint that was not in that earlier traversal.
5. **Signed extrusion.** `candidate_extrude` allocates copies at a target level,
   installs an extrusion parent link, and walks only the requested polarity's
   direct/exact bound side. It transports the corresponding source fibers to
   copied keys. The opposite side is not traversed by that step.
6. **Canonical merge.** `settle_candidate_intrusion` merges a copied row into
   its parent after the parent's level/target guard. `merge_candidate_rows`
   first transfers both physical bound sides and their attached fibers to the
   parent key. It then assigns the parent's level to `min(parent, copy)` and
   its non-generic bit to the disjunction, changes the forest representative,
   and canonicalizes bound incidence. The merge does not itself extrude all
   neighbors after taking the lower level.
7. **Rollback.** The route journal records old row levels/non-generic bits and
   bound lengths/capacities before mutation; intrusion undo records forest
   writes. Rollback restores those values, forest links, and copied state.
   Therefore a valid rollback returns the prior owner classification; it does
   not establish the needed invariant for a successful merge.

Outside tests, the direct production writers found were source-level
initialization, extrusion lowering, and merge minimum/OR. The other indexed
level writes in `lib.rs` are journal restoration; direct non-generic `true`
assignments found by the search are test setup. This inventory identifies the
places a complete induction must cover; it is not itself that induction.

## Exact missing induction case

The direct source constructor's equal-level case is sound under its stated
premise, and extrusion closes over already-installed adjacent rows. The
unresolved transition is a successful signed copy followed by canonical merge:

```text
copy has a selected-side bound to neighbor;
copy is merged into an older parent;
both bound fibers move to parent;
parent level becomes min(parent, copy);
neighbor's level is not changed by merge itself.
```

If the parent is at/below a later Capture boundary while the neighbor remains
above it and generic, the surviving owner becomes shared and Capture will not
expand it. The transferred relation can then be omitted from that local
frontier. The current code establishes this state transition mechanically;
this audit does not show that an accepted source history realizes the
antecedent or all three original Name/Lambda edges. It is therefore a
transition-level obstruction to proving the universal law from local
extrusion/merge code alone, not a source-qualified counterexample.

The exact remaining premise is a source-history lemma for this merge case:
for each original edge rehomed under a representative that becomes shared,
either all required neighboring source rows are also below the boundary, or an
independently reached Function/shared-anchor path supplies the same original
admission and mapped endpoints. The premise must include successful source
admission, one-sided copy selection, canonical representative changes, bound
fiber transport, and rollback validity. The R187 fixture result in R195 does
not discharge it. Original parent, A/B, source/native correspondence, and
production remain OPEN.

No independent review was performed.
