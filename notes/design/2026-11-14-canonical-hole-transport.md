# Canonical hole transport and reduced-hole source producers

Status: proof companion, partial source construction. This continues §5 of
[the open-producers note](2026-11-14-hole-phases-open-producers.md).
`ClassPHoleReadback`, universal `Simulation.next`, and unconditional unknown-root
Class P accessibility remain open. No boundary-agreement work is included.

The supervisor's latest owner update (2026-11-14, spec §6.5 / B4 addendum 8)
is authoritative: invariant arguments have explicit actual-argument names
(centers), and lack of a provenance certificate is not a semantic reason for
pending. The local checkout still has the older interval prose; this work does
not edit it. None of the new proofs infers pending from absent provenance.
The other worker owns the centered transition relation.

## 1. The invariant must survive one shared substitution

Fix the original source identity map `origins : Nat → Origin`, and let `H` be
the current subset of the original finite hole set. A uniform labelled
readback consists of:

- a **fixed** source `Pattern p` and finite `Expr Nat t`;
- `Label context p t`: `p` is covered, translates to `quote t`, and `t` is
  canonical, including sorted distinct record field positions;
- `Readback Models origins H actual t`: for **every** current model, `t`
  interpreted at the original source origins describes `actual`, and every
  leaf of `t` is in `H`.

The term, source keys, origin map, and remaining hole set are outside the
model quantifier. This is `UniformHoleLabels.Labelled`; it is not the weaker
statement that each model has some separately chosen finite expression.

Suppose a genuine refinement supplies a labelled expression `p_h, t_h` for
`origins h` over `H.erase h`. Replace **all** occurrences of `h`, simultaneously,
in every relevant expression and source pattern. Then:

1. semantic readbacks remain valid by `IndexedHoleReadback.replace_holds`;
2. leaves lie in `H.erase h` by `replacement_closed`;
3. source-pattern translation agrees with tree substitution by `filled_label`;
4. canonicality survives tree substitution;
5. every newly normalized source pattern retains its actual constructor keys.

`restrict_replace_all` proves these facts for arbitrary model restriction,
independently of any transition relation. `actual_replace` instantiates the
restriction with actual-Step model preservation. The arbitrary predicate
`relevant origin pattern term` permits simultaneous transport of a whole
collection, including old captures, output origins, aliases, and historical
inputs. It does not prove that every relevant newly created ID already belongs
to this collection.

`materialized_labelled` combines the existing actual materialization theorem
with labelled substitution. Its premises are a labelled actual schema recipe,
a single label substitution, uniformly represented actual input uses, and
uniformly represented earlier output-binder identities. Its conclusion is one
fixed labelled finite tree for the allocated target over the same `H`. No new
hole is introduced for the target. The template label and input/binder
readbacks are still producer premises.

## 2. Replacing a minimum by a stable comparison

A minimum chosen by the current unit leaf mass need not remain minimum after
substitution. We do not transport that choice or its old numerical inequality.

Literal equality of all finite capture presentations is also too strong while
cyclic values may remain opaque. For example, an opaque source value `h = V h`
can appear at two variable-only positions with presentations `h` and `V h`.
The head `pair x x` can share the actual value without equating these finite
syntactic expressions. This is a limitation of a proposed proof invariant,
not a new infinite execution, semantic question, or reason to modify Step.

`SubtermOrder.Below` is a sufficient structural comparison: reflexivity,
selection of a child, pointwise comparison under the same constructor, and
transitivity. In particular, `h` is below `V h`. It satisfies, for arbitrary
finite tree substitution `θ` and arbitrary nonnegative leaf weights `w`,

```
Below s t  →  Below (s.bind θ) (t.bind θ)
Below s t  →  weightedTree w s ≤ weightedTree w t
weightedTree w (t.bind θ)
  = weightedTree (fun h => weightedTree w (θ h)) t.
```

The last equality counts every occurrence, with the established canonical
record-spine cost. `filled_mass_exact` identifies the checker mass of the
normalized substituted source label with this exact weighted expression.

A packet `Presentation` retains a single source pattern and tree for each
capture name, an aligned match of every head position against its historical
input label, `Below` witnesses at variable positions, and exact normalized
source child-label equations. Different source constructor keys are retained
even if they translate to the same semantic constructor. The source patterns
cannot be reconstructed merely from semantic tree equality.

`Presentation.substitute` applies one global substitution to all captures and
all occurrence labels. `normalized_args_compose` proves the exact child
syntax equations, including record hiding, variant normalization, and the
emitter's normalization. `head_mass` recomputes the numerical inequality from
the transformed matching certificate. This closes the **transport** part of
§5(3), conditional on obtaining the initial compatible presentation.

No theorem says that arbitrary semantically equal finite trees have a common
`Below` presentation. Obtaining compatible presentations from actual shared
captures, possibly after source-hole identifications, remains a source
obligation.

Only packets that emit children need a presentation. `Checked` supplies the
required covered normalized counts when a where clause exists; a terminal
declaration can still contain syntax outside this covered fragment.
`CanonicalHoleJournal.History` therefore quantifies over nonterminal packets.
`history_descent` and `journal_parents` prove the ancestry bounds directly,
without imposing a new condition on terminal declarations. This is an additive
proof-interface refinement, not a change to the transition relation.

## 3. Actual K2 and exposure over the reduced frontier

`Backed state identities source term` relates a finite presentation to the
**actual** K2 graph. A leaf carries uniform equality with its original source
identity. A constructor supplies an actual K2 edge to each represented child
and recursively supplies its backing. Semantic `Holds` alone does not provide
these edges.

If a constructor tree for `source` contains `h`, and `source` equals the
original identity for `h`, following that occurrence gives a nonempty K2 path
back to an equivalent source. Endpoint equality transports the final edge;
it never acts as a graph edge by itself. Consequently:

- `occurs_cycle` produces the cycle;
- `occurs_rejected` adds the required model witness;
- `tested_occurrence_blocks` rules out an installing packet when that actual
  origin is tested;
- `safe_closed` removes `h` from the replacement's possible leaves.

Thus an inspected safe source with a uniformly graph-backed constructor
expansion has a genuine replacement over `H.erase h`. This is not an occurs
check on nominal bodies, and not an inference from a failed provenance lookup.

`ReducedHoleSources.structural_readback/structural_backed` build the parent
readback and actual edges from a recorded normalized structural observation,
provided each actual child already has a readback and backing over `H`.
`nominal_readback/nominal_backed` do the same for recorded point TYPE arguments.
Children may have compound expressions; they need not be leaves or members of
the new snapshot's frontier. The origin map and `H` stay fixed.

`structural_discharge` and `nominal_discharge` combine those producers with the
old shared leaf, inhabitedness, and actual K2 safety. They return membership
`h ∈ H` and the replacement readback over `H.erase h`. Unlike the earlier
one-level source cases, these theorems work after previous eliminations.
`backed_expansion` also transports every old represented origin across an
actual Step when such an expansion is obtained after it.

There is a second genuine elimination independent of constructor exposure:
if distinct surviving holes `h` and `k` have uniformly equal actual origins,
replace `h` by `k`. `alias_replacement` proves the uniform labelled readback;
`alias_eliminating_install` constructs the one-elimination Trace with growth
zero and transports the whole journal and all old relevant meanings.
Same endpoints, interval overlap, or one chosen model's equality are not
premises of this rule. It uses uniform equality of the **actual** origins.

## 4. The root inventory and certified transition branches

The old phase inventory contains finite `Expr Nat` values and an arbitrary
source-pattern decoder. The new `PatternInventory` provides a reversible
codec for source patterns, including exact constructor and field keys.

These codes are bookkeeping trees, not semantic type trees. In particular,
a two-entry record marker preserves a source field key, its payload and its
tail; it is not a canonical semantic record. No semantic `Label`, `Holds`, or
K2 proof is applied to such a code. Semantic trees remain separate.

`decode_encode_list` is exact. `substituted_root_code` shows that encoding the
normalized substituted root label equals substituting the encoded replacement
in the old root code. Its complete supported-label premises exclude unresolved
record tail spines. `Journal.replace` therefore transports inventory membership
by the actual `HoleElimination.eliminate` operation, without assuming a decoder
commutation law. `journal_bound` and `journal_parents` turn the finite current
inventory into the existing finite snapshot invocation bound.

`actual_retained` gives the zero-elimination branch for any actual transition
whose historical packet list is unchanged; all old labelled meanings restrict
to the new models. It does not account for newly relevant origins.

`actual_eliminating_install` proves the full inventory/history/readback result
for a certified eliminating installation. Its remaining local premises are:

1. the uniform labelled replacement over surviving holes;
2. its source-code closure and boundedness over the fixed finite vocabulary;
3. a simultaneous `Presentation` for the new nonterminal packet under the
   **transformed** historical labels.

The old packet presentations are reconstructed automatically. The resulting
Trace consumes exactly one hole; existing Trace composition gives at most the
initial number of holes over successive refinements. Between refinements,
the established snapshot signature enumeration and administrative order remain
the per-phase engine. This supplies a concrete branch of the intended
`Simulation.next`, not its universal source construction.

## 5. Exact remaining work and center dependence

| Requested part | Proved here | Still required from actual source generation |
|---|---|---|
| Uniform labelled expressions | Model restriction, global replacement, aliasing, labelled materialization from shared input/binder readbacks | Uniform source-key labels and expressions for **every** newly relevant actual center/capture/binder, with simultaneous shared choices |
| Relevant exposure | Reduced-hole structural and point-nominal parent producers; graph-backed occurs check; actual K2 blocking; equal-hole elimination | Exhaustive dispatch of full-report `Exposed`, including fallback origins, plus child graph backing and fixed vocabulary extraction |
| Historical labels | Exact normalized substitution composition, exact post-replacement mass, shared capture/history transport, encoded root inventory transport | Compatible new-packet presentation, preserved relevance and coverage after each refinement |

In particular, missing a proof of `Backed` does **not** imply pending. Missing a
`Labelled` or `Presentation` proof does **not** imply pending. No new such guard
has been introduced. The simultaneous source construction is still the open
content of `ClassPHoleReadback` / `ClassPHolePhases`.

Guard dependence and transfer to centers:

- Composition, mass, source-code, history-descent, materialized-label, and
  generic model-restriction theorems do not mention a Step or missing-provenance
  rule. They remain valid when shared provenance always exists.
- `tested_occurrence_blocks` uses actual-position K2 safety, with positive
  provenance evidence already supplied. It uses no absent-certificate branch.
- Reduced source producers use actual graph edges; the nominal producer is
  currently restricted to point TYPE parameters. A centered nonpoint producer
  must use the actual named argument, rather than an endpoint selected as a
  center.
- Actual-Step wrappers use `step_shared` only for model restriction, or the
  concrete unchanged/cons packet-journal shape. `journal_parents` additionally
  uses the existing birth-lineage reconstruction. Retargeting requires the
  centered relation's corresponding model, journal, lineage, and K2-edge facts;
  no transfer theorem for that future relation is claimed here.

There is no new semantic obstruction and no owner question. No unconditional
unknown-root Class P Acc theorem is claimed.

## 6. Verification and review

Eight new proof modules are imported by appended lines in `Yulang.lean`.
The new audit is `Audit/CanonicalHoleTransport.lean`; the frozen aggregate
audit and README are untouched. No existing proof-module line is changed.

Final commands and results are recorded below after verification. Earlier
elaboration attempts exited 1 while fixing dependent indexing, codec recursion,
and implicit parameter types; those intermediate versions are not the result.

The configured `prover` role and its launch configuration were unavailable.
The primary performed this bounded derivation; no prover agent ran. The
separate available `settled_review` worker independently checked theorem scope,
uniform model quantifiers, source-key preservation, actual graph evidence,
terminal-packet coverage, and guard dependence. It found no blocking issue and
confirmed that source production and universal `Simulation.next` remain open.

Final verification (all commands run from the repository root):

| Exact command | Exit code | Result |
|---|---:|---|
| `cd lean && lake build Yulang.GeneralNominalUniformHoleLabels` | 0 | All eight new modules are in this target's import closure; 803 jobs |
| `cd lean && lake build Yulang` | 0 | Aggregate build; 2315 jobs |
| `cd lean && lake env lean Audit/CanonicalHoleTransport.lean` | 0 | All 23 audited results use at most `propext`, `Classical.choice`, `Quot.sound` |
| `git diff --check` | 0 | No whitespace errors in tracked additions |

A separate scope check verified byte-prefix preservation of `Yulang.lean` and
`notes/design/INDEX.md`, no other tracked-file changes, clean forbidden-token
scan of all eight new modules, and unchanged HEAD `335681dca`. No commit, push,
or ref mutation was performed. Existing proof modules, specs, plan notes,
configuration, `Audit.lean`, and `README.md` are unchanged.

Final independent review also checked the equal-hole elimination and the owner
update. The reviewer independently reran the audit command: exit 0, the same
23 allowed-dependency results. It confirmed that zero growth follows from a
leaf replacement and that no missing proof certificate is treated as pending.
