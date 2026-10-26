# Finite lattice evidence construction and exactness

Date: 2026-10-26. Assignment ID: `20261026-inference-lattice-decision`.
Handoff revision: **1**, frozen for primary-owned independent review.
Producer: generic leaf `/root/lattice_decision`; no children or coauthors.
Requested role instructions: `.codex/agents/lean-prover.toml`; no custom-role
activation or effective model/effort was independently observed (UNKNOWN).
Outcome class: **kernel-checked proof-side construction**, pending nonauthor
review and primary integration. This is not parent-theorem closure.

## Original parent, authority, and exact ownership

The unchanged parent is `SourceProblem.InferenceSoundness` in
`YulangClosure/Contracts.lean` and `docs/yulang-whole-proof-closure-ja.md` §1:

```lean
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

This retains every original supported source constructor and lawful finite
history, the original lexical/type/event scopes, recursive monomorphic sharing,
generalization and all lawful uses, full Call, effect hygiene and one jointly
chosen source witness. Nothing below narrows those quantifiers or supplies a
new concrete `SourceProblem` instance.

Assigned baseline: branch `yulang3`, HEAD
`79fcb7e362f1ee075cb62aa10e2c60227233dc06`. The primary may advance its own
integration while this leaf uses the exact frozen source dependencies below.
The scope contract is
`notes/progress/2026-10-26-inference-evidence-construction.md`, follow-on
construction lease; its observed freeze-time snapshot is preserved as
`contract-observed.md` in the isolated scratch directory. This snapshot is
not a claim that the primary-owned mutable record had unchanged bytes
throughout the assignment.

Applied root `AGENTS.md`, `AGENTS.pre-sprint.md`, the `yulang-lean-proofs` skill
and source/execution guides, design-authority and orchestration budget rules,
and the exact primary packet. Original semantic authority remains the
2026-10-11 inference principles and 2026-10-24 immutable-birth SCC correction.
The original source-preservation statement was read in
`2026-10-13-intrusion-source-preservation-proof.md` §§1 and 3; manuscript
scope and missing source bridges remain intact. The existing lattice module
is the accepted finite rule/interpretation target, not a substitute source
language. The original paper's Fig. 10 and §§5.1–5.3 were consulted through
`inference-lattice/reference-sections.txt`; in particular, its permission for
unguarded source syntax is not erased by the graph acceptance guard.

Exact repository writes:

- `notes/theory/lean/YulangClosure/SimpleSubLatticeDecision.lean` (new).
- `tasks/agent-loop/inbox/20261026-inference-lattice-decision.md` (this handoff).

All other outputs are under the sole owned scratch directory
`/workspace/scratch/f98087c7ac1a/inference-lattice-decision/`, including its
isolated `project/.lake`. No dependency, other producer source, root import,
shared audit/navigation/status, compiler, toolchain, manifest, question or Git
state was modified. The copied project configuration is unchanged.

## Before and after

Before this packet, accepted lattice evidence required an external finite
`List (Comparison × Derivation)` certificate. The accepted dependency had only
`regular_fold`; selecting a common finite Layer derivation from arbitrary
all-depth witnesses was explicitly unproved.

After this packet, `constructCertificate graph` is an executable function of
the fixed graph alone. It always passes the original certificate checker. For
a valid graph, membership in its table is equivalent to the unchanged,
independently defined all-depth `Lattice.RegularSub`. Reverse unfolding is
proved only after finite saturation and finite-depth coverage establish that
equivalence. There is no external derivation table, model, regular-subtyping,
stabilization or termination premise in construction or accepted-output
soundness.

## Construction and proof argument

1. `allPairs` enumerates every same-kind pair of actual table indices. The
   exact membership theorem retains both endpoint bounds. No proposed
   source-level typing is enumerated.
2. `candidates` tries every declared finite Layer rule: structural, reflexive,
   bottom, top, both union injections, union elimination, both intersection
   projections, intersection introduction, both monotonicity rules, and
   transitivity at every in-range middle. Binary rules combine actual finite
   witnesses already stored. Only the existing `structural` derivation checker
   can consult the recursive comparison table; no lattice hypothesis is
   admitted from its mere table membership.
3. Each `derive` result passes the original `checkDerivation` against the
   fixed recursive table. `close` accumulates those witnesses and removes
   successfully derived pairs from a pending list. A changed round strictly
   shortens that list. Its initial length therefore suffices to produce both
   `Witnesses` and `Saturated`, with no assumed saturation bound.
4. Validity implies every endpoint of every independent finite Layer proof
   exists. This includes the middle of a transitivity proof. `saturated_complete`
   then inducts over all Layer constructors, obtaining child witnesses from the
   saturated certificate and locating the corresponding actual rule candidate.
   Together with checker soundness this proves `layerCertificate_exact`.
5. `prune` starts from the whole universe and deletes pairs for which that
   exact finite layer construction has no witness. Every changed outer round
   strictly shortens the candidate list, so its initial length suffices for a
   postfixed table. `extract` retains precisely that table with its finite
   derivations, and `constructed_checked` uses the original certificate checker.
6. To prove completeness without assuming reverse unfolding, `FiniteCover`
   records an actually constructed depth whose approximant is contained in
   the current candidate table. The universe covers depth 1. Each deletion
   round preserves coverage at the next depth using `Layer.mono` and exact
   finite layer construction. Thus the final table covers some finite depth
   uniformly for all pairs. Every all-depth comparison belongs to that table.
   Certificate soundness supplies the converse. Only then is `regular_unfold`
   derived from the finite shared postfixed table.

Every comparison, including both Function effect ports, uses the same final
table and graph. The unchanged structural expansion retains variance
`(-,-,+,+)`, exact record labels/optional bits, tuple order/arity, and variant
tags with whole payload lists. The actual lattice Layer and Derivation
constructors were not modified.

## Key exact checked interfaces

All names in this section have prefix
`YulangClosure.SimpleSub.LatticeDecision`. Types below use the existing
`Lattice` and `Regular.Comparison` namespaces for readability.

```lean
constructCertificate (graph : Lattice.Graph) : Lattice.Certificate

constructed_checked (graph : Lattice.Graph) :
  Lattice.checkCertificate graph (constructCertificate graph) = true

constructed_sound (graph : Lattice.Graph) :
  ∀ pair, pair ∈ Lattice.table (constructCertificate graph) →
    Lattice.RegularSub graph pair

constructed_exact {graph : Lattice.Graph} (valid : graph.Valid)
    (pair : Comparison) :
  pair ∈ Lattice.table (constructCertificate graph) ↔
    Lattice.RegularSub graph pair

regular_unfold {graph : Lattice.Graph} (valid : graph.Valid)
    (pair : Comparison) :
  Lattice.RegularSub graph pair ↔
    Lattice.Layer graph (Lattice.RegularSub graph) pair

decideDemands (graph : Lattice.Graph) (demands : List Comparison) : Bool
-- Definitionally: Lattice.accepts graph (constructCertificate graph) demands.

decideDemands_sound {graph : Lattice.Graph} {demands : List Comparison}
    (accepted : decideDemands graph demands = true) :
  graph.Valid ∧ graph.Guarded ∧
    ∀ pair, pair ∈ demands → Lattice.RegularSub graph pair

decideDemands_exact (graph : Lattice.Graph) (demands : List Comparison) :
  decideDemands graph demands = true ↔
    graph.Valid ∧ Lattice.checkGuarded graph = true ∧
      ∀ pair, pair ∈ demands → Lattice.RegularSub graph pair
```

`decideDemands_rejects_iff` is the exact negation of the last conjunction.
`decided_joint_relation` exhibits one common postfixed relation containing all
demands and included in `RegularSub`. The constructor/table soundness results
need no graph-validity premise; validity is computed by accepted demands and
is needed for the all-depth completeness proof's finite endpoint universe.

The guard remains the existing executable `checkGuarded = true`, rather than
an unproved equivalence with `Graph.Guarded`. No guard-checker completeness or
claim that every original source graph satisfies this guard is asserted.
Mathematical exactness of the constructed table itself requires validity,
not guardedness.

## Parent application and remaining owners

The parent can now instantiate the external certificate argument of the
existing lattice history/publication/growing-history consumer with
`constructCertificate graph`. Its terminal acceptance premise is exactly
`decideDemands graph last.obligations = true`, by definition. This is the
specific consumed reduction: the caller no longer supplies or assumes the
existence of a finite terminal derivation table. The public interface was
sent to the primary while it owned consumer integration.

This module does not depend on moving `SimpleSubLatticeInference` or
`SimpleSubLatticeGrowingInference`; it does not edit their assumptions.
The first original-source premises still have their actual owners:

- Native/source graph construction must faithfully preserve every actual
  type identity, lattice constructor, bound, polarity-specific copy, metadata
  and source/history event. Native success must yield the relevant terminal
  acceptance; a total decision procedure alone does not prove it accepts
  every successful original inference history.
- The existing guarded-fragment condition must be justified for the actual
  represented graphs where used. Original unguarded source syntax is not
  rejected or silently removed from the parent. Alias/open-row and ordinary
  coalescing correspondence remain separate from this exact fixed-graph result.
- History, lawful constructor completion, scoped publication inventory and
  metadata coverage remain the concrete consumer/source responsibilities.
  The primary's integration lane owns application to its final computed
  consumer; this producer does not assume those changing files.
- Full source derivation construction, complete Call and effects, original
  shared witnesses/scopes, original generalization/use and remaining native
  correspondence are still required for `SourceProblem.InferenceSoundness`.
  No accepted graph theorem replaces those obligations.

Mutual TODO `LD-CONSUME-1`: primary integrates the graph-only certificate into
its completed growing-publication theorem, preserving all existing metadata,
coverage, history and source premises. Falsifier: a new consumer still asks for
an external terminal certificate or drops an original shared-scope premise.

Mutual TODO `LD-NATIVE-1`: the native/source correspondence owner supplies the
actual graph/history/terminal-acceptance bridge for the unchanged original
source domain. Falsifier: a successful supported original history has no
faithful represented graph or has uncovered original demands. This request
adds no production algorithm, native checker requirement or write lease.

## Execution, resource bounds, and examples

The reference enumeration has `N = n_value² + n_effect²` pairs. Each inner
saturation has at most N shrinking-pending rounds; each outer construction
has at most N deletion rounds. All fuel is derived from actual finite lists,
not a caller-provided unfolding bound. The implementation binds the inner
certificate once per prune round and the final table once for extraction.

These are termination/round bounds, not a polynomial implementation-cost
claim. Linear-list lookup and repeated finite witness checking are used;
binary derivation trees can grow substantially. No production efficiency
or recommended native inference/search/coalescing algorithm is claimed.

The final source includes two `by decide` kernel-computed tests: lattice
injection succeeds and a genuinely unjustified union elimination fails.
The original recursive Function/union/intersection example is also proved
accepted by exactness; separately, actual execution computes it successfully
without receiving the old hand-written certificate.

`EvaluateDecision.lean` directly executes six cases: recursive lattice
acceptance; delayed recursive lattice/atom mismatch rejection; finite
injection; failed finite union elimination; unguarded lattice rejection; and
dangling-reference rejection even for empty demands. All six passed. This
execution is a bounded example check, not an additional theorem premise.

Native executable:
`/workspace/scratch/e41512dd7957/toolchains/lean-4.35.0-linux/bin/lake`.
Observed Lake `5.0.0-src+eb6cafb`, Lean `4.35.0`, release commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
The pinned copied project has no external packages. Every invocation has
`LEAN_NUM_THREADS=1`, `-j1 -M1024`, and a 120-second process-group timeout.
The exact native checker commands used sandbox escalation as authorized;
there was no installation, global change or auto-review rejection.

Budget spent: **9 focused checker/execution/audit calls plus 2 version calls**
(11 total invocations, within the maximum 18 even counting both versions).
Cumulative subprocess wall time: **35.786 seconds**. No timeout or resource
limit increase occurred. Task work finished within the 1,800-second envelope.
All material failed logs and their hypotheses/repairs are preserved:

| Log | Exit | Seconds | Evidence / repair |
| --- | ---: | ---: | --- |
| `check00-lean-version.log` | 0 | 0.165 | PASS: Lean 4.35.0, exact release commit recorded below. |
| `check00-version.log` | 0 | 0.064 | PASS: native Lake identifies Lean 4.35.0. |
| `check01.log` | 1 | 18.328 | FAIL: expected-type elaboration inferred the wrong predicate for List.find?_some. Repair: expose the find? equation and infer the lemma result before applying it. |
| `check02.log` | 0 | 1.179 | PASS: executable construction and complete accepted-output soundness. |
| `check03.log` | 0 | 1.842 | PASS: replace arbitrary inner rounds by shrinking-pending saturation and prove close_correct. |
| `check04.log` | 1 | 1.524 | FAIL: contradiction tactic did not reduce true/false equality in the generic find helper. Repair: explicitly simplify the known successful test in the failed-test equation. |
| `check05.log` | 1 | 3.285 | FAIL: dotted .trans had no expected type inside a change command. Repair: use Derivation.trans explicitly. Every other saturation case elaborated. |
| `check06.log` | 0 | 3.380 | PASS: all finite Layer completeness, all-depth exactness, derived reverse unfolding, and exact acceptance/rejection. |
| `check07.log` | 0 | 3.976 | PASS: final source, explicit computation sharing and two kernel-computed finite lattice examples; all 8 focused jobs. |
| `check08-eval.log` | 0 | 0.822 | PASS: six direct executable acceptance/rejection cases. |
| `check09-audit.log` | 0 | 1.221 | PASS: every one of 141 originating declarations, including all 95 theorem constants. |

The actual focused build command was `lake build
+YulangClosure.SimpleSubLatticeDecision`; execution and inventory used
`lake env lean -j1 -M1024 EvaluateDecision.lean` and the analogous
`AuditDecision.lean` command. Shared/default integration was not run here;
that cache and final import surface remain primary-owned.

## Complete originating-module audit

`AuditDecision.lean` enumerates constants by their actual originating module,
including private/generated declarations. It rejects project axioms, confirms
all 45 authored theorem roots, prints every declaration's full type and
transitive axiom list, and checks all dependencies against the standard
whitelist. It inspected **141 declarations**, including **95 theorem
constants = 45 authored + 50 generated/private theorems**.

| Axiom set | All declarations | Theorem constants |
| --- | ---: | ---: |
| none | 47 | 25 |
| `propext` | 56 | 32 |
| `propext`, `Quot.sound` | 38 | 38 |

There is no `Classical.choice`, `sorryAx`, project axiom, unchecked native
evaluation assumption or kernel bypass. The source scan of the exact
seven-module cone found no `sorry`, `admit`, axiom declaration,
`debug.skipKernelTC` or `native_decide`. A source scan is supplementary;
the originating-declaration audit checks the actual transitive dependencies.

Complete full types and axiom lists for **all 141 declarations**, not just
public theorem names, are preserved in `check09-audit.log` and in parsed
`declaration-inventory.json`. Every begin/end pair, declaration name and axiom
record was checked; all 141 names are unique, the 95 theorem begin/end sequences
agree, and the final counts match. These include all private generated match
identities, compiler equation theorems and omega proof helpers.

## Frozen source dependencies and artifacts

All six imported source modules match the assigned immutable dependency
snapshot and their isolated copies at freeze time. The accepted lattice
module retains its exact reviewed hash. The new file has 711 lines.

| Repository dependency | SHA256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `notes/theory/lean/YulangClosure/SimpleSubConstraintSyntax.lean` | `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6` |
| `notes/theory/lean/YulangClosure/SimpleSubConstraintSoundness.lean` | `33709d3978e8071708c10bba23d85b1b025c11dfd988220501acb7c6e3220293` |
| `notes/theory/lean/YulangClosure/SimpleSubRegularSolutions.lean` | `755d267714bd23bcfc17ec37d43d258392567b7d1356afc4897f541ae9855b29` |
| `notes/theory/lean/YulangClosure/SimpleSubRegularConstraintSoundness.lean` | `1d2266867115fc27afe39dbb80a3ca0e8f75247a2e16b739145137e83999de33` |
| `notes/theory/lean/YulangClosure/SimpleSubLatticeCertificates.lean` | `55533eee35ed7058abd125ac0e01d8f29b8c0534800018d254c1bd9f9c0bb79b` |

Own artifact and evidence hashes (scratch names are relative to
`/workspace/scratch/f98087c7ac1a/inference-lattice-decision/`):

| Artifact | SHA256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/SimpleSubLatticeDecision.lean` | `a9c184512bf6e23d15cc8a3a2ed230652fb168f707155e779be18c562d8e57c9` |
| `project/AuditDecision.lean` | `a40951abe62b0c1091b7ef2de692c7a367e39412eca05640db94d3a25241118d` |
| `project/EvaluateDecision.lean` | `2881ae9429566974c5f9c6d83294dd18d22a1434b9a455a609289ca12dc5e094` |
| `check07.log` | `120068b05d0512a1201e2774bdec2b748f946522d413dff33e7b4452cffe9eb7` |
| `check08-eval.log` | `fba340e8e484e2465b0721ba59f6f2dfc3ac272e3817cbab4a8693851670d89f` |
| `check09-audit.log` | `2d5dff142edf1488573f81b1b39f592026ea6f1bc81bf9a8d596eb15302273c8` |
| `declaration-inventory.json` | `8504a9d2c7e910e6bc2e4133acc371005f3914ab0ff69330b13cec04de8ced71` |
| `dependency-hashes.json` | `9681aff5556cf67ffb1869522e7d83f49753be7e06a5ed514374fbf9bba5904b` |
| `check.py` | `f2fa6601b4239f6fe9f019bed7ebad64eef1a332e0898555b50afc9a2ff5ff54` |
| `contract-observed.md` | `fc7e19978206c369a18d604fea4aefbf3eeadd4d104ea268dae8732d53c69b66` |

`dependency-hashes.json`, `artifact-hashes.json`, the runner, all check logs,
the isolated project and two inventory/evaluation drivers remain intact for
review. No dependency or unrelated cache was written after copying the pinned
inputs. The exact repository source and checked isolated source are byte-identical.

## Freeze and writer cessation

Revision 1 is ready for the assigned fresh nonauthor review. There is no
self-certification or production promotion. Primary owns acceptance,
consumer/import/audit integration, status synchronization, Git staging,
commit and push. The original parent remains OPEN with the precise source
premises above.

**All producer writes stop after this handoff is saved and its hash is sent.**
No descendants or unknown writer leases were created. The leased source and
this revision will not change during review without an explicit primary repair
assignment and a new handoff revision.
