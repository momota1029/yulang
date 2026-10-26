# Guarded regular structural solutions from finite certificates

Date: 2026-10-26. Producer: `/root/paper_allocation_execution`, generic
`lean_prover` fallback. Assigned baseline:
`0f6346a2de0a8bff863f41d487eb4b29cf8fb5f3`.

Status: concrete construction checked by Lean 4.35.0; complete originating-
module type/axiom audit passed. Independent review and integration are
primary-owned. This supplies regular structural solutions from successful
finite certificate checking, without an assumed final valuation. Original
source inference soundness and native certificate production remain OPEN.

## Frozen artifacts

- Source: `notes/theory/lean/YulangClosure/SimpleSubRegularSolutions.lean`.
  SHA256 `755d267714bd23bcfc17ec37d43d258392567b7d1356afc4897f541ae9855b29`.
- Isolated cache/logs: `/workspace/scratch/f98087c7ac1a/inference-regular/`.
- Direct project dependency: frozen `SimpleSubConstraintSyntax.lean`, SHA256
  `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6`.
- Prior `SimpleSubConstraintSoundness.lean` remains unchanged at SHA256
  `33709d3978e8071708c10bba23d85b1b025c11dfd988220501acb7c6e3220293`.

No existing source, compiler, root import, manifest, shared record or Git
state was edited. No children were launched.

## The missing premise addressed

The earlier forward constraint theorem assumes a satisfying valuation of
the final retained store. Its valuation returns finite `Term`s, with no
`mu`, and therefore does not establish existence of a model for recursive
native graphs. This module constructs a different, explicit regular
structural interpretation directly from finite graph/certificate data.

The main theorem does not take a model, a subtype derivation, or a local
preservation law. Its input is the Boolean result of a finite checker
whose branches inspect graph references, metadata and certificate closure.
The independently defined conclusion is compatibility at every finite
unfolding depth, including arbitrarily repeated structural cycles.

## Exact mathematical construction

Namespace: `YulangClosure.SimpleSub.Regular`.

`Graph := (k : Kind) → List (Node k)` consists of two finite, kind-indexed
node tables. A `Comparison` retains kind, lower node identity and upper node
identity. Supported nodes are unchanged atoms, bottom, top, four-port
Function, whole finite records, whole finite tuples and whole finite variants.
Function child order is `(argument, argumentEffect, resultEffect, result)`;
the first two comparisons reverse and the last two preserve direction.

Records store a complete finite `List Field`, retaining label, optional bit
and child identity. Variants store a complete finite `List Alternative`,
retaining tag and the whole finite ordered payload list. Cycles can pass
through field/payload children; no cyclic row spine is used to manufacture
infinitely many record fields or variant alternatives.

`expand graph comparison` determines the immediate recursive demands from
the two actual looked-up constructors. It returns `none` for missing
endpoints, wrong constructors, incompatible atoms, different record metadata,
tuple/payload arity mismatch or different variant tags. It produces no
children for bottom/top or identical atoms. Whole record and variant lists
must match in order and metadata for this structural case; this is not a
complete width/optional-row or variant-admission algorithm.

The independent semantic relation is:

```lean
Layer graph relation pair :=
  ∃ children, expand graph pair = some children ∧
    ∀ child, child ∈ children → relation child

Approx graph 0 pair := True
Approx graph (depth + 1) pair := Layer graph (Approx graph depth) pair
RegularSub graph pair := ∀ depth, Approx graph depth pair
```

`coinduction` proves every postfixed relation is included in `RegularSub`.
`regular_unfold` proves that `RegularSub` itself unfolds to one shared child
list satisfying `Layer graph (RegularSub graph)`. Determinism of `expand`
identifies that same finite child list at every depth. Thus the semantics is
the greatest fixed point of the represented structural operator, rather
than a proposition defined as checker acceptance.

The checker separately executes:

1. `checkGraph`: every reference resolves at its declared kind, and record
   labels / variant tags are unique. This checks the whole finite graph,
   including children that bottom/top comparison would otherwise skip.
2. `checkCertificate`: every retained pair expands successfully and all of
   its immediate children occur in the same finite certificate table.
3. `accepts`: both checks above hold and every demanded pair is retained.

`certificate_sound` derives regular comparison from finite closure checking.
`accepted_joint_relation` constructs one concrete postfixed relation
(membership in that exact certificate) covering all demands together, along
with graph validity. This is shared structural pair evidence; it does not
replace the original source-scoped joint Call/effect strategy.

## Main checked types

With the namespace shortened:

```lean
accepted_demands_sound :
  ∀ {graph certificate demands}, accepts graph certificate demands = true →
    ∀ pair, pair ∈ demands → RegularSub graph pair

accepted_all_depths :
  ∀ {graph certificate demands}, accepts graph certificate demands = true →
    ∀ depth pair, pair ∈ demands → Approx graph depth pair

accepted_joint_relation :
  ∀ {graph certificate demands}, accepts graph certificate demands = true →
    graph.Valid ∧ ∃ relation,
      (∀ pair, relation pair → Layer graph relation pair) ∧
      (∀ pair, pair ∈ demands → relation pair) ∧
      (∀ pair, relation pair → RegularSub graph pair)
```

No successful native execution, final solution, interpretation law, graph
well-formedness proposition or postfixedness proposition is assumed by these
three theorems. Graph validity and postfixedness are derived from the actual
finite Boolean checks. `coinduction` has its usual postfixed premise, but
the accepted-certificate result supplies that premise constructively.

## Checked cyclic and rejection examples

`mixedCyclicGraph` has ten value nodes and two effect nodes. Two distinct
recursive Functions return records. One record field passes through a tuple
and a variant payload back to the original Function; the other field refers
back to its own record. The four Function ports require the proper
bottom/top comparisons, including both effects. A six-pair certificate
passes by kernel reduction.

- `mixedCyclic_accepted` computes acceptance.
- `mixedCyclic_regular` proves the root regular subtype relation.
- `mixedCyclic_all_depths` proves every finite unfolding depth.
- `mixedCyclic_missing_effect_rejected` rejects a certificate retaining all
  value pairs but omitting the required effect pair.
- `mixedCyclic_reverse_rejected` rejects the reversed comparisons.
- `optional_mismatch_rejected` rejects differing presence metadata even when
  both record graphs are recursively self-referential.
- `dangling_graph_rejected` rejects a missing Function child even though the
  immediate demanded comparison starts at bottom.

General `missing_demand_rejected`, `broken_pair_rejected`, endpoint existence,
lookup validity and constructor-expansion theorems are also proved.

## Source and native acceptance inspection

Governing sources were the inference top-level principles, immutable
birth-level correction, original source-preservation claim, and the exact
paper import in `2026-10-11-parreaux-simple-sub-proof-import.md` §§3–5.
That import distinguishes ordinary positive/negative coalescing from the
unifying interpretation used in the soundness proof, and records Fig. 10's
guarded recursive-hypothesis discipline. This construction has no alias-only
nodes or union/intersection cycles. It does not certify unrestricted
coinductive self-justification or unifying/ordinary coalescing equivalence.

Fresh primary-source access was attempted: the old local PDF and Scala path
do not exist in this environment. The author's
[ICFP 2020 page](https://cse.hkust.edu.hk/~parreaux/publication/icfp20/) and
[original explanation](https://lptk.github.io/programming/2020/03/26/demystifying-mlsub.html)
were read, confirming the paper link and the recursive/coalescing route.
The author's preprint link redirects to EPFL. EPFL PDF retrieval failed
with a provider redirect / 429; the publisher PDF returned 403. Thus the
formal Fig. 10 / unifying-coalescing details were inspected in the pinned
repository import, not falsely reported as a freshly fetched full PDF.

Actual Rust owners inspected:

| Owner | Observed behavior and implication |
| --- | --- |
| `lib.rs`: `SolvedModule::solve`, `InferenceSession::run`, `finish`, `errors` | `Result::Ok` is availability completion; `finish` preserves `data.errors` and exposes them separately. It is not already successful type inference. |
| `lib.rs`: `run_candidate`, `finish_candidate` | Candidate completion additionally rejects unresolved active field-tail selection. No semantic regular-model certificate is supplied by this return type. |
| `shadow_apply.rs`: `CandidateInference.export` | Public graph export rejects nonempty final errors, verifies root ownership and obtains the actual retained graph. This is a concrete consumer to target for native correspondence. |
| `shadow_apply.rs`: `fresh_use`, `selected_field_tail_uses`, `operator_fresh_uses` | Final no-error gates and authentic retained-use/provider ownership are checked separately from availability. |
| `shadow_apply.rs`: `operation_v1_field_bounds` | A receipt requires both consumed evidence and final absence of solver errors; a drained local edge alone is insufficient. |
| `f5c_generalization.rs`: `GeneralizationDraft`, `F5cRecursiveBound`, `build_component_with_bound_sidecar` | Explicit recursive binder/lower/upper data and memo/transaction completion remain native owners. Their semantic soundness is not obtained from scratch-empty assertions. |
| `lib.rs`: `finalize_generalization_draft_raw` | Recursive ordinals and constructor serialization are checked; the legacy Function serialization supplies empty/bottom effect ports. It is not identified with a faithful full-four-port decoder. |

The checker is a proof construction, not a new runtime validator mandated
by fiat. A future proof may extract its finite relation from existing native
memo/worklist evidence and prove acceptance without changing compiler
behavior. No native code was changed here.

## Verification

Pinned native Lake path:
`/workspace/scratch/e41512dd7957/toolchains/lean-4.35.0-linux/bin/lake`.
The established Lean 4.35.0 binary was used with `LEAN_NUM_THREADS=1`,
`-j1 -M1024`, one owned Lean process at a time, each call bounded by 60s.
Five focused build/audit calls consumed approximately 15.9 seconds.

| Log | Result |
| --- | --- |
| `check-01.log` | Exit 1: dependent Node pattern needed an explicit kind-indexed helper. Repaired by defining `expandNodes`; no semantic claim changed. |
| `check-02.log` | Exit 0: independent semantics, checker and whole-graph validation. |
| `check-03.log` | Exit 1: after dependent lookup cases, endpoint witnesses needed reflexive equalities. |
| `check-04.log` | Exit 0, 3.780s: complete module dependency build, including cyclic examples. |
| `audit-05.log` | Exit 0, 4.190s: complete actual originating-module theorem audit. |

Successful build command:
`lake build +YulangClosure.SimpleSubRegularSolutions`.
Audit command:
`lake env lean -j1 -M1024 RegularAudit.lean`.

All **134 theorem constants** passed exact-type and axiom inspection,
including **33 authored public theorems** and **101 generated helpers**.
There are 134 matching begin/end receipts. All authored printed types were
inspected. Axiom sets: **45 empty**, **64 `{propext}`**,
**25 `{propext, Quot.sound}`**. No `Classical.choice`, `sorryAx`, project
axiom or bypass occurs. Source search found no holes or unsafe/checker
bypasses. Default integration and non-author review remain primary-owned.

| Evidence | SHA256 |
| --- | --- |
| `RegularAudit.lean` | `e1ed9c45cc93ea0e772db46903a8d1ff5244c1cc6ffa1c999f5f2e97fdca0474` |
| `audit-05.log` | `6846c750c69cea3dbbf7ab69cc0ddbb0107d8131f8c9b357844fcdfc278e62bb` |
| `check-04.log` | `68b5b94505d9b84d121690da56819bb02cda275be5f9e11bb233b7900626583c` |

## Application to the original inference path and first remaining bridge

For a real accepted native export, the next proof must decode its actual
guarded structural graph and comparison roots while preserving row kinds,
four Function ports, constructor identity, complete finite fields/payloads,
aliases and the actual original demanded comparisons. It must extract or
construct a finite closed comparison table from the actual successful native
constraint evidence and derive `accepts = true`. Then
`accepted_joint_relation` constructs the regular structural solution; this
step no longer needs a supplied final model.

`RegularSub` is distinct from the frozen finite `Sub` relation. It cannot
be passed to `History.sound` as a fabricated finite-Term valuation. Extending
that reflection route to regular interpretations, or proving an exact
decoded-native-demand interpretation theorem, is an explicit next bridge.
Union/intersection coalescing, unguarded row-bound cycles, complete Call and
contextual effect semantics, source generation, publication/generalization,
required principal coverage and termination remain original obligations.
Their scope is unchanged; no smaller theorem replaces the original root.

Writes stopped after this handoff. Source is frozen at the hash above. No
Lean process remains running. Prior proof artifacts and all other repository
paths remain untouched.
