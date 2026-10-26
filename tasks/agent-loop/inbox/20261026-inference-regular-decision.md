# Constructed terminal regular evidence

Producer: primary `/root`. Baseline `eb3eef2f6a29d9c2a6132d648866c60900db276c`.
Artifact: `notes/theory/lean/YulangClosure/SimpleSubRegularDecision.lean`.
SHA256: `6b6e5e6f1c45140d935e1aa29fba4c1303ae89cd91fd6e1cde0d37387148db8d`.

## Original parent and exact reduction

The full original `SourceProblem.InferenceSoundness` remains the parent. The
previous structural publication theorem consumed an independently supplied
finite terminal certificate. This module constructs that certificate from the
existing finite graph and proves it contains exactly the graph's independently
defined all-depth `RegularSub` comparisons. It does not change that relation,
the graph constructors, original source typing or the native inference algorithm.

The relevant source is the existing regular solution construction and its
concrete history/publication consumer, frozen at the baseline, under the
unchanged inference top-level principles and source-preservation obligation.
The theorem applies directly to those consumer declarations; it does not add
an opaque semantic `LocalLaws` package.

## Construction and theorem surface

`RegularDecision.allPairs` enumerates only well-indexed pairs of each kind in
the fixed graph. `pruneStep` filters the current list by the actual existing
`Regular.checkPair`; `prune` exits at equality or recurs with one less fuel.
Every changed round strictly decreases the list length. The initial length
therefore suffices to construct a postfixed certificate, including empty lists.

The complete semantic relation survives each filter: unfold one original
`RegularSub` comparison, use the same actual child list, and apply the inclusion
of all semantic children in the current list. Conversely the final postfixed
list is sound by the existing coinduction theorem. No model, stabilization,
termination, or desired comparison is supplied to these proofs.

Key checked declarations in `YulangClosure.SimpleSub.RegularDecision`:

- `prune_checked`: list length at most fuel implies the result passes the
  original finite certificate check.
- `constructed_checked graph`: the graph-determined `constructCertificate`
  always passes that check.
- `constructed_exact graph pair`: membership in the constructed certificate
  iff the unchanged `RegularSub graph pair`.
- `decideDemands_exact graph demands`: executable decision is true iff
  `graph.Valid` and every original demand is a regular comparison.
- `decideDemands_rejects_iff`: exact negation, with no termination assumption.
- `decided_original_demands`, `decided_store_history`: apply that generated
  evidence to the existing concrete transformation history and decoder.
- `decided_publication_with_clients`: the existing original publication and
  all included clients share one reference assignment, with no certificate
  parameter or existential evidence-generation assumption.

The last theorem still has the same explicit finite inventory coverage,
successful decoding, concrete history, capture/allocation closure and endpoint
decision premises. Actual native success implying these premises remains OPEN.
Changing an input certificate into a computed certificate does not prove that
an arbitrary terminal graph/demand is accepted.

## Concrete checks and resource meaning

Kernel-reduced examples construct evidence for two cyclic Functions with all
four ports, reject a recursively exposed result-atom mismatch, reject an exact
optional-bit mismatch, and reject dangling references even for empty demands.
There is no `native_decide` or unchecked evaluation premise.

This is a reference construction, not a production solver change or mandatory
runtime validation pass. It enumerates N = n_value^2 + n_effect^2 pairs, stores
at most N of them, and performs at most N strict deletion rounds. Each round
checks actual expansions and uses linear-list membership. No efficient native
complexity claim is made, and no alternative typings are searched. Native
certificate extraction can later use the already proved acceptance interface.

## Verification

Own isolated project/cache: `/workspace/scratch/f98087c7ac1a/inference-decision`.
Native Lake: `/workspace/scratch/e41512dd7957/toolchains/lean-4.35.0-linux/bin/lake`.
Observed Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
All calls use `LEAN_NUM_THREADS=1`, project `-j1 -M1024` and 120-second timeout.

| Call | Result | Seconds |
| --- | --- | ---: |
| `check-01.log`, focused build | exit 1: parent `Certificate` name collision and reserved `universe` identifier | 25.932 |
| `check-02.log`, focused build | exit 1: one stale lemma reference after renaming | 1.733 |
| `check-03.log`, focused build | exit 0, all 10 jobs | 1.683 |
| `audit-04.log`, complete originating-module audit | exit 0, 37 theorem constants | 1.227 |

The complete audit includes **23 authored + 14 generated/private theorems**.
All printed types and axiom lists were inspected: 3 empty, 10 only `propext`,
24 `propext, Quot.sound`. No `Classical.choice`, `sorryAx`, project axiom or
kernel bypass occurs. Source scan is clean. Audit SHA256:
`fd6c65380c74a699d88dc498abdea295c2ae9463b7e0733ea6370615ea9914e5`.
The audit driver is `DecisionAudit.lean` in the isolated project; material
failure logs remain beside it. No dependency, global configuration, native
compiler or existing Lean source changed for this packet.

## Boundaries and handoff

The graph interpretation still has exact closed finite carrier metadata and
guarded structural cycles. It does not contain lattice/alias nodes, native open
rows, width/presence weakening, ordinary coalescing or full source Call/effect
meaning. Native history/graph production and the original shared source
witness are not inferred from this finite algorithm. Full inference soundness
remains OPEN; the next consumer is constructive graph completion followed by
faithful native serialization/history correspondence.

Source and handoff are frozen for independent non-author review. No owned
checker process remains running. Primary integration/status duties continue
on separately owned paths.
