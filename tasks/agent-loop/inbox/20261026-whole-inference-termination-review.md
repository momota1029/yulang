# Independent review: original inference termination local descent packet

Date: 2026-10-26
Reviewer: `/root/effect_hygiene`, nonauthor of the reviewed termination module
Decision: **ACCEPT for the stated local results and their explicit boundaries**
Blocking / major / minor findings: **none**
Original whole `SourceProblem.InferenceTermination`: **OPEN**
Production/compiler semantics: unchanged by this review

## 1. Exact reviewed snapshot

| Artifact | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/OriginalInferenceTermination.lean` | `26aca31b41897e297e516bf98b6e11d63dab50482a69f5b8a1f98a739696f946` |
| `tasks/agent-loop/inbox/20261026-whole-inference-termination.md` | `002b8517716004c5949be71751f746eeb1e1d1f29ff7022561ba351201469cf1` |
| Isolated `AuditOriginalInferenceTermination.lean` | `038ace8c8b71a55d9d6b356c77d3b27b888dd860e2a0e7cbf542023283c18685` |
| Isolated `census-original-termination.log` | `f8e0da741b6b507433d3dcf174b27c133bd6f95a54572e535ea9a2ebaa0d56f4` |
| Isolated `check-original-termination.log` | `73c3c899a35505eddddd0b9096de9750293a42651c2efc432bc17277afd129d5` |
| Isolated `termination-dependency-hashes.json` | `7ecba3cbd0f37941613691e90e46433737fd3baa5f53ffad3e7d9096e443c9b7` |

The isolated evidence directory is
`/workspace/scratch/e3678bef96db/lean-termination-work`.
All thirteen proof/dependency module hashes match the manifest in both the
repository and isolated copy. Eleven of the twelve source/authority/configuration
hashes also match. The sole difference is the primary's announced integration
addition of `YulangClosure.WholeMetatheory` to the Lake target globs; current
`lakefile.toml` hash is
`e62c909702ea210955e7d4b1c5d19991a1997a96990f70eb398f3044a479b56d`.
That intended integration edit does not change the producer's verified snapshot
or the reviewed theorem/dependency bytes. No source drift was found.

The reviewed work is disjoint from my earlier Effect hygiene authorship. This
receipt does not independently certify my own Effect hygiene module.

## 2. Scanner descent, rejection, and exact total outcome

I inspected the complete 416-line module, complete producer handoff, all 28
authored theorem types, all 47 further originating/generated theorem types,
and the definitions used at the critical imported boundaries.

`scanStep_decreases` applies to the existing
`NativeContextExpansion.scanStep t s = some u` and concludes strict decrease of
the pending-stack sum of `3^id`. It has no hidden successful-transcript, finite
table, acyclic-table, finite-universe, or source-typing premise. The cases are
exhaustive:

- Identity and already-visited entries remove one positive summand, including
  `id = 0`, for which the summand is one.
- Prefix, Swap, and Without succeed only with `input < id`, and replace one
  summand with a strictly smaller one. Prefix's mode and weight validation
  remain the existing scanner guards.
- Replay checks both strict child bounds. The genuine arithmetic inequality
  `3^left + 3^right < 3^parent` accommodates repeated children without requiring
  disjoint subgraphs or a visited invariant.
- Missing table entries, invalid guards, Suffix, and Both reject. They do not
  produce a successor that would need an unproved descent fact.

The nonzero parent needed by the power argument follows from a strict child
bound; it is not an omitted extra hypothesis. `pendingRank_zero_iff` correctly
handles the empty and nonempty cases.

`scanStep_wellFounded` uses the proved subrelation of natural-number descent.
`scanTotal` recurses only on that exact scanner successor, and its termination
obligation is discharged by `scanStep_decreases`. Thus its well-foundedness is
not circular. `scanLoop_eq_total` proves a sufficient fuel bound by induction,
with the zero-fuel case forcing an empty pending stack. Stabilization applies
to rejection as well as success. `parse_stable` uses `3^root` as proof-side
fuel; it introduces no native allocation limit or supported-source cap.

`scanTotal_success_iff` has both directions. The forward direction obtains an
existing `ScanRun` through the sufficiently fueled checker; the reverse
direction follows the actual run constructors. Separately,
`scanTotal_execution` constructs a finite execution for every input, including
validation rejection and empty-stack final rejection. It does not assume the
finite execution it concludes.

The varying-table relation existentially quantifies the observed `Tables` at
each successful step. Since the same stack measure decreases for every table,
it proves descent even when observations change between steps. It does not
model or bound intervening table mutation/allocation events themselves, and
the packet makes no such inference.

## 3. Source owner comparison and callback boundary

I compared the scanner projection with
`crates/yu-solver/src/candidate_context.rs:3669–3766`, including the actual
stack pushes, child-ID checks, mode changes, weight/view checks, duplicate
filter handling, and final mixed-filter rejection. Native Replay pushes upper
then lower, matching the Lean next-pop list order lower then upper. Rejecting
Suffix/Both matches this specific parser's supported fragment; it does not
restrict the language-wide source domain.

The scanner proof ends before post-scan resource sampling, installation of
`checking_filters`, and `consume(self, &filters, residual)`. It does not prove
that callback terminates. Native reservation failures can exit earlier and are
outside the pure scanner projection. The result is an exact statement about
the existing Lean scanner projection, supported by this source comparison;
this review does not manufacture a formal Rust operational-refinement theorem.

I also inspected `run_candidate_typed_drain` and relevant `step_typed_drain`
control in `lib.rs:14235–14420`. The enclosing loop can return `More`, reenter
Transport, settle intrusion, and receive additional work. Its termination does
not follow from this local scanner rank. The producer prominently preserves
that distinction.

## 4. Constructed topology, cancellation, and ready-marker order

The topology proof reuses the existing interner formation lemma and actual
`NativeContextTables.Step.context` constructor guard. On a fresh insertion,
the prior vector length becomes the new zero-based index, and the stored ID is
that index plus one. Thus `child ≤ oldLength` yields the required strict bound
against the new ID. Cached nodes retain the prior invariant. Every other Store
step preserves the Context vector.

I inspected `Store.contextAt`, `Store.tables`, `Store.intern`, `intern_values`,
`contextInputs`, `ContextsFormed`, `context_preserves_formation`, all Store step
constructors, `Run`, `History`, and `cancellation_vectors`. Cancellation restores
the saved Context vector, so it restores its proved topology. Subsequent fresh
insertion again uses the retained frontier; numerical ID reuse does not break
the child bound. The readback proof explicitly excludes `id = 0` before
converting `child ≤ id - 1` to `child < id`. Both Replay children and all six
stored constructors are covered.

The finite `History` premise is used for topology preservation, not as a claim
that every complete inference history is finite. In particular,
`native_context_scan_accessible` needs no `History` argument at all: arbitrary
table inputs are already handled by the scanner's own guards.

I compared the other traversal projection with native rename
(`candidate_context.rs:1566–1660`), payload discovery (`1696–1724`), and fold
(`1739–1784`). The ready-marker rank gives each unready frame `4^id` and each
ready marker one. The proved two-child inequality leaves room for the ready
marker. Filtering removes nonnegative contributions, and reversal preserves
the rank. The logical next-pop orders are accurate:

| Native owner | Projection settings and resulting order |
| --- | --- |
| Fold / rename | `ready = true`, `backwards = false`; filtered children in constructor order, then the parent ready marker, then the old stack |
| Payload discovery | `ready = false`, `backwards = true`; reverse constructor order after native `extend_from_slice`, with no parent marker |

Identity and memo hits are pops. Completed callback processing is also a pop;
the relation does not model the callback's internal execution. The projection
allows more actions than each specific native owner, including a Both descent
that payload discovery rejects. This is valid for its explicitly stated role
as an overapproximation of successful stack actions. The Rust-to-projection
refinement, callback termination, and repeated invocation over newly discovered
roots remain separate obligations. No premise hides those obligations inside
an assertion of whole inference termination.

## 5. Negative projection theorem and unchanged original goal

`drain_projection_not_accessible` directly uses the existing unrestricted
`NativeDrainOwnership.Step.reserveOther`. Every abstract state has another
such successor, so accessibility of that event-conservation relation is
impossible. The proof introduces no transition and no hypothetical source
program. It is correctly presented as a reason that this abstraction cannot
serve as the terminating inference relation, not as native divergence evidence.

The original target remains the exact `Contracts.lean:152–154` statement:

```lean
∀ s x n, p.supported s → p.inferInitial s x n →
  Acc (fun next prev => p.inferStep prev next) n
```

I found no concrete `inferInitial :=` or `inferStep :=` assignment in the current
Lean tree. This packet supplies neither an authentic whole-source transition
instance nor global progress across allocation, callbacks, Replay, extrusion,
intrusion, capture, and generalization. The original supported-source domain,
rejection paths, recursion, and current birth-level SCC qualification are not
weakened. No evaluation-termination claim is made.

## 6. Checker evidence and trust boundary

I inspected the producer's native Lean 4.35.0/Lake version receipts, successful
14-job focused build, and 16-root named checker output. I inspected the complete
census program: it selects theorem constants by originating module index,
rejects originating axioms, requires all 28 authored roots, prints complete
types and axiom dependencies, and rejects dependencies outside the permitted
standard Lean set. Its inventory includes private/generated constants even
when their printed names are in imported namespaces.

Independent log parsing confirmed 75 unique BEGIN/END pairs in matching order,
75 corresponding axiom records, and inclusion of every authored root. Exact
dependency sets are 20 empty, 5 `{propext}`, and 50 `{propext, Quot.sound}`.
There are no `Classical.choice` dependencies in this module census and no
unapproved axiom reports. The absence of project axioms/proof holes is supported
by the checker and its complete dependency checks, not merely a text search.

No concrete checker or dependency risk required another Lean invocation, so I
did not redundantly rebuild or rerun the audits. This is an independent source,
statement, correspondence-boundary, and evidence review; it does not relabel
producer execution as reviewer execution.

Not independently re-proved or tested here: the complete imported theorem
corpus, Rust operational semantics, runtime allocator behavior, arbitrary fold
callbacks, actual source-to-native inference refinement, and global inference
termination. No Cargo or whole-project integration build was run by this
reviewer. These exclusions agree with the accepted packet's stated scope.

## 7. Decision and stopped receipt

**ACCEPT** the frozen local descent, total scanner, topology, traversal-control,
and negative abstraction results. Apply them only at the corresponding local
premises; keep original whole inference termination and its concrete native
instance gate **OPEN**. No producer repair is required by this review.

**Writes stopped.** The sole write in this review is this receipt. No source,
dependency, configuration, shared status, or Git mutation was performed. No
child agents were created, and no subprocess or background write remains.
The reviewed source and handoff are frozen at the hashes above; any later
change to those artifacts requires review of the changed snapshot.
