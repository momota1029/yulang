# Ordinary-extension transport of source dictionary evidence

Status: Verified and published in work/dots-main at ae519000b1235124a7b1b9d2bfdfb43cc38a295c after the I-24 audit-shard migration. Date: 2026-11-12.
Scope: I-23, dictionary Evidence only. Astra transitions and source semantics remain unchanged.

The recorded-instance theorem retains each packet's original inspection context. The target Evidence uses the final context. A transition preserving only models does not by itself preserve inspection, canonical child allocation, or source readback. In particular a certified refresh can change nominal observations, so it cannot be silently handled as an ordinary extension.

This cycle isolates a genuine exact case, for arbitrary registries, contexts, occurrences, model assignments and raw dictionary payloads: extend only the reserved identity list, ordinary atom list and allocated-origin ledger. The base carrier, normalized observation, nominal descriptors, allocation seed and constructor interpretation are unchanged. The proved theorem is that source Instance/Evidence in the extended context is equivalent to the original Instance/Evidence together with satisfaction of the added ordinary atoms. The same payload, actual output equations, source identities, canonical ordered children, and multiplicities must remain intact.

Inspection/allocation invariance and branch-model equivalence lift to Instance and recursively to the existing Evidence. The actual recorded terminal packet has same-final-context Evidence exactly when the final state has a model; both a positive model and the output-equation negative model are checked. An installed feedback parent retains its real ordered generated child. This is transport, not the choice of a new Evidence predicate or a new fragment classifier.

Remaining obligations: actual descriptor-changing refresh; joint compatibility of the selected branch with a whole journal; complete classification of joint alias classes. V4's EvidenceNode still quantifies all stable states, not merely SourceFormed states. Stability cannot be used to infer Joint circularly: Installable itself requires Joint. The raw JournalObstruction is not a Stable counterexample; the separate Stable inconsistent journal cannot refute model-indexed EvidenceNode.

The V4 structure has thirteen fields (GeneratedChildren was added), not the old V3 count of twelve. No new complete concrete B4 or unconditional EvidenceNode is claimed by this work.

Yulang2: the existing work/dots-audit x-oracle was reread at `55574b60`. It has no direct oracle for internal journal/context transport. The new law is a theorem about unchanged Lean source semantics, not an imported Yulang2 behavior. No new Yulang2 execution is claimed.

## Actual transition connection

Installation extends reserved IDs, ordinary atoms and the allocated-origin ledger. Enqueue leaves the context fixed; merge and equality feedback append atoms. These actual constructors therefore fit the exact Extension relation. OrdinaryStep is the conjunction of Astra's existing Step and this syntactic Extension relation, not a replacement transition. A finite OrdinaryStep trace must imply both a real feedback trace and the composed context extension. Instance/Evidence transport then gives same-final-context evidence, rather than only the packet's stored context. Descriptor-changing refresh is deliberately not given an Extension lemma.

## Verified ordinary scope

The first three new modules contain 36 public theorems. Focused `lake build --wfail` passes (635 jobs); the scoped 36-theorem `lake env lean --trust=0` axiom audit passes. Standard `propext`, `Classical.choice` and `Quot.sound` occur; no `sorryAx` or new axioms. No full build or full Audit was run.

`Installable` supplies journal compatibility, not the generated-focus/novelty premises of the first installation step. `installed_trace_execution` includes both premises explicitly to give an actual complete feedback trace. The current-context Instance/Evidence results separately require the actual install-function output and an ordinary actual-step tail, and keep the same final model throughout. They do not assert arbitrary descriptor-refresh preservation, stable selected-branch Joint, or closure of EvidenceNode.

## Concrete descriptor refresh and I-24 migration

A fourth module `GeneralDictionaryRefreshCurrentEvidence` proves four further theorems for the existing actual descriptor-refresh fixture. Its parent Instance uses `refreshedContext`, not the packet's old context. It observes the unchanged parent list interval while the generated child's nominal descriptor changes. This does not prove arbitrary refresh invariance or the child's complete dictionary. Focused `--wfail` build passes (637 jobs), direct trust-zero and scoped four-theorem axiom audit pass.

During the cycle a fresh inbox read found I-24 at integration commit `5c14c61f`: freeze Audit.lean and move pending audits into small files. All unpublicized audit additions from 131–135 were preserved in `Audit/Recovery131135.lean`; the 40 new audit declarations are in `Audit/Cycle136.lean`. The frozen Audit is byte-identical to integration. No retry of the earlier unresolved large blob creation is used.
