# Function-bound value observation for callback adequacy

Question ID: `function-bound-value-observation`
Question revision: `q1`
Predecessor/history: none
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): `13378f6bf`; current source files are unchanged at question publication
Task/thread locator: unavailable; active goal is the Yulang inference replacement thread
Governing source/section: `notes/design/2026-10-04-source-generated-callback-structural-theorems.md` §§2.4–4; `notes/progress/2026-10-04-callback-local-abstraction-boundary.md` §§2, 4–6; `notes/design/2026-10-04-production-callback-endpoint-generation-draft.md` §4

## Requested scoped decision

For the complete Function bound used by callback adequacy, should observations retain exact concrete data-value identity/correlation, or should the bound compare typed observations that forget concrete data values while retaining value types, typed requests, continuations, and the existing `nu,K,D` incidence?

This question concerns the proof/denotation boundary for value endpoints. It does not ask to expose refinements in public schemes; the accepted criterion remains `zero : any -> int`.

## Background and current premises

- The user-directed principal criteria state that value-level dependencies must not be exposed as public refinements; `zero` has `any -> int`.
- Theorem C's complete-bound transport preserves the same complete observation and tuple under its constructed source graph.
- `notes/progress/2026-10-04-callback-local-abstraction-boundary.md` §2 proves that a bound depending only on grounded Function ports can contain an output value that the exact identity-body recipe does not produce. Its §4 gives a local integer-body saturation only for a projected first-order observation that forgets concrete input/output root equality; it does not identify this abstraction with production.
- The production callback draft §4 still lacks full-bound realization from the current Function endpoint to the Theorem C graph. It says this is not yet a demonstrated production counterexample or a settled semantic choice.

The unresolved distinction is whether exact value identity is part of the complete bound being transported, even though it is not part of the public type, or whether the callback bound itself uses the typed observation projection.

## Options and consequences

### A. Typed observation projection

Forget concrete data-value identity/correlation in Function-bound observations, while retaining value types, event/request data at its typed interface, continuations, provenance, and the same `nu,K,D` relationships. This gives the local saturation result a possible source-generation role, subject to proving the projection preserves all required callback observations. It is a weaker adequacy observation than exact source execution.

### B. Exact value observations internally

Keep exact concrete data-value identity/correlation in the complete bound used by callback adequacy, while still erasing it from public schemes. This preserves stronger internal observations but means the local saturation result cannot discharge full-bound factorization; production must retain and transport source-owned value relations or prove endpoint bounds already do so.

## Affected work

Blocked scope: selecting the observation relation for the full callback Function-bound factorization and using the scalar local abstraction as a production bridge.

Independent authorized work: source generation, structural regular completion, solver architecture, and implementation planning that does not assume either observation contract.

Required answer: explicitly select A or B for this callback proof/denotation boundary, or state a precise third contract and its retained observations. This answer alone does not authorize implementation; applicable theorem review and implementation gates remain.

Pending publication: keep this entire question directory unstaged and uncommitted until explicit approval of a displayed answer draft. Posting does not pause the active goal.
