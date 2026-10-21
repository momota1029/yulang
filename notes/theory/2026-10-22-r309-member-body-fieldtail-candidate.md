# R309 — Member body and deferred FieldTail candidate path

Status: ACTIVE, solo Luna primary, unreviewed. Parent R149 remains OPEN.
Baseline: `0408581b505b874a808a9c45ed8ae889436923f2`.
Contract: `tasks/agent-loop/sprints/r309-member-body-fieldtail-candidate-20261022.md`.

## Governing design and proof material read

Re-read the converted unified design §§4.1–4.5, 6.1–6.8, 9 stage 4, and the proof companion §§3.6–3.8, 4.5, 7.1–7.3. The design requires semantic identities, typed endpoints and payload to travel together; member/method selection remains a delayed obligation until relevant bounds settle. Capture/FreshUse results apply only to records included in the graph and to source constructors whose premises have been established. The effect annotation correction remains active: contravariant `[io]` means `[io,'e]`, so `[state]` alone is not a violation.

## Starting evidence

R302 carries an exact FieldTail source occurrence, authenticated role-member candidate IDs, receiver/result Value and Effect rows through Capture and one FreshUse map. Its receiver probe exposes an ordered two-element tuple with Int and String lower facts. R303 carries original role/implementation member identities, headers and RHS source, but ordinary candidate scheduling lacks Member roots and its value graph rejects them. R303 also records two source-form obstacles in pinned `Display`: the role default body has an imported operator chain, and the ordered-pair implementation has tuple-pattern binders. R308 resolves the selected imported `+` provenance and exact provider body but deliberately does not lower or type it.

Current core owners confirm the seam: `SourceRootId::Member` is distinct from Definition/Expression; `LocalSource::form_ordinary` receives no member receiver parameter; `CandidateValueGraph::retain_source` rejects Member; candidate publication is Definition/Expression-oriented; `DeferredFieldTail` retains four rows but always blocks finalization. No selected implementation or body constraint is currently established.

## R309 question and evidence standard

Can the exact member receiver/header/body enter candidate inference as a source-owned method candidate, and can the corresponding FieldTail consume it only when the same inference session has enough receiver-bound information to establish a stable unique selection?

Evidence must join declaration/member SourceNodeKeys, exact receiver binder and annotation, body source occurrence, candidate root/parameter identities, generated constraints, scheme/capture rows and FieldTail occurrence. Wrong role/implementation owner, stale/recovered source, missing receiver, late-arriving incompatible receiver bound, ambiguous member and unresolved nested `show` must not become successful finalization. Source spelling alone and one tuple observation are not candidate-selection proofs.

## Proof obligations

For each admitted member body, establish the source constructor-to-receiver-parameter map, body expression occurrence lineage, constraint-generation correspondence and exact endpoint relation to the member's declared receiver/result/effect ports. For each FieldTail consumer, establish that all four rows share one owner/use mapping, and identify all updates that can change receiver conformance or nested obligations. A selection is publishable only under a stability condition preserved by every later legal update; intermediate source-action quiescence is insufficient. If the current inference lifecycle has no such condition, retain the pending obligation and report that exact gap.

The proof companion's Capture and fresh-copy results may justify the already-present row transport after its source-to-record premises are shown. They do not prove Member registration, receiver binding, member typing, a role implementation match, source completeness or runtime correspondence. Do not infer the parent theorem from test passes.

## Implementation route and falsifiers

Use authentic member IDs and the existing `SourceRootId::Member`; never mint an ordinary top-level definition. Build receiver input from the exact member header, not a guessed name. Keep member candidate roots separate from ordinary module execution while giving candidate collection and value-graph traversal enough owner information to connect the receiver parameter and body. Preserve ordered tuple pattern projection and use R308's imported operator source receipt only as an exact declaration/body link; no spelling rewrite. Store unresolved method selection with the existing FieldTail four-row bundle, and make every relevant bound update visible to its readiness check.

Falsify this route if an ordinary Member body is inserted into top-level execution, receiver parameter is disconnected from the member source, any Value/Effect row is dropped or aliased across FreshUse, operator body is selected without provenance, tuple binders share the whole scrutinee instead of ordered component rows, a later bound can invalidate a published choice, or a method returns success while its nested FieldTail remains pending.

## Current state and limits

No R309 implementation changes are made at this entry note. Exact leases and 1800-second solo cap are in the R309 contract. One Cargo process at a time; no subagents. Types/Console unchanged execution, source/native proof, A/B, principality, termination, independent review and production remain OPEN. R149 remains OPEN.
