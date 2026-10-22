# R330 — Console role frontier and member projection

## Initial source trace

In the focused unchanged Console readback, the `value.show` receiver and `where 'a: Display` subject are distinct value rows. At the completed source schedule, both rows have the same four exact `IntPositive` lower atoms. Each row has a single direct upper edge to the other, with no exact upper atoms. The imported route maps the subject to the `Display` obligation and the receiver to the FieldTail in one FreshUse. The frontier counter starts at the receiver, follows positive lower rows, and counts only the receiver's upper edge; it does not traverse the reciprocal edge, so the old gate reports one negative row edge.

This is evidence for a narrowly source-qualified pair, not a general row equality rule. A provisional helper now requires one reciprocal live edge, equal current positive shapes, no other direct upper rows or exact upper atoms, exactly one same-FreshUse source field, and exactly one matching authenticated where-role subject. It leaves both row identities distinct.

## First falsifier

The focused Console test no longer reaches the old deferred-selection assertion. It fails while collecting the selected member projection with `Collection(MissingDefinitionEndpoint)`. This exposes a source/HIR collection seam that must be repaired before Console output can validate the selection hypothesis. The observation is not evidence that the output runs or that the selector gate is sound.

## Current code state

The source-qualified gate is experimental and must remain subject to falsification. The exact source member projection now tolerates separate authenticated HIR projections of one module while still rejecting a repeated identical artifact as `DuplicateModule`. Member selections retain both the provider FieldTail owner and, when uniquely matched by the same source obligation and receiver row, the outer operator use owner/occurrence.

Runtime lowering keys shared operator providers by their active use site. When a selected FieldTail belongs to a shared provider template, runtime may use its source-owned template selection only when every matching no-use template selects the same exact member root; disagreement remains unavailable. Member bodies are compiled once independent of the caller's operator-use occurrence. Host `write` lookup accepts either source import spelling (`out::write` or `std::io::out::write`) while checking the resolved export identity and signature.

The selected-path guard snapshots the canonical receiver and exact `where` subject representatives plus both positive shapes before applying a source-qualified selection. The candidate is publishable only after the complete nested FieldTail dispatch fixed point leaves both representatives and shapes unchanged. The ordinary source schedule is already drained before this phase. Since bound insertion and intrusion merging are monotone, a changed shape or representative rejects the candidate with `DeferredSelectionUnavailable`; the same-shape atoms do not alter the unique source target. This frontier check is specifically over `Value` rows and value-shape atoms. It does not compare Effect rows or reinterpret contra `[io]`: that annotation remains `[io,'e]`, admits `[state]`, and preserves performed state in the residual. This is executable fail-closed evidence for the accepted path, not a standalone proof that every possible candidate schedule satisfies the condition.

## Conditional stability argument for accepted candidates

For a result returned by `run_candidate`, any FieldTail selected through the reciprocal-role exception keeps the same selected source target through the active FieldTail phase. The premises are the source-qualified receiver/subject witness from the same mapped route, complete receiver/implementation inventories, one matching target, complete direct where-clause witnesses with one prerequisite-free implementation, and the post-dispatch snapshot check. `run_candidate` drains `execute()` before `execute_candidate_field_tails`; that routine processes the initial active obligations and every nested obligation until no deferred items remain. On the exceptional path it records the exact Value representatives and positive shapes of the receiver and authenticated where subject before admitting the chosen body. At the fixed point it compares both representatives and shapes; any difference returns `DeferredSelectionUnavailable`, and `finish_candidate` separately rejects unresolved active selections. Candidate value bounds are only inserted and intrusion representatives only merge, so the check rules out a later distinct positive shape or quotient change in every published candidate. The unique target and where-prerequisite tests are functions of those exact shapes and the pinned complete source inventory, so their result is unchanged at publication.

This closes only the implementation-level stability condition for published candidates that take this path. It is not a static theorem about schedules that fail the guard, a derivation of every `LocalSource` constructor into the typed core, or the full source/native theorem in proof companion §7.1. The unchanged sample tests exercise one accepted source path; R70/R71, all-sample Yulang2 compatibility, principality, and production remain open.

The unchanged Console sample now completes ordinary inference and module execution with exactly `hello from Yulang\n3\n`. The Types sample's existing host-write execution and one-shot continuation tests also pass. Exact-source CLI regression tests now cover both 142-byte Types and 92-byte Console templates and their required outputs. Full `cargo test -p yu-playground` passed (all library tests and package integration groups). Temporary `R330_*` traces and the temporary module inventory print were removed. These are implementation receipts, not proof closure.

## Conditional FieldTail source-to-runtime identity bridge

For a successful `CandidateInference` accepted by `RuntimeProgram::from_candidate_world`, each selected FieldTail target remains joined to the source member identity through runtime lowering:

1. `selected_field_tail_uses` reads the retained `MemberFreshUse` records. A use carries its exact member root, FieldTail owner, source owner and occurrence. If it came through an operator provider, the provider FreshUse is joined by the exact occurrence and receiver representative; more than one matching use is rejected as `ArtifactMismatch`.
2. `from_candidate_world` requires the candidate to observe every supplied HIR and have no conflicts. For each use it resolves one source module for the exact source owner, verifies that the exact occurrence is a `FieldTail`, resolves one module for the exact `SourceMemberRootId`, and verifies the member's single root parameter against its receiver header. Conflicting evidence for the same runtime key is rejected.
3. Runtime source-root collection revisits that source owner and occurrence and builds the same key `(active_owner, source_owner, occurrence, use_occurrence)`. It resolves the exact member root from that key. A shared provider-template fallback is available only when every matching no-use template selects the same member root; otherwise lookup fails closed. It then verifies the selected member's source header and spelling before adding that exact member source root to the runtime-root worklist.
4. The member body is compiled once under its exact `SourceMemberRootId`. A retained `FieldTail` instruction is lowered to an ordinary `Apply` whose callee is that member template and whose argument is the original receiver instruction. No later lookup by member spelling or runtime value shape chooses a different implementation.

Therefore, **when candidate publication and runtime-program construction both succeed**, execution uses the exact source member selected by the candidate's source-qualified FieldTail evidence, including `pair.say` for Types and the nested `value.show` in Console's imported `say` body. Missing sources, duplicate module owners, conflicting selections, and absent evidence return an error rather than selecting another member. This is a finite source/HIR/runtime identity argument for the retained records and successful lowering path. It does not prove that every intended source typing creates those records, that the member application is type preserving, or that every accepted source is executable. The exact CLI output tests establish execution for the two pinned examples; R149's public-type pane, Web/WASM path, whole source-to-typed-core theorem, and general runtime simulation remain open.

## FieldTail source-to-constraint bridge

For one retained `LocalSourceForm::FieldTail` at occurrence `o`, with receiver child `i`, member spelling `m`, receiver value/effect endpoints `(r, εr)`, and result value/effect endpoints `(v, εv)`, the source collector retains one `DeferredFieldTail` recipe with exactly those four endpoints, the source node, `m`, and role-member candidates obtained from that HIR's imports. At admission, `source_owners[o]` supplies the authenticated source root; the recipe becomes a `SourceFieldTailObligation` keyed by that owner and keeps `o`, the source node, spelling, candidates, and the same four endpoints. No value constraint is admitted yet.

After ordinary candidate execution, a unique source member selected from the receiver readback is instantiated by one `freshen_candidate_graph_retained` call. Its receiver, result, result-effect, and nested FieldTail rows are all read through that one `FreshUse.rows` map. The solver then records four occurrence-tied constraints: actual receiver value to the member's negative receiver endpoint; member result value to the actual negative result endpoint; receiver evaluation effect to the FieldTail result effect; and member body result effect to that same result effect. The first two use distinct Value slots, the latter two use distinct Effect slots, and each goes through admission with provenance before live propagation. Nested member obligations use the same FreshUse row map. The exact selected root and FreshUse are retained in `MemberFreshUse` for later source/runtime lookup.

This proves an implementation-local source-to-recipe-to-admission identity fact for the selected path: the constraints consumed for the member application originate from the same FieldTail receiver/result endpoints and the same selected source member use. It does not prove that the final candidate graph has a model, or that each admitted bound is a valid premise of a declarative typing derivation.

The corresponding conditional core step is ordinary value-parameter application. If the selected member body has a typed unary Value-entry arrow whose argument and result endpoints are exactly the fresh member receiver/result rows, the receiver has the type represented by the admitted receiver comparison, and the two effect inclusions are valid under the core effect interpretation, then the typed-core application rule yields the FieldTail result type and an effect containing both receiver evaluation and member-body effects. Runtime lowering's exact-member `Apply` supplies the same receiver expression, as established in the preceding identity bridge. This conditional construction does not establish its antecedents: the explicit proof companion's small core excludes Role/method adaptation, and the candidate result currently retains neither a solved model for these bounds nor a typed derivation for the selected member body. Closing source adequacy therefore still requires a method-selection typing rule that links the authenticated role implementation and same-use member body to this ordinary Apply derivation, plus a proof that accepted candidate bounds discharge that rule's premises. No transitivity of concrete adaptation is assumed.

## Web/WASM check environment

`wasm-pack build` compiled `yulang-wasm` for `wasm32-unknown-unknown` in release mode. The Web check could not complete its bindgen step: the default Cargo home is read-only, and with a writable `/tmp` Cargo home plus the existing local registry cache, `wasm-bindgen` CLI is not installed. Offline metadata and compilation work, but the CLI crate is not cached; the attempted registry access failed because `index.crates.io` is unreachable. No Web/WASM smoke result is claimed.

## R149 Web entrypoint audit

The checked-in browser path does not yet exercise either unchanged R149 source. `web/playground/src/main.ts` registers the six older Yulang2 fixtures plus the existing general examples; its inference button calls the experimental graph renderer, and its run button calls the selected-definition API. `apps/yulang-wasm/src/lib.rs` exports only `infer` and selected-definition `run`, even though the host library already has `execute_module`. `web/playground/smoke-test.mjs` checks the same older fixtures and selected definitions. The graph renderer explicitly disclaims principal-type and production-admission claims. Candidate finalization also asserts `closed_types.is_none()` and `schemes.is_empty()`, so there is no accepted public scheme for a Web Types pane to display. Thus the R149 browser gate needs both an actual public-type result for Types (`id`, `answer`, `name`, `pair`) and a whole-module execution/output API for Types and Console; adding the two strings to the example menu alone would not satisfy it. The next implementation boundary needs new exact leases for the inference owner that can publish accepted types, the WASM wrapper, and browser entrypoint/smoke test. The current R330 leases do not cover those Web files.

## Concrete Types candidate graph evidence for public projection

Running the unchanged 142-byte Types source through `yu-playground`'s current graph renderer gives a direct candidate shape for `id`: its root is positive row `r0`, with a function lower bound whose value argument and result both refer to the same value row `r1`. The function's argument-effect and result-effect ports refer to `r3` and `r2`; the retained effect bounds are `EffectBottom <: r2` and `r3 <: r2`. The `answer` and `name` roots each have their exact `IntPositive` and `StrPositive` lower bounds. `pair` has an ordered tuple lower bound whose children point to the `answer` and `name` rows; the concrete integer and string bounds remain attached to those rows. This is source-derived graph evidence for the needed display, not yet a public typing derivation.

The candidate graph already retains root nodes, row identities and bound endpoints, but its export marks semantic premises unresolved. A correct projection must compute a public scheme from the accumulated Simple-sub constraints, preserve the shared quantified row in `id`'s argument/result, retain tuple order and use the same accepted result as execution. `yu_types::ClosedValueScheme` is an available positive/negative type representation with quantified binders and recursive bounds; its generic closed-type builder could be considered only as an output encoder after a candidate-owned construction is proved. Calling `shadow_closed_schemes` or routing candidate inference through legacy F5 would violate the active withdrawal decision. The observed `id` graph also falsifies any projection that prints root lower bounds alone: it would omit the function's correlated ports and the shared variable identity.

Further inspection rules out `ClosedValueScheme` as a complete public carrier without extending its format: its function effect endpoints can only view `EffectBottom` and `Empty`, with no quantified effect-row node or operation-label set. The captured `id` graph has distinct local argument/result effect rows `r3` and `r2` and retains `r3 <: r2`; both rows are marked local by the actual `level > boundary && !non_generic` capture rule. Collapsing these rows to empty would erase the accepted open-effect relation. A public projection must therefore preserve effect-row variables and their bounds alongside value quantifiers, or extend the type representation. It must not assume a closed empty effect merely to render the sample.

The capture rule also limits which bounds are available for a scheme projection: `Capture::row` sets `local` exactly when `level > boundary && !non_generic`, and `expand_row` returns without copying any bounds for a nonlocal row. Thus a self-contained scheme can quantify its local rows, but it must preserve or explicitly discharge every nonlocal shared anchor from the owner context. A `local` bit alone is a generalization eligibility fact, not proof that a root's entire type is closed or that every reachable row may be independently quantified. For the exact Types trace, `r1`, `r2` and `r3` are local and are joined through one root graph; the projection must use one simultaneous row-to-binder map across the function's four ports and all bound endpoints. The first falsifier for a proposed encoder is a graph with a nonlocal row whose omitted owner bounds affect the rendered root.

## Open proof

Show that the complete ordinary source schedule and typed drain finish before field-tail selection. Show that selected method admission adds only receiver-negative constraints and cannot change the positive receiver/subject shape; account for nested member obligations and other pending tails that can share either row. If any later consumer can add positive shape evidence before selection stability is established, keep deferring and extend the pending-work fixed point instead of selecting early. The current focused and package tests do not establish this stability lemma.

The complete Yulang2 sample set, R149, source/native adequacy, original A/B theorem closure, independent review, and production remain open. Contravariant `[io]` still means `[io,'e]`, so `[state]` remains admissible and performed state remains in the residual.

## R331 continuation receipt

The two converted Japanese documents are now part of the active reasoning for this work. The proof companion corrects the earlier Capture diagnosis: replay creates an ordinary shortcut for the cited finite identity chain, so the former R245 assignment does not refute that path. It does not prove general Capture completeness; a broader incidence index remains an optional construction unless another source-qualified gap is found. For R252, the contravariant `[io]` annotation is `[io,'e]`: it admits a `[state]` callback, and calling that callback keeps state in the residual. Permission remains distinct from the callback's actual effect and from runtime Grant evidence.

R331 now exposes a bounded candidate type/effect rendering for the unchanged Types source and a whole-module ordered-write API. The Types rendering keeps the shared identity argument/result row, ordered tuple shape, open effect rows and effect bounds visible; it labels source typing and principality as open. The WASM wrapper and Web entrypoint now select the exact Types and Console sources, show candidate types, and retain module write order. Native package tests pass, including the exact Types and Console outputs and the separate Types `["(42, Yulang)\\n"]` and Console `["hello from Yulang\\n", "3\\n"]` event sequences.

A dispatcher audit found that the initial renderer could hide retained Value constraints and omitted bound-only Effect rows from its quantifier set. The projection now includes all Value and Effect bounds, collects Effect rows before quantification, and rejects multiple concrete Value heads atomically. The renderer and CLI files were added to the exact R331 leases.

Verification: `cargo test -q -p yu-playground` passed after the final projection and ordered-event changes. The focused negative-formal `[io]` regression passed with `--features shadow-apply-candidate`. `wasm-pack` compiled `yulang-wasm` for wasm32, but could not install the wasm-bindgen CLI because the default Cargo home is read-only; `--mode no-install` confirms that no local CLI is available. Therefore fresh WASM glue generation and browser smoke remain unverified. Source-to-typed-core adequacy, principality, full A/B closure, independent review and production remain open.


## R331 fail-closed renderer continuation

A source-level audit found that `render_type_node` had a fallback that printed the internal placeholder `effect-operand` when a graph node was neither a leaf, row, function nor tuple. That could turn an unsupported internal node into user-facing type text. The renderer now returns an error for that case, and the exact Types sample regression asserts that no placeholder appears. An incomplete relay probe without its `act io`/`act state` declarations stopped at source lowering and did not test the permission rule. The exact source with both declarations and a state-effect callback reaches candidate inference; before this repair, rendering stopped at an effect bound operand.

Verification: fresh `cargo test -q -p yu-playground` passed, including the 45 library tests, 27 CLI tests and all package integration targets. The exact Types and Console bytes, type view and ordered output-event expectations remain green. A focused assertion checks that `id`'s rendered argument and result use the same quantified Value row, matching the captured graph correlation for this exact source. A second exact-source test checks that contravariant `[io]` exports an open formal permission and admits a callback that performs `state`; its `answer` section retains a state support bound into an open residual row. The solver-level regression separately verifies that state remains distinct from `io` and connected to that open effect row. The view now renders effect labels/routes and open tails in retained bounds rather than rejecting those operands. Browser smoke remains open: `wasm-bindgen-cli` is absent locally, and a bounded install attempt could not resolve `index.crates.io`; it was stopped before changing repository files. The native test surface references all six checked-in browser examples through sample-specific CLI tests; the broader original Yulang2 catalog is still not established. `npm --prefix web/playground run typecheck` fails because checked-in generated JS declarations do not export `infer_types` or `run_module`. A fresh binding build is still unavailable because the `wasm-bindgen-cli` install cannot resolve `index.crates.io`. The public projection and source-to-solver correspondence remain provisional and open.


The exact `[io]`/`[state]` input is candidate-path evidence only. The resulting view still says source typing and principality remain open; it does not close the original source/native bridge or the full inference A/B obligations.


## R331 continuation and R332 handoff

R331 reached its 900-second serial envelope as an open continuation. Its final renderer adjustment collects unresolved Value rows that occur in displayed bounds into the same quantifier/anchor set, while rows with direct concrete lower heads remain internal graph coordinates so exact ground entries stay unquantified. Focused Types and `[io]`/`[state]` tests pass after this adjustment, and the full `cargo test -q -p yu-playground` suite passes in R332: 45 library tests, 28 CLI tests and every package integration target.

The exact source-level `[io]` regression reaches candidate inference, retains the formal open permission, and shows the `answer` support bound connected to an open residual row. The separate solver regression establishes that the callback's state label differs from `io` and remains in the residual. This is candidate-path evidence, not a proof of production source typing, runtime Grant, principal schemes, or parent A/B closure. `npm run typecheck` still fails because generated bindings lack `infer_types` and `run_module`; fetching `wasm-bindgen-cli` still fails DNS resolution.

R332 continues the unchanged parent goal by constructing a candidate-owned scheme representation and proving its mapping from the exact source graph. The six checked-in browser fixtures each have sample-specific CLI coverage; the larger original Yulang2 playground catalog remains unverified.


## R332 typed candidate scheme projection

The playground projection now first constructs a typed `CandidatePublicScheme`: the value body is a `SchemeType` tree (`Leaf`, typed `Row`, `Function`, or ordered `Tuple`), binders retain Value/Effect row kind, and shared anchors are typed by row kind. The existing display is rendered from that structure, preserving the same shared quantified row in `id` and tuple order in `pair`. Effect operands, permissions, and retained bounds are still held in a textual observation section; this is not yet the solver-owned accepted scheme required by R149.

After this refactor, `cargo test -q -p yu-playground` passed: 45 library tests, 28 CLI tests, and every package integration target. The exact `[io]` open-permission / `[state]` residual tests and the unchanged Types/Console source tests remain included. Browser typecheck still fails on stale generated bindings, and Web smoke remains unavailable without wasm-bindgen-cli.

## R332 direct-primary: typed graph image and constructive correspondence

Status: UNREVIEWED candidate lemma and implementation evidence. The user's
2026-10-22 continuation selects direct primary proof/code work with minimal
sprint bookkeeping. No child or independent reviewer ran. This section replaces
only the preceding description of text-only constraints; the parent A/B,
source/native, generalization and production gates remain OPEN.

### Construction and claim

`tools/inference-playground/src/scheme.rs::CandidatePublicScheme::project`
constructs a finite typed image of `CandidateGraphExport`, before formatting.
It owns node/row/constraint tables and borrows immutable candidate provenance;
it is not a detached, solver-accepted generalized scheme. Nodes retain their
original graph identity and polarity. Effect operands retain the complete
`CandidateGraphEffectOperand` variant, including source owner, origin,
position, operation declaration/use, member index, labels, route/instance and
original tail node. Formal permissions retain their original typed object.
No source identity is reconstructed from printed names.

For every successfully projected exported graph G, let N map its enumerated
node identities to `NodeId`, and let R map its canonical row identities
(`CandidateGraphRow::same_identity`) to `RowId`. The claimed image laws are:

1. N is a bijection onto the image's node table, and its root is N(G.root).
   Distinct nodes remain distinct even when their leaves or row identities agree.
2. R preserves and reflects canonical row equality. Each image row retains
   Value/Effect kind and locality. Aliased rows with conflicting locality/kind
   cause failure, rather than silently generalizing an outer anchor.
3. Every constructor and ordered child edge is retained. A function retains
   its four ordered ports; tuples retain all elements. Leaf polarity and exact
   effect variant/provenance remain available through their source objects.
4. The complete ordered list of exported bounds is mapped pointwise to
   `(kind, N(lower), N(upper))`. Neither rows with concrete heads nor bounds
   outside the displayed body are deleted from this carrier.
5. Every exported formal permission retains its occurrence, source row, path
   and explicit labels, with its tail mapped through the same R as all other
   Value/Effect references. Every effect-operand tail is checked for graph
   membership and Effect kind before its R-reference is stored.

These quantify over successful finite exported graphs, not all source programs
or arbitrary native solver states. They establish absence of additional loss
at this projection seam, not adequacy of the earlier capture/export.

### Constructive argument

`CandidateGraphExport::nodes` enumerates each index of one fixed graph exactly
once. `CandidateGraphNode` equality and hashing use the graph pointer and that
index. The immutable borrow prevents the indexed graph from changing during
projection. Inserting all indices into N before mapping any edges therefore
establishes law 1 and handles forward references/cycles without recursive copying.
An unresolved root or child lookup returns an error before a scheme is returned.

`CandidateGraphRow` equality and hashing both use the immutable state pointer
and `intrusion.rep(RowKey)`. The row loop inserts only a previously absent key,
retains the first source coordinate, and checks subsequent aliases for equal
kind/locality. Thus equal canonical keys have the same R-image and unequal
keys cannot obtain the same image slot, establishing law 2. Opposite polar
nodes can reference this one row without equating their node identities.

The node loop has exhaustive cases for the currently exported leaf, row,
function, tuple and effect constructors. It copies a leaf, applies R to a row,
applies N pointwise to structural children, or retains the original effect
variant while validating and translating its tail. It returns an error for
an unrecognized node. This is a finite case analysis proving law 3; no
induction on potentially cyclic graph reachability is needed. The bounds loop
pushes exactly one image bound per source bound, in iteration order, with both
N-lookups required. This proves law 4. The permission loop similarly stores
the whole returned permission plus its checked R-tail, proving law 5.

Concrete-head expansion happens only in rendering. Its single bounds scan
replaces the previous scan of every bound at every row occurrence. The typed
carrier retains the original constraints even when the printed heading uses
`int`, `str` or a function abbreviation. Multiple distinct concrete heads still
withhold the display. The renderer uses an explicit work stack; active row
expansion returns the same row reference on recurrence. The existing output
byte/work limits and finite node/row/bound/stack limits reject the whole result;
there is no recursive Rust tree traversal or recursively owned type tree.

Projection performs one row pass, two node passes, one bound pass and one
permission pass. Its expected hash-table work is linear in those entries and
child/label/path incidences, plus the actual cost of canonical representative
queries in row hashing. The formal-permission exporter has its own pre-existing
scan/allocation cost. Rendering is bounded by the emitted work/bytes and may
repeat shared substructure; no linear-size pretty-printing theorem is claimed.
Native allocation failure is not converted into a recoverable Rust error.

### Apply to source owners and the original obligation

The source chain is `prepare_with_world` -> candidate inference ->
`CandidateInference::export(definition_root)` -> this typed projection ->
`render::public_scheme` -> `infer_types`. Export checks conflict freedom and
exact definition-root ownership. `Capture::row` canonicalizes row keys and
sets locality from `level > boundary && !non_generic`; `Capture::expand_node`
constructs polar function/tuple/effect nodes; `Capture::expand_row` intentionally
leaves nonlocal bounds in the owning context. This image preserves that
boundary and cannot prove a shared anchor's omitted owner constraints.

For the exact negative `[io]` source, `candidate_formal_effect_port` creates an
open fresh effect port and records the explicit labels, occurrence, owner,
source row and formal path. `formal_effect_permissions` follows that retained
path through the captured negative function, checks Effect kind and returns
that exact port. The new permission table retains its source object and maps
its tail through R. Thus this step does not manufacture an `io` contribution,
close the open tail, or provide runtime Grant evidence. In the exact source
regression the answer's distinct `state` support is an Effect lower bound into
an Effect row; law 4 transports that same bound into the typed carrier.

New source-driven regressions check all nodes, constraints and permissions for
the unchanged Types graph and the `[io]`/`[state]` graph. They additionally check
that `id`'s negative argument and positive result share one RowId, and that the
state support remains connected to a typed residual row. A separate synthetic
deep-display test checks bounded iterative rejection; it is not source evidence.
The existing CLI expectations and exact sample bytes are unchanged.

The remaining parent premises are concrete: capture/source-rule completeness
and shared-anchor ownership (`candidate_scheme`/`candidate_source`), authentic
permission and invocation/Grant correspondence (`candidate_effect`/
`candidate_context`/runtime), correct generalized binders and FreshUse semantics
(`candidate_scheme`), and public types/execution from one accepted inference
result (playground/WASM publication). In particular, `infer_types` and
`run_module` still perform separate candidate preparations; matching results
and successful smoke tests do not discharge the same-accepted-result contract.
This candidate lemma removes the renderer's text-only reconstruction seam; it
does not close any of those premises, principality or the original A/B theorem.

Validation for this frozen projection slice: `cargo test -q -p yu-playground`
passed (48 library tests, 28 CLI tests and all package integration targets).
`npm --prefix web/playground run check` passed after downloading the official
wasm-bindgen 0.2.125 Linux executable into a unique temporary tool directory;
the pinned release matches Cargo.lock. This freshly rebuilt WASM, regenerated
the ignored bindings and passed the existing smoke, including exact Types and
Console events. `npm --prefix web/playground run typecheck` also passed. No
generated WASM/build artifacts are staged. The previous CLI/DNS blocker is
resolved for this session. No browser deployment or independent review occurred.

Resource observation: an unrelated pre-existing solver test (PIDs 95124/95134,
about ten hours old) remains live with unknown owner, approximately 1.6 GiB RSS
and one CPU. It was not stopped or reclaimed. The machine had 20 CPUs and over
26 GiB available RAM; this primary used one Cargo process at a time, and the
WASM build used one Cargo job with a 300-second timeout. Legacy UNKNOWN workers
remain quarantined. Existing dependency warnings concern retained HIR/source
provenance and solver observation APIs; changing those contracts or removing
proof evidence requires their owner-specific follow-up, not erasure here.

### Same-candidate publication continuation

`execute_module_report` now calls `prepare_with_world` exactly once, derives
`candidate_public_types(&hir, &candidate)`, and passes that same HIR/world and
candidate to `RuntimeProgram::from_candidate_world`. Only after the module
schedule completes does it return `CandidateModuleReport { types, events }`.
The public-types helper rejects a candidate that does not own the exact HIR,
even when another independently prepared module has identical source bytes.
The runtime constructor already checks ownership of the main and imported HIRs.
The standalone inspection and execution APIs retain their existing roles.

The constructive publication property is: for any successful report, there is
one prepared tuple (H, C, W, I) such that its types are the projection of C's
exports for H and its events are execution of the runtime program constructed
from that same tuple. This follows directly from the single preparation binding,
shared immutable C references, ownership checks, and final report constructor.
Every earlier failure returns through `?`, before that constructor. Host writes
on this path are captured in private memory; they are not externally emitted
before the report returns. Thus a later unhandled operation or step exhaustion
discards both the type text and any captured event prefix.

The WASM `run_module_report` serializes this one completed report, and the Web
Types/Console Run action consumes it atomically. The initial source and hidden
selected-definition field now agree with the initial Types selector. This
closes the *implementation gap of two separate preparations on the combined
path* identified above. It does not make C a production-accepted inference
result or close the source-typing/generalization/Grant/A/B premises. The new
structural claim remains UNREVIEWED.

Native and WASM regressions retain the exact Types/Console expectations and
check combined reports, candidate conflicts, zero runtime budget and an
unhandled operation after captured Console writes. The type-conflict case uses
an existing type-error fixture. During construction, a standalone `println`
program (without Console's following `say: 1 + 2`) stopped earlier with
`Unsupported`; that probe did not reach the runtime failure boundary. This
existing source-admission limitation remains part of the broader source/capture
work and is not hidden by changing the expected error. The post-output failure
case uses the working Console path plus a distinct unhandled `io::tick`.

One observed owning-package warning is repaired separately: the immutable
`expected_ids` set in `tests/runtime_resume.rs` no longer has an unused `mut`.
Its assertions and expected values are unchanged. Dependency provenance/API
warnings remain assigned to their original HIR/solver owners; no blanket
warning suppression or removal of retained proof evidence is introduced.

Final continuation checks: `cargo test -q -p yu-playground` passed all 212
tests (49 library, 29 CLI and 134 other package integration tests). Fresh
`npm --prefix web/playground run check` and `npm --prefix web/playground run
typecheck` both passed with wasm-bindgen 0.2.125. The smoke now also checks the
combined report and its three failure cases. `python3 tools/agent_sprint.py
check` passed as static bookkeeping evidence only. No broader workspace suite
or independent review was run. Projection checkpoint `aba924221` and its five
previously local R331/R332 commits were pushed non-forced; the combined report
and final receipt are preserved by the commit containing this paragraph.

Next work remains candidate generalization/source-capture adequacy, including
shared-anchor constraints and the standalone-println admission obstruction,
then the broader unchanged Yulang2 catalog. R332 is an OPEN continuation, not
a completed accepted-scheme or parent-theorem gate. The next session can work
directly from this state without routine dispatcher/producer agents.

### Transitive provider closure and source-position operator construction

The standalone `println` counterexample has two distinct causes. First,
`pinned_provider_projection_inner` followed imported binding names from selected
library bodies but scanned imported operators only in the original consumer.
Consequently `println "one"` lacked the library's `+` provider, while appending
an unrelated consumer `1 + 2` supplied it accidentally. The projection now
processes both dependency kinds on every newly selected module projection.
Export joins authenticate declaration identity, namespace, name, range and
kind; operator joins authenticate module, parse revision, declaration and RHS.
Missing, duplicate or stale owner receipts remain unavailable.

For a finite pinned parse universe, let S be the vector of selected source-root
sets. Every enqueue after the initial consumer follows at least one strict
insertion into S. No root is removed, and every newly projected body is scanned
for both kinds of dependency. Thus the worklist terminates after finitely many
strict increases. At termination every binding/operator dependency discovered
in a selected projection has its authentic provider in S. This is a constructive
closure argument for these two source forms, conditional on the existing
projection/import enumerators; it is not completeness for every source form.

Second, the solver formerly captured *all* definition SCCs before constructing
operator provider graphs and operator uses. A direct call could recapture late
operator constraints, but `my emit message = println message; emit "wrapped"`
had already copied the incomplete library graph into `emit`. It admitted a
candidate with no selected FieldTail for the nested `+`; runtime then correctly
reported `UnsupportedFieldTail`. Late recapture at the first library boundary
could not recover the constraints missing from the earlier fresh copy.

`candidate_capture_order` now orders existing definition SCCs and exact operator
provider roots together. Definition-use edges and operator-use edges both point
to the provider required before capture. Definition SCC membership and its
open internal-use routing remain unchanged. Iterative DFS visits each node and
edge; a gray dependency through a provider returns unavailable because a
recursive mixed provider/SCC capture protocol is still open. Ordinary operator
RHS dependencies on definitions, and nested provider dependencies, participate
in the same order. Checked allocations and orchestration accounting cover the
finite node/edge inventory, stack, states and output order.

Each infix occurrence now emits `Action::Operator` at its source position.
Executing it reconstructs exactly one provider FreshUse and admits the existing
two Apply value/effect relations. Duplicate source-use execution is rejected.
Every retained provider FieldTail is transported through that same FreshUse's
four rows (receiver value/effect and result value/effect). Its active owner is
the enclosing source root; its original source owner and occurrence remain
unchanged. Definition FreshUse performs the same ownership transport. Therefore
an enclosing definition capture includes the obligation before its graph is
made visible to a later definition or expression use. The old late per-owner
operator scan and recapture augmentation are removed.

The acyclic capture-path invariant is constructive: assuming dependency graphs
faithfully retain their constraints, source actions first construct the
provider instance and its obligation; capture retains all four rows; a later
FreshUse transports all four with one row map. Induction over the new order,
and then over wrapper uses, preserves that descriptor and the ordinary Apply
constraints. Final availability accepts an unselected route only when the exact
source owner, occurrence and *all four canonical rows* remain in a captured
dormant template. Any still-active obligation continues to block completion.
This does not prove local-binding capture completeness, mutual-SCC obligation
closure, accepted generalization, principal schemes or the original A/B claims.

Selected-member export now finds an operator RHS by immutable source owner,
while runtime attaches an unspecialized member receipt to the actual source
body rather than its enclosing inference capture owner. Exact operator-use
receipts still carry their source call-site context. Conflicting selections
still fail; no receiver-shape runtime dispatch was introduced. Existing Console
`str` addition and `int` addition remain distinct.

New coverage includes the exact transitive operator-provider join, selected
nested-library evidence, single and repeated `println`, one and two wrapper
levels, a forward definition, and an ordinary consumer string addition. An
uncalled wrapper also has a successful candidate with a dormant obligation and
no fabricated selection. Its *runtime* path still reports `UnsupportedFieldTail`:
`reachable_runtime_roots` currently requires a selected method even inside an
uncalled lambda. That separate source-to-runtime generalization boundary is
explicitly open; the candidate-only regression does not claim executable
support. The nested-provider solver case also includes a provider RHS using an
imported `id`, so moving all providers blindly ahead of definitions cannot pass.

These arguments and implementations remain UNREVIEWED direct-primary research
work. No independent reviewer or child ran, and no production gate is promoted.

Validation of this slice: the complete `yu-playground` package passed all 216
tests (52 library, 30 CLI, 134 other integration tests). The solver's
`candidate_scheme::authentic_demand_capture_tests` filter passed 13 tests and
failed 6. A separate clean detached worktree at baseline `8d495d3fd` passed 12
and failed the same six with the same errors/assertion values; the new imported
provider-definition case accounts for the added success. The baseline worktree
was removed cleanly afterwards, without altering the current working tree.
The still-failing baseline tests are:

- `active_outer_root_two_helper_uses`: `IdentityExhausted`;
- `module_fresh_route_retains_full_remap_crosswalk_and_capacity_accounting`:
  retained-map byte assertion, 1032 versus 744;
- `replay_constructor_lineage_observes_rejected_cross_route_authentication`:
  `ReceiptMismatch`;
- `retained_demand_transport_authenticates_distinct_uses_and_rejects_wrong_use_or_root`:
  `ReceiptMismatch`;
- `structural_bound_scoped_payload_authentic_capture_uses_shared_reconstruction`:
  `ReceiptMismatch`;
- `types_sample_fieldtail_receiver_bounds_expose_ordered_pair_shape`:
  the old assertion requiring a still-unselected method.

No expected output or assertion in those six tests was changed. This is a
comparison against the parent commit, not a green solver suite or evidence
that their underlying obligations are resolved. Logs for this execution are
`/tmp/yulang-r332-all-native4.log`, `/tmp/yulang-r332-baseline-authentic.log`,
and `/tmp/yulang-r332-authentic-capture3.log` (ephemeral execution artifacts).

Three further probes locate the next generalization/source-runtime work:
`my main = 1 + 2` and `my main = { my add x = x + x; add 3 }` still reach
`UnsupportedFieldTail` under `--run-module`, while
`my emit value = say value; emit 3` stops with
`Solve(DeferredSelectionUnavailable)`. The first case shows that module
initializer evaluation must also be distinguished from latent function bodies;
merely permitting uncalled lambdas at runtime would not solve that obligation.
The role-prerequisite transport through wrappers and local-binding obligation
capture remain separate open owners. These are recorded counterexamples, not
new source-language restrictions or altered sample expectations.

Fresh WASM build and smoke passed via `npm --prefix web/playground run check`
with the pinned wasm-bindgen 0.2.125. The smoke includes unchanged Types/Console
and added standalone/wrapped-library reports. TypeScript `typecheck` passed.
Generated bindings and build outputs remain ignored and unstaged; no deployment
occurred. The direct-primary slice is ready as an UNREVIEWED research checkpoint.

### Captured definition constraint saturation (current continuation)

Construction invariant for the next repair: an instantiated obligation must
resolve before publication; an obligation retained in an authenticated reusable
definition graph may remain as a template. Both are ordinary source constraints
and use the same evidence-gated member rule. A selected template contributes its
member constraints to its original live rows; nested unresolved obligations must
remain in that same enclosing definition graph. No execution/constant-folding
judgment chooses a member. After this finite dispatch phase, recapture affected
definition exports from the updated live graph so public types include the new
constraints. Operator/member provider graphs and already retained FreshUse maps
must keep their original row-index contracts. This is a proposed constructive
repair under existing source inference authority, not an accepted A/B theorem.

The implemented worklist seeds both active obligations and captured definition
obligations. Seeds are deduplicated by immutable source owner/occurrence and
all four canonical interface rows; an active seed takes precedence. Selection
uses the unchanged complete-inventory, positive-frontier, negative-frontier and
exact-role checks. Unknown template receivers are retained rather than guessed.
Nested obligations from a selected template inherit its enclosing definition
owner and the selected body's single FreshUse row map. A repeated member in
template ancestry stays deferred; a concrete instance still cannot publish it.

At the fixed point, every unresolved item must be a template before completion
is allowed. Its exact descriptor is retained in the enclosing definition graph;
only then is it removed from the active-obligation table. Existing role-frontier
stability checks still cover the entire dispatch phase. This supplies the
preservation step that was missing when a definition was captured but never
used by a later Name occurrence. Selection in a function's constant body also
works without assuming that the function executes during inference.

Affected definition graphs are recaptured once from their original live root,
boundary, source frontier and source-role obligations, together with the old
FieldTail descriptors and newly retained nested residuals. Thus a successful
public snapshot contains the bounds added by selected member bodies. Stored
operator/member provider graphs and per-route graph snapshots are not replaced;
their retained FreshUse row indexes retain the same referents. The recapture
also samples the updated retained graph accounting. This remains a conditional
source-to-graph preservation argument, not a proof of principal generalization,
whole-source completeness, local-binding capture or original A/B closure.

The worklist extends a finite source inventory without enumerating typings.
Each successful dispatch adds one exact member instance; ancestry bounds each
nested chain by the finite member inventory. Deferred items are revisited only
after some dispatch adds constraints. Seeding uses a checked hash set; final
recapture occurs once per affected definition. The existing receiver-readback
and deferred-round scans remain a potential cost to optimize after correctness
coverage; this increment does not assert a linear bound for the whole solver.

Shared-anchor correction in the implementation: deduplicated template work
retains a vector of *all* definition positions containing the same exact
source/occurrence/four-row descriptor. Nested residuals inherit that vector and
are attached to every such graph during final recapture. The active work table
contains the one processed descriptor, which is removed once after all owner
captures succeed. A concrete active seed takes precedence over template seeds.
This prevents deduplication from dropping a residual from one of two graphs
that share anchors. The owner-vector inventory is bounded by the original
captured-descriptor inventory; nested ownership follows the actual selected
instance, not a new source identity or guessed environment.

The regression now runs `pub answer = 1 + 2`, string concatenation, both branches
of an ordinary conditional, and a constant expression inside a function. Each
runs without needing an extra source Name occurrence and publishes the correct
concrete result head. The displayed graph still retains quantified effect-bound
variables; the check accepts that existing explicit binder syntax rather than
erasing the constraints. An invalid `1 + false` in the unchosen branch of
`if true` still produces candidate type conflicts. An uncalled generic wrapper
still retains an unresolved template without a fabricated selection.

Native validation after the shared-owner repair: `cargo test -q -p yu-playground`
passed all 217 tests (52 library, 31 CLI, 134 other integration tests). The
solver authentic-capture filter again passed 13 and failed the same six baseline
tests named above; no expected assertion was changed. TypeScript `typecheck`
passed. Current logs are `/tmp/yulang-r332-template-native3.log` and
`/tmp/yulang-r332-template-solver2.log`. The initializer failure recorded in the
previous subsection is now repaired for the tested ordinary source forms.

The uncalled `println` wrapper, wrapped `say`, and local `add` counterexamples
were re-run and still fail at their previously recorded boundaries. The next
source-owner step is the `instantiate_candidate_graph` role-prerequisite
transport: a first FreshUse retains the role/receiver correlation, but enclosing
definition capture does not yet carry the role prerequisite forward to the next
wrapper use. Local scheme capture likewise needs its own FieldTail descriptor
transport. Neither is reclassified as a source restriction. Shared-anchor and
full capture/source completeness, independent review, original A/B and
production remain OPEN; this continuation remains UNREVIEWED.

The final fresh WASM check passed with 14 execution examples, including the new
captured-initializer case, unchanged Types/Console outputs and the prior wrapper
regressions. Generated bindings and build outputs remain ignored. No deployment
or independent review occurred. Only the direct primary worked; no child or
background primary process remains after this checkpoint.

### Enclosing role-prerequisite transport

The source identity of a where-clause provider and the graph that currently
captures its instantiated constraint are different owners. Preserve the
provider, exact clause/subject/role keys and role identity. Map its subject row
through the same FreshUse as the associated FieldTail receiver, then retain it
under the receiving source root until that graph is captured. A graph can retain
prerequisites from several authentic providers. A repeated clause at different
fresh subject rows is distinct work; duplicate same-row metadata is redundant.
The existing bidirectional role/FieldTail checks remain required. This is the
construction invariant for the repair, not a new role-selection rule or proof
of unrestricted generalization.

A sibling obstruction is already present in direct `say (3, "text")`: its
receiver shape is the complete tuple (int, str), with one reciprocal role edge
and two negative non-row bounds in the tuple-element frontier. The old gate
rejects every such bound. A closed primitive upper bound equal to the row's
complete positive primitive head adds no alternative member target: int <: int,
str <: str (likewise unit/bool) are satisfied, and any later incompatible lower
bound conflicts instead of licensing a different shape. Extend only the
existing authenticated role-edge case to admit these matching terminal bounds.
Count all other upper bounds as unresolved; do not infer a shape from uppers.
Keep exact role receipt checks and the final whole-shape/representative snapshot
check. This elementary compatibility argument does not certify the broader
source-role frontier or original A/B theorem.


For the module-capture step, write a prerequisite as `(p, w, s, q, R, r)`,
where the first five coordinates are the immutable provider, exact source keys
and authenticated role identity, and `r` is its subject row. If a captured
FieldTail requires `R`, the existing bidirectional check establishes its
same-graph receiver/subject witness. For one retained FreshUse map `f`, the
transported prerequisite is exactly `(p, w, s, q, R, f(r))`; the associated four
FieldTail ports use that same `f`. Enclosing capture normalizes both with the
same current representative map and retains their actual graph bounds. Thus a
second FreshUse `g` receives the composition through that captured graph;
neither the original provider nor a row from another invocation is substituted.
Induction over a finite chain of successful module captures preserves the
source coordinates and this same-use correlation, conditional on the existing
capture/restoration correspondence. Distinct provider prerequisites coexist;
deduplication removes only the same source clause at the same canonical subject.
This addresses the missing metadata transport premise in the wrapper path of
the original source-to-constraint bridge. It does not establish capture
completeness, principal schemes or unrestricted member dispatch.

Validation: all 219 native playground tests pass (53 library, 32 CLI, 134 other
integration tests). New source coverage includes integer/string wrappers,
two nested wrappers around tuple display, repeated use of one provider, and two
distinct where-clause providers captured by one function. The tuple readback
retains its two actual negative primitive bounds and sole authenticated role
edge. The new solver test rejects classifying a mismatched primitive upper as
compatible and confirms that an upper alone supplies no positive shape. Its
first harness attempt omitted interning the primitive leaves; authentic typed
source declarations supply those leaves in the corrected harness. The focused
solver filter now passes 14 tests and retains the same six baseline failures
listed above; no existing expected assertion changed. Fresh WASM smoke passes
all 14 execution examples plus the new tuple-wrapper module-report case and
unchanged Types/Console outputs. TypeScript checking passes. Logs:
`/tmp/yulang-r332-role-native.log`, `/tmp/yulang-r332-role-solver2.log`,
`/tmp/yulang-r332-role-web.log`.

The remaining local seam is concrete: `LocalScheme` stores only its root,
boundary and optional scope region, and `route_candidate_local_run` captures
with empty role/FieldTail descriptor lists. Source initializer ownership must
select the exact descriptors before local FreshUse can map them; a result-shape
filter or all obligations from the containing definition is insufficient.
Operator/member provider capture now retains any received role descriptors,
but their subsequent FreshUse paths and the role-frontier receipt scanner still
need the corresponding transport extension. Uncalled generic runtime bodies
also remain open. Only the direct primary authored this checkpoint; independent
review is UNREVIEWED. Original source/native and A/B obligations, accepted public
schemes, the full unchanged Yulang2 catalog, and production remain OPEN.


### Local initializer ownership construction

The current local repair uses source-scheduled initializer brackets. Collection
emits `BeginLocal(slot)` before visiting the exact binding initializer, and its
existing `Install(slot)` closes that bracket after all initializer actions.
The source traversal is a stack, so induction on nested blocks gives properly
nested brackets with the same authentic HirLocalId at both ends. While a
bracket is active, descriptors received by that source root belong to its
innermost initializer; descriptors owned by another source root remain there.
Completed inner schemes keep their own descriptors. Only an actual inner local
use transfers a fresh image into the enclosing initializer. Consequently an
unused inner generic body's independent obligations are not accidentally made
active by calling its enclosing function.

Local capture must retain those exact descriptors with its live root and
boundary, then use the same FreshUse row map for the root, all four FieldTail
ports and each prerequisite subject. The pure existing module prerequisite
check can be shared. Local templates, like definition templates, participate in
member propagation, with unresolved latent templates retained at their actual
capture owner and concrete active uses still required to discharge. This is a
provisional source-ownership/transport construction under the existing capture
premises, not a proof of general local generalization or original A/B closure.


The implementation retains one descriptor bucket per authentic local slot and
an initializer stack. `retain_source_role_obligation_for` and
`retain_source_field_tail_obligation` select the innermost matching source owner
at insertion; `Install` closes only its own bracket. Nested local use consumes
the stored descriptors and activates their exact FreshUse images in the current
caller bucket. The original module prerequisite validator is now a pure shared
helper. The reciprocal role-frontier witness also reads retained LocalFreshRoute
maps under the identical unique-source/same-row conditions. Local templates join
the existing propagation queue; owner tags distinguish definition recapture
from local descriptor retention. Ordinary active obligations remain mandatory.
Initializer markers add O(depth) live stack space and O(1) amortized push/pop
work; retained metadata adds O(locals + descriptors + role/member payloads)
space; duplicate-marker validation scans at most the current nesting depth. Insertion accounting measures capacity deltas rather than rescanning
all previous initializer descriptors. Existing descriptor-deduplication and
bounded graph capture costs remain; this is not a new whole-solver complexity
claim. Failed local publication records whether it closed a bracket in the
existing route journal, restoring that marker on rollback without synthesizing
a new source action.

A second source correspondence defect became visible with two different local
functions using `+`, one at int and one at str. Inference selected both exact
members, but runtime export tried to recover each operator source occurrence by
comparing the selected receiver with the original operator FreshUse row. Local
FreshUse had correctly copied that row, so both selections lost their distinct
call sites and collided. `OperatorFieldTailOrigin` now records the authentic
introducing operator owner/occurrence at `execute_candidate_operator_use`, travels
unchanged with the descriptor through capture and FreshUse, and reaches the
selected MemberFreshUse. Export verifies it against the retained operator-use
inventory and returns that exact source key. No type shape chooses the origin.
The descriptor-work identity includes this origin so equal row constraints
cannot discard distinct runtime source uses. This repairs the dropped-fact
premise of the conditional source-to-runtime identity bridge; polymorphic
specializations at one identical operator source site still need their own
runtime call-context construction.

Observed remaining counterexamples (not source restrictions):

- `my main = { my emit x = say x; emit (3, "text") }` with `--run main`
  reaches runtime `ContinuationMaterialization` because capture_template refuses
  a GlobalRead/Root frame in the continuation suffix. The local role obligation
  now solves. The same local body called from a top-level function or expression
  executes with `(3, text)\n`; the runtime initializer case remains OPEN.
- `my main = { my add x = x + x; (add 3, add "a") }` reaches runtime
  `InvalidSourceReference`: two specializations of the *same* source operator
  site require runtime call-context evidence. Distinct local operator source
  sites now execute independently and correctly.
- `my outer x = { my unused y = y + y; x }; outer 3` still fails eager
  runtime construction with `UnsupportedFieldTail` in the uncalled generic
  body. Source-level descriptor ownership no longer activates that unused
  body's constraint in the caller. A general runtime body construction repair
  remains necessary.


A source-coverage check found that retaining all initializer descriptors only
in the local scheme would drop an *executed* initializer when its value is
unused. The final construction also brackets each source Lambda. Descriptor
insertion records whether its lexical lambda depth equals the active
initializer's entry depth; those initializer-computation descriptors are copied
into the enclosing bucket when Install closes the local bracket. Descriptors
beneath a Lambda remain with the local value. The original local descriptors
are retained for local value FreshUse; one-shot effects still flow through the
existing initializer-to-block effect constraint, and local Name effects remain
pure. This follows the source evaluation/abstraction boundary without inspecting
inferred shapes or constant-folding branches. The pure counterexample
`my outer x = { my unused = x.show; 1 }; my main = outer 3` now executes, and
constant output initializers execute once even when their values are unused.

The related source `my outer x = { my unused = say x; 1 }; outer 3` remains
OPEN at the existing role-frontier gate: its instantiated show receiver has
complete positive Int evidence and one matching target, but five reachable
negative row edges (zero negative primitive bounds), so the sole reciprocal
edge exception does not apply. Temporary readback code was removed; the
observation is `/tmp/yulang-r332-local-eager-trace.log`. No gate was weakened and
no failing output was changed to an accepted expected error. This is a separate
source-qualified premise for generalizing the role-frontier proof, alongside
the runtime counterexamples above.


Final validation for this local-capture checkpoint: all 222 native playground
tests pass (53 library, 35 CLI, 134 other integration tests). The focused solver
filter passes 17 and retains exactly the same six baseline failures, including
the unchanged 1032-versus-744 accounting assertion. Three new solver tests check
nested initializer ownership, retention of an eager unused initializer in its
parent, exact descriptor row transport, incremental memory accounting, and
restoration of the source bracket after a failed local publication. The existing
`local_annotation_first_edge_failure_rolls_back_and_retries` test also passes.
The final source Lambda markers and shared local transport passed the full
native suite; only a subsequent private helper rename/comment cleanup preceded
the fresh WASM build. Fresh WASM smoke passes 17 execution examples, the new
local tuple-output report, and unchanged Types/Console outputs. TypeScript
checking and all 57 sprint-tool simulation tests pass. Simulation checks do not
constitute live workers or independent review.

Logs: `/tmp/yulang-r332-local-native5.log`,
`/tmp/yulang-r332-local-solver3.log`,
`/tmp/yulang-r332-local-publication.log`, and
`/tmp/yulang-r332-local-web.log`. Generated WASM/build products remain ignored;
no deployment occurred. All work is direct-primary and UNREVIEWED. The next
source/proof seam is the five-edge role frontier above; same-site polymorphic
runtime calls, uncalled generic bodies, initializer continuations,
operator/member role transport, the complete unchanged Yulang2 catalog,
source/native correspondence, principal schemes, and original A/B remain OPEN.
