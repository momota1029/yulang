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

### Closed internal role frontiers

The eager-unused-initializer counterexample has three canonical rows: receiver
50 and authenticated Display subject 51 each have lower row 55 and one upper
edge to the other; row 55 has concrete Int evidence and upper edges to 50 and
51 (including retained duplicates). Thus the five counted edges are not five
unresolved external requirements. No edge or duplicate may be erased merely
to satisfy the old edge-count gate.

Construction invariant, before implementation: retain the existing unique
same-FreshUse role/FieldTail witness and reciprocal receiver/subject pair.
Let P be the positive closure of both roots, following all lower-row edges and
positive tuple children. Each row in P must have a complete positive shape,
obtained only from positive evidence; every lower branch must agree. Both roots
must have the same shape. For every negative row edge u -> v from P, require
v in P and equal positive shapes at u and v. Every non-row negative bound must
be the matching closed primitive upper of its already-known positive shape.
Unknown, cyclic, unsupported, external or incompatible frontiers remain open.

Conditional target-stability argument: induction over the finite acyclic
positive closure establishes each row's concrete shape independently of its
uppers. Each permitted negative edge relates equal established shapes, and
each permitted primitive upper is satisfied by that row's established head.
These constraints therefore supply no alternative implementation head. The
existing complete implementation inventory, unique target, exact role identity
and where-witness checks still determine the same selection. Later propagation
must preserve the receiver/subject representatives and complete positive shapes
at the existing final snapshot check; otherwise the candidate is withheld.
Conflicts still prevent publication. This extends the previous conditional
selection lemma to internal forwarding edges; it does not establish general
principal typing, source/native adequacy, or original A/B closure.

The planned checker validates against one already-produced positive shape,
borrowing its tuple subshapes. A completed-row map prevents repeated traversal
of shared positive rows, while an active set rejects positive cycles. All visits
and structural shape comparisons share a finite work budget. Negative-edge
validation uses only the completed map, never adds roots or infers positive
evidence from an upper. Work is O(visited positive and negative edges plus
inspected shape-comparison nodes), with O(distinct positive rows + depth) scratch
space; work/depth exhaustion withholds this sufficient witness. Existing
positive-shape construction and source-receipt scans retain their prior bounds.

### Scheduled initializer cut for host writes

The actual failing initializer reaches a scheduled `Frame::Root`, not a
`GlobalRead`. Request propagation already stops before a pending GlobalRead,
leaving its sole cache-write frame live. It instead pops Root into the saved
suffix; the correct cache-free template check then rejects that suffix.

Construction before implementation: for the authenticated resumable host
consumer, extend the same cut to Root. For a stack
P ++ [Root(next, cell)] ++ K, ordinary request forwarding consumes only K;
internal Catch frames in K remain eligible before reaching the cut. At the cut,
retain P and Root, the empty cell and initializing marker, original request
identity, current owner and live views. The authenticated host-write response
enters a template containing K only, above the unchanged live Root, using the
existing single-use external continuation handle. Its returned value reaches
that one Root exactly once, publishes the same cell via the existing Return
rule, clears the marker and advances the same next cursor. The global scheduler
and cache write never become reusable template nodes. A second response to the
same stopped handle is rejected by the existing state/consumed checks.

This is the GlobalRead stack-cut argument applied to the scheduler's authentic
initializer owner. Induction on successive host suspensions preserves one live
publication frame; a later root starts only after the earlier one returns.
The change itself never advances a cursor or initializes a demanded dependency,
and introduces no new automatic consumer. Full forward-demand effect order and
source materialization remain open under the approved 2026-10-16 initialization
decision. The code change costs one additional tag alternative in the existing
O(1) top-frame check and allocates nothing on that branch beyond the existing
unhandled-request/template path. Review remains UNREVIEWED.

The private machine-state regression additionally exposed a scheduler frame in
the host template for a top-level expression: ExpressionReturn advanced to
Completed before the enclosing template OwnerReturn/ResumeReturn could drain.
The same cut must retain ExpressionReturn as well. Its return discards the
expression value and advances the original cursor, with no cache publication.
The identical stack decomposition proves that the scheduler cursor stays
outside the saved suffix and runs only after the resumed expression's owner
frames have returned. This is required for the claimed quiescent completion,
not an assertion weakened to accept leftover frames.

The cut is applied to scheduler frames only for that exact authenticated host
operation. Other outward operations have no external resume protocol and keep
their established opaque saved-suffix/depth observation. A full-suite control
identified that boundary (`cli_native_payload_entry`); its assertions and
expected output remain unchanged. The unconditional GlobalRead cut remains as
before, excluding caller-only handlers for every initializer escape.

### Retained abstract member bodies

The uncalled generic-body obstruction arises because runtime construction walks
every retained source expression, including Lambda bodies, and demands a
selected implementation immediately. The candidate intentionally retains these
unspecialized FieldTail constraints in definition/operator/member/local captures.
Evaluating a Lambda constructs a closure; it does not evaluate its body.

Construction before implementation: expose exact retained template descriptors
from the successful conflict-free candidate, preserving source owner, occurrence
and introducing operator origin. Runtime may retain an unresolved FieldTail
instruction only for that exact authenticated template key. Selected members
still lower through their existing exact evidence. Missing arbitrary evidence
still rejects construction. Reaching a retained unresolved instruction during
execution stops the private attempt with UnsupportedFieldTail; it cannot choose
an implementation from a runtime tag or publish a completed result.

For traces that never enter an unresolved instruction, every step is unchanged:
closure creation retains its body label, source environments and receiving view;
all actually executed member instructions use the same selected bodies. A simple
induction on executed instructions therefore preserves these traces. No static
unreachability claim is needed, and no body is deleted. If execution reaches a
retained unresolved instruction, no member call occurs and the existing atomic
run/report interface withholds the incomplete result and buffered output. This
is a partial-runtime construction, not a proof that every candidate execution
can discharge every stored constraint. Same-site polymorphic specialization
still requires its own call-context/dictionary construction.

The descriptor inventory uses O(captures + descriptors + operator uses)
enumeration/hash work and O(descriptors + operator uses) scratch space, excluding
source-identity hash lengths. Runtime indexes exact keys in a hash set; its
existing per-key source validation still scans owning modules/expressions.
Retaining an abstract instruction adds no runtime search. This slice does not
change inference acceptance.

An additional source probe, `my main = { println "first"; println "second";
7 }`, fails before execution at StructuralProjection. The machine-state tests
use authentic local initializers to reach the intended runtime boundary; no
previous successful sample or expectation was rewritten. General bare-expression
sequencing inside blocks remains a separate source-projection obligation.

### Direct-six checkpoint

The internal-frontier construction now executes the original eager-unused
`say x` initializer for int, str and tuple inputs, nested local initializers,
and repeated same-type calls. The readback still reports all five negative
edges and one selected implementation. The checker controls reject an external
upper even with the same head, incompatible primitive uppers, missing/bottom-only
positive evidence, positive cycles, and disagreement in the role subject.

The host cut keeps scheduled initializer publication and expression scheduling
outside reusable templates. Actual-source state tests retain one unpublished
cell through two writes, reject a duplicate host response, publish the original
result once, execute the later expression write in order, and finish with no
frames or initializing markers. Exact retained abstract constraints now permit
uncalled local and top-level generic bodies. Missing arbitrary runtime evidence
still rejects construction; an adversarial forced entry into an unresolved
instruction produces UnsupportedFieldTail without allocating a result or
request. Invalid unused bodies still produce candidate type conflicts.

All 228 native playground tests pass (56 library, 38 CLI, 134 other integration
tests), preserving existing assertions and expected outputs. Fresh WASM smoke
passes 19 execution examples, unchanged Types/Console outputs and added eager
initializer/module-write regressions. TypeScript checking passes. The focused
solver filter has 18 passes and the same six baseline failures; no failing
expectation was weakened. All 57 sprint-tool simulation tests pass; these are
static/simulation receipts, not independent review or live-agent evidence.

Logs: `/tmp/yulang-r332-frontier-native6.log`,
`/tmp/yulang-r332-frontier-solver-final.log`,
`/tmp/yulang-r332-frontier-web.log`,
`/tmp/yulang-r332-frontier-typescript.log`, and
`/tmp/yulang-r332-frontier-tooling.log`. Generated WASM/build outputs remain
ignored. No deployment or subagent launch occurred. This checkpoint is
UNREVIEWED; all three arguments are local/conditional applications to the
unchanged parent, not original A/B closure or production admission.

Next exact obstruction: `my main = { my add x = x + x; (add 3, add "a") }`
still reaches InvalidSourceReference while building runtime evidence. Its two
selected implementations share one original operator source site, so the
current source-key-only map collides. The next construction must carry the
actual FreshUse/call context or explicit member dictionaries into closures;
runtime value-shape dispatch is not a substitute. The same obstruction occurs
for `outer 3; outer "text"` at one generic `say` site. Operator/member FreshUse
role transport, general bare-expression block projection, the six solver
baseline failures, all unchanged Yulang2 examples, accepted principal schemes,
source/native correspondence, original A/B and independent review remain OPEN.

### Exact instantiation contexts for member dictionaries

The next construction retains the actual successful FreshUse route at each
descriptor transport. A source owner/occurrence identifies a written method
site; it does not identify its polymorphic instantiation. For a local `add`
used at int and str, the distinct local Name routes and their simultaneous
four-port maps must remain distinguishable after enclosing capture.

Before implementation, define a context word by the constructors Empty and
Compose(outer, route, inner), interpreted as word(outer) ++ [route] ++ word(inner).
Each route is a typed index into the retained module, local, operator or member
FreshUse inventory, not a type shape or a reconstructed source guess. Module,
local and operator transport prepend their actual route to the captured inner
word. A selected member's nested constraints compose the caller's word, that
member FreshUse, and the nested graph's word. Capture copies the context handle
unchanged. Selected member records retain the exact originating context.

Induction on these constructors proves that every exported step has its actual
retained row map and source identity, and that order survives arbitrarily nested
capture and re-instantiation. A context DAG interns fixed-size nodes whose outer
and inner references point to earlier nodes. Thus context formation needs O(1)
expected hash work per transported descriptor and O(distinct compositions)
retained space, with no cloning of complete histories. Bounded flattening must
reject exhaustion, dangling routes and malformed DAG references. A stored word
is inference-instantiation evidence, not a chronological execution trace: eager
initializer effects must not be replayed when their values are later read.

Runtime application must preserve this distinction for aliases, returned
closures and captured parameters. Re-evaluating an initializer to obtain a
specialized closure would repeat effects. Selecting by a runtime value tag would
replace the established static choice. The needed next bridge is dictionary
substitution through the existing value/closure environment, preserving its
one-shot initialization and receiving evidence. Context transport establishes
the missing source discrimination premise; it alone does not prove that bridge
or complete polymorphic execution, principality or original A/B.

Runtime construction to attempt from this evidence: each actual binding
initializer gets a fresh dictionary-scope variable (its existing machine cell),
whose default context is its enclosing initializer context. A closure retains
that symbolic context with its lexical environment. A source Name with an
actual FreshUse substitutes the read binding's scope by the caller context plus
that exact Name step. Substitution composes in order through aliases and is
carried alongside ReceivedValue, preserving its value handle and receiving view.
Captured parameters therefore receive the same substitution when read. At a
member instruction, only remaining uninstantiated scopes use their initializer
defaults; this executes eager effects in their enclosing context exactly once.

For contexts (scope, word), substitution of scope a by (b, prefix) gives
(b, prefix ++ word). Functional composition applies the old value substitution,
the current binding substitution, then the caller substitution; it is not a
union of mutable maps. The elementary substitution identity proves that an
alias `f = add` and a later `f` use retain the inner `add` occurrence below the
outer `f` occurrence. Source Name inventories exclude uninstantiated recursive
references. Operator evaluation appends its actual operator step, and selected
member entry appends the actual member step before evaluating that body. Argument
evaluation keeps the caller's original context. No initializer is re-evaluated.

Dictionary construction indexes the complete context word and original FieldTail
site. Each entry must have one statically selected member; disagreeing entries
for the same word withhold construction. A uniform source site may keep its
existing erased static dictionary because all of its actual selections agree.
The context engine is needed only when this uniformity fails. Missing dictionary
entries stop the private attempt. Context words and substitutions are immutable,
bounded data; none inspect a runtime value shape or grant effect authority.
Full source/runtime substitution correspondence remains an explicit research
gate even after the concrete alias/closure cases execute.

#### Dictionary quotient and substitution invariants

The retained context handle now travels through every FieldTail capture,
activation, pending-selection identity and successful member record. The
source-qualified role-frontier join also requires this exact context; equal
receiver rows or equal source sites cannot merge two instantiations. Module,
local and operator active-use publication checks require their exact composed
context. Readback rejects missing routes and nonprior context parents.

Runtime construction projects a retained route to (route kind, original source
owner, original occurrence). It drops the solver's session-local use-instance
ordinal only after checking the following finite quotient condition: for each
complete projected word and original FieldTail site, all retained selections
have the same member root. A disagreement rejects the whole program. Nested
member constraints are included in this check at their extended words. Thus
lookup in the resulting finite map returns the already selected member; the
lookup supplies no new shape judgment. If every existing source key has a
single member choice, the previous static lowering remains applicable.

For the immutable runtime algebra, write a context as `(a,w)` where `a` is an
optional initializer cell and `w` is an ordered word. An assignment
`a := (b,p)` maps `(a,w)` to `(b,pw)` and leaves other bases unchanged. `Then`
means ordered function composition, with the first substitution applied first.
Consequently a binding read carries `S_value; [cell := C_caller.name]; S_caller`.
`C_caller` is stored symbolically: preapplying `S_caller` here would apply it
twice. Initializer defaults likewise store the raw parent context while the
initializer inherits its parent's substitution. The new non-idempotent unit
probe uses `[b := empty; a := b]` and distinguishes one application from two;
this is an algebra test, not a claim that arbitrary synthetic substitutions
are generated by source programs.

Induction on `Assign` and `Then` gives the stated substitution action. Induction
on `Step` and `Join` gives ordered word concatenation. Both traversals verify
strictly earlier child indices. Remaining unassigned initializer scopes unfold
their stored defaults under the current substitution; defaults, substitution
expansion and word expansion share one 32768-work budget per lookup. Missing
entries, invalid indices and exhausted budgets return unavailable. The solver
context readback separately retains its existing 16384-visit limit.

Environment overlays contain no binder and therefore preserve lexical name
lookup after erasing dictionary metadata. A Name read modifies only the
ReceivedValue substitution: its value handle, interface and receiving-view
handle are preserved, and its cached cell is unchanged. Closure and delay entry
compose the substitution with the captured environment; tuple destructuring
transports it to the received child. Request execution carries it into the
existing payload without changing the payload's receiving view. The original
initializer code and publication frames still run once at their original cells.
Host continuation frames retain immutable environment indices, so resumption
does not clone initializer publication or restart source initialization.

These are local algebra/representation invariants and an explicit finite-map
selection argument. Full source correspondence still requires proving that all
source evaluations generate exactly the retained words, including recursion,
all effect/continuation interactions and higher-order escaped values. No
universal saturation/idempotence property of source-generated substitutions is
assumed proved. Existing source/native, principal scheme and original A/B gates
remain unchanged and OPEN; passing executions do not close them.

Costs: forming a context, word join or composition stores a constant-size arena
node (source context interning has expected constant hash cost). Reading a word
costs its expanded substitution/default/word traversal, up to the shared work
limit, not merely the retained DAG size. Runtime dictionary construction and
lookup also materialize/hash expanded source words. Repeated substitutions can
share storage while still costing repeated expansion. This checkpoint makes no
whole-program linear-time claim; aggregate runtime resource adequacy remains
part of the open correspondence/performance work.

#### Direct-seven checkpoint evidence and remaining obligations

The original same-site int/str counterexamples now execute. Source regressions
cover local and module functions, alias chains, nested functions, escaped local
closures, captured function parameters, tuple storage/destructuring, and both
module and local recursion. A generic `show` selects int/str bodies, while one
`outer`/`say` site prints int, str and tuple values in order. Private source runs
check one host initializer write for both global and local polymorphic bindings,
correct final tuple values, unchanged value/view/interface on dictionary reads,
unchanged cache metadata, and empty publication frames/markers at completion.
Removing contextual dictionaries rejects execution without inspecting value
shapes. Algebra/storage tests cover order, non-idempotence, interning/capacity,
invalid DAG edges, missing routes and bounded expanded work.

Actual validation receipts for the current implementation:

- `cargo test -q -p yu-playground -- --test-threads=1`: **236 passed** (62 library,
  40 CLI and 134 other integration tests). Afterward one additional CLI regression
  was added and run exactly: `polymorphic_member_dictionaries_coexist_with_handler_resumption`,
  **1 passed**. It returns `(6, "aa", 11)` with contextual dictionaries and an
  ordinary resumed handler in the same program. Thus 237 current native tests
  have passing receipts; the last addition was a focused run, not a second full run.
- `cargo test -q -p yu-solver --features shadow-apply-candidate authentic_demand_capture_tests -- --test-threads=1`:
  **19 passed, the same 6 baseline failures**. The errors remain IdentityExhausted,
  the unchanged 1032-vs-744 test-only capacity assertion, three ReceiptMismatch
  failures, and the unchanged old “method selection not implemented” assertion.
  No prior expected output was weakened. The separate `instantiation_context_tests`
  filter passes its missing-route/nonprior-parent test. An initial invocation
  without the required candidate feature failed compilation; its corrected
  feature-enabled run is the receipt above.
- Fresh pinned-toolchain `npm --prefix web/playground run check`: **23 execution
  examples passed**, with the unchanged Types/Console bytes, module reports,
  diagnostics and added polymorphic initializer-output probes. TypeScript passes.

Logs are `/tmp/yulang-r332-dictionary-native-final.log`,
`/tmp/yulang-r332-dictionary-handler.log`,
`/tmp/yulang-r332-dictionary-solver2.log`,
`/tmp/yulang-r332-dictionary-context-readback.log`,
`/tmp/yulang-r332-dictionary-web.log`, and
`/tmp/yulang-r332-dictionary-typescript.log`. Build artifacts remain ignored.

The next source/runtime obstructions are still concrete. General standalone
blocks containing expression statements before their final expression reach
StructuralProjection: `module/local_source.rs::block` currently accepts only
BindingStatement predecessors, while the existing expression-only `sequence`
formation is selected specially for conditional bodies. A general repair must
preserve lexical scope, statement order and source identities, including mixed
binding/expression blocks. This observation does not narrow the parent source
quantifiers or authorize manufactured binding sources.

For effects, `act io: our tick: int -> int` with
`my compute x = { my before = io::tick 7; x + x }` and
`my relay (thunk:[io] 'a) = catch thunk { io::tick(value), k -> k 11 }`
still reaches HandlerEvidence at runtime construction. Both
`my main = relay(compute 3)` and the int/str pair have this failure; it also
occurs with repeated continuation use. The monomorphic result annotation `[io]
int` coexistence test passes. These are current source probes, not evidence
that the general handler obligation is solved or that the failing feature is
outside the original task.

Operator/member role transport, complete dictionary/source correspondence,
general effect/continuation execution, six baseline solver failures, all
unchanged Yulang2 examples, accepted principal schemes, original source/native
correspondence and A/B, independent review and production promotion remain OPEN.
This is a direct-primary UNREVIEWED research checkpoint; no child, reviewer,
background service or deployment was launched.

Tooling also passes: `python3 -B tools/agent_sprint.py check` and all 57
`test_agent_sprint.py` tests. These are static/simulation receipts, not live
workers or independent review. All current-primary process handles are terminal.
A fresh runtime list contains only /root. Foreign PIDs 95124/95134 still exist
(12h48m at observation, solver RSS about 1.95 GB); their ownership stays UNKNOWN
and neither they nor the three quarantined historical identities were reclaimed.

### Ordered mixed source statements: construction before implementation

For a block prefix `s1; ...; sn` followed by the existing final expression `e`,
retain an ordered sum `Expression(original index) | Binding(original ordinal)`.
Every expression keeps its original parse-owned source identity; every binding
keeps its real binder, initializer and parameter identities. No synthetic local
is introduced for a discarded expression. Existing prefix-only Block and
conditional expression Sequence carriers retain their contracts; a mixed
StatementBlock expresses the source ordering absent from those two carriers.

The decisive invariant is prefix induction: before statement i, lexical lookup
contains precisely the preceding published bindings plus the enclosing scope.
An expression evaluates/checks in that environment and changes no lexical
binding. A binding checks/evaluates its original initializer and publishes once
under the existing self-recursion rule, after which its name is visible to the
remaining suffix. The final expression has the resulting environment, provides
the block value, and all prefix effects contribute to the block effect. A
discarded prefix's value need not constrain the result, but its own internal
constraints must still be generated and solved. The same lexical-restore boundary
prevents bindings from escaping into sibling branches or the outer block.

Source work-stack construction, solver actions and runtime continuation frames
must each implement this induction in order. Local capture brackets surround
only actual initializers. Source reference ownership assigns initializer Names
to their local Values and intervening expressions to the enclosing Value; source
incidence is preserved without fabricating declaration nodes. Interruption saves
the current suffix/environment, so resumed execution neither skips a later
statement nor replays an already completed prefix. Formation and each traversal
are linear in the source statements/children they own, apart from the existing
solver/runtime work of those expressions. This is a local construction obligation,
not full source/native or original A/B closure.

#### Ordered-statement correspondence lemma

Let B be a successfully formed block with n retained prefix statements and
original final expression e. For 0 <= i <= n, let Gamma_i be the enclosing
lexical environment extended, in order, by the actual bindings in the first
i statements. The initializer's existing temporary self binding and parameters
are local to that initializer. Let C_i be the source suffix after those i
statements. The construction has the following implementation-local properties.

1. **Source identity and scope.** At i = 0, the work stack contains the original
   block restore boundary, final expression, and reversed prefix work. If the
   next statement is an expression, its work item observes Gamma_i and introduces
   no binder. If it is a binding, `Work::Initializer` installs the existing
   temporary parameter/self scope, then `Work::Publish` restores that scope and
   publishes precisely the actual binder. Thus the next item observes Gamma_i+1.
   Induction proves the claim for every prefix and the final expression. After
   the final expression, the stored restore boundary removes exactly the block's
   lexical additions. Allocation of later binder identities before work execution
   does not publish them into lexical lookup. Every expression occurrence and
   binder source key is obtained from its original syntax node.

2. **Constraints.** `Work::Visit` schedules each expression and actual initializer
   before the next statement; only actual initializers open local capture brackets.
   The existing Install step retains its initializer-effect inclusion at slot 20.
   Finish emits one inclusion epsilon_s <= epsilon_B at slot 51 for every prefix
   expression and the existing Group relation from e to B. No prefix value is
   compared to B's result. Slot 51 belongs to the unique parent's contribution,
   and the child's own rules retain their distinct slots. Consequently, assuming
   the existing expression/initialization rules and effect inclusions have their
   intended interpretation, a derivation for every statement and e yields the
   usual sequential block derivation: the value is e's value, and the effect
   contains every initializer/expression effect. A discarded value never discharges
   its internal constraints. The graph traversal gives initializer references
   their original Local owner and prefix-expression references their enclosing
   owner; it does not fabricate local generalization for an expression statement.

3. **Machine suffix.** Relate C_i under Gamma_i to `begin_local(B,i,rho_i)`, where
   rho_i resolves the same published binders to the existing runtime cells. An
   expression step pushes `BlockExpression(B,i+1,rho_i)`, evaluates that original
   label, discards only its returned value, and enters the related suffix. A binding
   step uses the existing Local frame/cell rule; after completion it publishes the
   returned value/view/dictionary metadata and enters the suffix with the extended
   environment. At i = n, the machine evaluates e without a discard frame. Induction
   gives ordered evaluation and the same final value, conditional on the existing
   child-expression, cell and recursive-local simulation relations. No new runtime
   value tag, member choice or receiving certificate participates in this step.

4. **Suspension.** A BlockExpression frame contains only B, the next ordinal and
   the immutable environment index. The existing captured-frame mechanism copies
   that exact suffix descriptor. A request in statement i therefore retains the
   unfinished part of i and C_i+1, not a frame that restarts C_0. Repeated invocation
   repeats the retained suffix according to the existing continuation rules;
   completed prefix statements stay outside it. A binding located after the
   request allocates/publishes its own cell on each invocation. This argument
   does not assert that a partially executed initializer's cell is freshened:
   that case continues to use the existing Local-frame semantics. Scheduled module
   publication and authenticated host resumption retain their previous unique
   live Root frame. The new block frame neither owns nor recreates that frame.

This discharges the newly introduced StatementBlock constructor's structural
preservation obligations relative to the named existing rules. It supplies a
compositional case for the parent source/native proof, not a proof of those
antecedents, all source constructs, principal generalization or original A/B.
Empty blocks and declaration-only endings still lack the existing final-expression
formation case; neither they nor unsupported scoped consumers are reclassified
as accepted. The accepted parent source domain remains unchanged and OPEN.

#### Remaining operator and receiving counterexamples

The source `my f x = { say x; my y = x + x; say y; y }` followed by
`my main = (f 3, f "a")` still reaches UnsupportedFieldTail. A binding-only
control replacing each discarded `say` with an actual unused local binding
also fails through the old Block carrier. Controls with `{ my y = x + x; y }`,
`{ x + x; x }`, `{ 0; my y = x + x; y }` and `{ say x; x + x }` execute;
`{ my y = x + x; say y }` fails at the later show. These observations isolate
the retained dependency/selection problem beyond statement formation.

Temporary readback probes found the original Add descriptors, including module
f uses and local y uses, with their exact context DAGs. The blocked Add receiver
has complete positive Int or Str shape, one positive row edge and six retained
negative row edges (four in a later snapshot). The negative frontier is neither
empty nor source-qualified by the current witness. The later show lacks a
positive shape until that Add result is admitted. Only the first say and its
internal string addition have selected runtime dictionary entries. An executed
missing entry therefore fails closed; dictionary lookup does not choose a member
from runtime tags. Logs: `/tmp/yulang-r332-statements-controls.log`,
`/tmp/yulang-r332-statements-deferred2.log` and
`/tmp/yulang-r332-statements-frontier.log`. All temporary instrumentation was
removed before final native/WASM verification.

The exact next proof obligation is to characterize this extra negative frontier
with authenticated source constraints and stable complete positive shapes, then
transport that witness through the real Operator/Member and enclosing module/local
FreshUse maps. The current helper additionally requires the original FieldTail
owner to be a Definition and an exact reciprocal where-role pair; the generic
operator FieldTail has an Expression source owner. Merely increasing an edge
count allowance or admitting every known primitive shape would not establish
the missing source witness. Active executed instances captured into a main
template also need a complete source-activity argument; capture ownership alone
does not establish that an unresolved instance is dormant.

For the `[io] 'a` handler counterexample, the concrete boundary is
`runtime/receiving.rs::RootCompSchema::from_parameter`: it constructs a schema
only for Unit/Int/Bool/Str result annotations with an outer effect and matching
source owners. Its existing test explicitly rejects Variable and Function.
The generic formal is still classified as a Computation, but no RootComp schema
is minted. The matching handler consequently has no positive local Grant unless
the separate whole-program closed-primitive certificate applies. Generalizing
this constructor requires the result-parametric root-view correspondence,
including returned closures/tuples and inherited views; it cannot be replaced
by treating absent evidence as an unprotected request. No receiving gate or
existing expected rejection was changed in this slice.

These are source-qualified open obligations for the unchanged parent, retained
by the direct primary. They are not new source restrictions, theorem closure,
or an independent review receipt.

#### Direct-eight verification receipt

Ordered expression/binding prefixes now pass through original HIR identities,
sequential solver publication/effect contributions and runtime suffix frames.
Coverage includes braced and indented bodies, shadowing and branch isolation,
discarded heterogeneous values, recursive locals, polymorphic closures/member
dictionaries, effectful initializers, host writes and repeated resumption. An
invalid discarded expression and an invalid unused branch still produce type
conflicts. Effect tests reject a pure annotation for every effectful prefix,
retain both io and state in a function's latent effect, and accept the matching
closed effect allowance. Formal negative permissions are unchanged.

Final receipts, after all implementation/test edits:

- `cargo test -q -p yu-playground -- --test-threads=1`: **242 passed** (64 library,
  44 CLI, 134 other integration tests), exit 0. This final whole-package run
  includes both new private machine tests and the additional effect regression;
  the earlier 240-test run and focused host test are superseded for coverage.
- HIR local-source unit filter: **20 passed**. Catch and conditional source
  integration: **6 + 11 passed**. Inline Lambda source: **5 passed, 1 failed**.
  `malformed_or_unsupported_literals_refuse_private_formation` still expects
  `my value = \x -> (1, 2)` to be unsupported; the exact same assertion fails
  in an isolated clean checkout of baseline `4c691726b`.
- Solver `ordinary_expression_source`: **14 passed**; computation laziness:
  **6 passed**; conditionals: **13 passed**. The authentic-demand filter is
  **19 passed / the same six baseline failures** listed above.
- Solver effect-annotation suite: **14 passed / 4 failed**, reproduced as
  **14 / 4 with the same assertions** in a second clean baseline checkout.
  The failing tests are
  `annotation_checks_whole_generated_lambda_and_preserves_fresh_alias_uses`,
  `exported_annotation_support_is_checked_by_an_outside_boundary`,
  `local_symbolic_effect_tail_keeps_late_concrete_flow`, and
  `local_symbolic_effect_tails_freshen_independently_per_use`.
  These pre-existing annotation failures remain open; their expected outputs
  and assertion bodies are unchanged. Both temporary worktrees were clean
  before ordinary removal, and their build outputs used a separate /tmp target.
- Fresh pinned-toolchain `npm --prefix web/playground run check`: **27 execution
  examples passed**, unchanged Types/Console outputs, identity/diagnostic cases
  and ordered mixed-block host writes. TypeScript passes.
- Sprint tooling unit suite: **57 passed**. These are simulation/static tests,
  not worker launches or independent review. The synchronized current snapshot also passes
  `python3 -B tools/agent_sprint.py check`.

Logs share prefix `/tmp/yulang-r332-statements-`: `native-final.log`, `hir.log`,
`hir-integration.log`, `hir-baseline.log`, `solver.log`, `solver-source.log`,
`solver-effects.log`, `solver-effects-baseline.log`, `web.log`, `typescript.log`
and `tooling-tests.log`. No test expectation was weakened. No child, independent
reviewer or background service was started. All owned tool processes reached a
terminal receipt; foreign PIDs 95124/95134 and historical UNKNOWN identities
retain their quarantine. The direct-primary result remains UNREVIEWED and R332
OPEN_CONTINUATION. The statement constructor is an additional conditional case
of the original source/native obligation; all-source completeness, principal
schemes, original A/B and production promotion remain OPEN.

### Direct-nine: connected frontier construction before implementation

The current original-source trace for `f x = { say x; my y = x + x; say y; y }`
at `f 3` has Add receiver 106 with positive child 116. Row 116 has IntPositive
and upper 112; 112 has independent IntPositive evidence and upper 110; 110 has
independent IntPositive evidence and uppers 112 and 135; 135 has IntPositive
and IntNegative. Thus an upper lies outside the receiver's positive closure,
but the entire connected value component has independently known equal heads.
The operator's source owner is an Expression and it has no required where role.
The old reciprocal-role witness cannot describe this ordinary source instance.
The trace is `/tmp/yulang-r332-frontier9-trace.log`; no gate has been changed
to obtain this evidence.

Proposed sufficient witness: begin with the receiver's complete positive shape.
Build its full positive closure as before, requiring independent positive evidence
on every row and rejecting unknown branches, incompatible heads and positive
cycles. For a negative row edge to an unvisited row, independently check that
row's complete positive closure against the source row's established shape;
never use the negative edge as positive evidence. Repeat until every negative
edge has been checked. Negative cycles are finite graph revisits; positive
cycles still fail. Matching closed negative constructors validate their already
known positive shapes, including ordered tuple children when supported. Every
edge and duplicate remains in the solver. A finite visit/depth bound withholds
the witness before unbounded traversal.

Induction over each acyclic positive derivation establishes its shape without
negative assumptions. Induction over the queue of independently established
rows extends that invariant to the connected component. Every checked row edge
then relates the same established shape, and each terminal upper is structurally
satisfied by its source shape. Consequently none of these frontier constraints
introduces another implementation head. The exact original member inventory,
unique matching implementation and existing where-prerequisite checks still
determine the selected target; the graph argument does not invent a role witness.

Source authentication is a separate premise: join the original FieldTail
owner/occurrence/source/member inventory to either its direct source recipe or
one actual retained Module/Local/Operator/Member FreshUse record. Check the
context DAG node's outer/inner references and all four mapped rows together,
using its existing retained obligation-index crosswalk. Preserve required roles
and operator origin through this join. Receiver equality alone is insufficient.
This supplies the source instance for the graph certificate without assuming
that every FieldTail belongs to a Definition or has a where annotation.

Before admitting a newly certified member, retain the receiver row,
representative and shape. At the end of the complete nested dispatch phase,
require the same representative/shape and recompute the connected-frontier
certificate. This final check also examines any newly introduced negative edge
or constructor. If any premise fails, withhold the whole candidate. Conditional
on publication, monotone constraints and these checks preserve the unique target
through the phase. The old positive-closure-only helper and reciprocal-role
witness retain their existing contracts and negative tests.

This is a conditional implementation-level selection argument and an explicit
source-instance construction, pending implementation/falsification and fresh
independent review. It does not solve principal schemes, all accepted source
reachability, generic receiving, complete dictionary/source correspondence or
the original source/native and A/B obligations.

#### Direct-nine implementation and parent application

`candidate_receiver_closed_component` now realizes the construction above.
Its shared checker retains a completed row-to-shape map, a positive recursion
stack and a queue of rows whose negative frontiers remain to be checked. A row
enters the completed map only after every positive lower has independently
derived the same ordered shape. Bottom supplies no evidence; an otherwise empty
row, a positive cycle or an incompatible constructor rejects. Each completed
row is queued once. Processing an upper may invoke another positive derivation,
but cannot insert an unproved row. Revisiting a completed negative neighbor
only checks equality. This proves the queue invariant by induction on successful
insertions and explains why a negative cycle does not justify a positive cycle.
The old positive-closure-only checker uses the same positive rules and still
rejects upper rows outside that closure and negative tuple constructors.

For a negative tuple, the checker first matches arity and ordered children to
the established positive shape. Primitive children must match their negative
leaf. A row child must have its own positive derivation, is queued, and later
has its entire negative frontier checked. Thus accepting the tuple head alone
cannot hide an unknown child or an incompatible upper on that child. The finite
checker examines every retained duplicate; no bound is removed or approximated.

`candidate_field_tail_has_source_instance` supplies a separate source premise.
It checks the original source-owner table and unique DeferredFieldTail recipe,
including occurrence, source key, member and exact role-member candidates.
A direct instance requires the original owner, no invented role/operator
metadata, and the four original component/parameter rows. A transported
instance uses one actual Module, authentic Local, Operator or Member record,
the record's own graph and row vector, and the retained obligation-index
crosswalk. Both the graph keys and all four current row representatives must
agree. Context references are earlier DAG nodes; the Member outer context is
the actual selected parent's context and the inner context is the captured
field's own context. Operator origin is preserved or introduced by that actual
operator-use constructor. Required roles retain their exact source provider,
identity and reciprocal subject/receiver relation under this same row map.
This authenticates the field's required-role crosswalk; it does not establish
the complete separate Operator/Member role-obligation lifecycle.

The new readback witness is consumed by the existing unique target/where
checker and by source-body projection. Projection only supplies exact member
source bodies; it cannot replace solver admission. Selected receiver snapshots
are retained through the whole nested dispatch phase. Publication requires
unchanged representatives and positive shapes plus a recomputed connected
certificate, including bounds introduced by subsequent dispatch. Failure
returns no candidate. The four-row source join and this stability check are
separate premises; neither follows merely from a known primitive runtime tag.

For the original mixed-statement counterexample, the solver now selects both
Int and Str Add instances, retains their negative edges and distinct source
contexts, and then selects the dependent shows. Native selected-definition
execution produces `3`, `6`, `a`, `aa` in source order. Binding-only, local and
escaping-closure controls also execute. The no-host control returns
`(("3", "6", 6), ("a", "aa", "aa"))`. Bool Add and mismatched operands
withhold execution and publish no earlier write. These are actual source to
constraint to selection to dictionary/runtime cases of the original parent,
not a proof of all-source completeness or principal schemes.

The checker has a shared 16,384-work ceiling and depth 128. Map, recursion-set
and queue growth use checked reservation; each row is queued once. Source
authentication separately caps recipe, crosswalk and required-role searches at
16,384 units; before the existing reciprocal-role predicate it charges its
worst-case four scans of the graph's bound list. Exhaustion returns no witness.
Shape snapshots are bounded per selected receiver and held until phase end,
alongside the existing role snapshots. The total work still repeats bounded
readbacks per field and can scan the recipe inventory per authentication; this
is not a global linear-time or complete peak-accounting theorem. No new cache,
constraint deletion or result approximation is introduced.

#### Whole-module observation and the next source boundary

The first fresh WASM smoke exposed an overbroad assumption in the newly authored
module fixture. The exact original `my main = (f 3, f "a")` returns the expected
writes when `main` is explicitly selected, but a whole-module run with no Name
or expression demand for `main` returns no events. Existing
`runtime/program.rs` classifies Apply/If/Catch/Block/StatementBlock binding
roots for the source schedule; Tuple is currently outside that classifier.
The unchanged module tests all still pass. This is an observed distinction,
not an adopted claim that arbitrary effectful tuple initializers may be omitted.
R149 preserves lazy value materialization and requires every source-marked
computation initializer to run; the initialization decision supplies no new
effect detector. A source-owned classification/initialization proof is needed
before extending this classifier. No scheduler or existing expectation changed.

The new Web selected-definition example retains the exact original source and
expected four writes. The new whole-module examples instead contain actual
top-level demand: either `(f 3, f "a")`, or the same main binding followed by
the Name `main`. Both produce the same four writes. Their addition establishes
these execution paths without claiming that the unforced Tuple binding case
was repaired. Initial failed smoke and focused observation are retained in
`/tmp/yulang-r332-frontier9-web.log` and `module-observation.log` under the same
prefix; the successful final smoke has a separate
receipt. The complete unchanged Yulang2 parent remains open.

For generic receiving, a further source audit identifies two coupled owners:
the primitive-only `RootCompSchema::from_parameter` guard, and
`machine.rs::Frame::RootCompReturn`, which replaces the actual returned view
with `Receiving::ground`. The reviewed primitive theorem justifies that
projection because Unit/Int/Bool/Str have no latent effect paths. For a general
result A, the matching-path map removes the consumed computation root and
maps each actual result path back to that same result path; it does not map
the consumed root onto a function's future invocation. Arbitrary A can retain
its own unknown public profile and private captures. Current closures retain
their environment, and tuple elements retain whole ReceivedValue records;
these facts identify useful preservation cases but do not complete the
general Return/result-view construction. Merely widening the schema guard
would apply the ground projection without its premise. Both owners remain
unchanged; the original generic `[io] 'a` obligation remains OPEN.

#### Direct-nine verification receipt

- Latest full native playground run: **244 passed** (65 library, 45 CLI,
  134 other integration tests), including exact selected-definition output,
  no-host returned values, local/escaped closures and rejection without writes.
- Solver authentic-demand suite: **22 passed / the same six baseline failures**.
  The three new positive/negative frontier and source-crosswalk tests pass;
  existing nested-operator tests additionally authenticate their actual fields
  and reject removal of operator origin. A separate actual-source Member test
  passes for two Relay-to-Render uses and rejects substituting the parent context.
  Its world uses the public role-source entry's existing unscoped mode.
- Solver ordinary source **14**, computation laziness **6**, conditionals **13**
  pass. The older four annotation and one HIR baseline failures remain recorded
  obligations; those suites were not rerun in this slice.
- Fresh WASM build and final full `npm --prefix web/playground run check` pass:
  **29 execution examples**, unchanged Types/Console, three identity definitions
  and two diagnostic cases, plus ordered whole-module write cases. TypeScript
  checking passes. The generated WASM is an ignored local artifact, not staged.
- Sprint tooling **57 simulation tests** pass. Static state checking is a
  separate final integration receipt, not a proof or an independent reviewer.

Exact local logs share `/tmp/yulang-r332-frontier9-`: `native-final.log`,
`solver-final2.log`, `member-instance8.log`, `solver-source.log`,
`web-final.log`, `web-smoke.log`, `typescript.log`, `module-observation.log`
and `tooling-tests.log`. Earlier fixture/debug iterations are not final receipts;
all temporary compiler instrumentation is removed. Existing expected outputs
are unchanged. No child or independent reviewer ran. The conditional proof
and implementation remain UNREVIEWED, with original A/B, all-source adequacy,
principality, general receiving, source initialization and production OPEN.

### Direct-ten: result-parametric RootComp construction

The unchanged source counterexample is reproduced at `f040ea8e2`:
`compute x = { my before = io::tick 7; x + x }`,
`relay (thunk:[io] 'a) = catch thunk { io::tick(value), k -> k 11 }`,
and `main = (relay(compute 3), relay(compute "a"))` fail with HandlerEvidence.
The exact command/source receipt is `/tmp/yulang-r332-root10-baseline.log`.

Fix the original formal, Lambda, outer annotation/effect-row positions and
one shared source assignment, with actual interface Comp(E,A). Keep the ordinary
compatible source typing, operation/response contracts and the existing
receiving/continuation transition premises. A is the actual result interface,
including symbolic, function and structural results; it is not chosen again
after an event. The outer annotation exposes exactly the consumed RootComp
position. The receiving default and concrete-permission rule at this position
depend on its original row, formal and receiver, not on A's tag. Thus the local
RootComp boundary/receipt and positive Grant derivation of the reviewed primitive
theorem extends to A without declaring any nested/future profile complete.
Unknown inherited coverage stays unknown; a symbolic family alone grants none.

At whole-computation completion the typed matching-path map has no image for
the consumed RootComp position. It removes the result prefix of each actual
result path and preserves that path's original evidence, ledger references and
lineage. Disjointness of RootComp and result paths proves that an outer grant
does not become a returned function's future-call grant. Unlike the primitive
case, the result can have unknown or nonempty paths; replacing its view with a
ground view is not justified. The source rule preserves the same actual result
packet, with only the consumed computation's execution delimiter ended.

The current runtime separates these inputs constructively. `consume(Execute)`
opens the received carrier view and stores its exact execution in RootCompReturn;
`execute_with_substitution` evaluates the carrier's original code. Every normal
result is a complete ReceivedValue of that code, not a view synthesized from
the ambient execution stack. Literals/primitive results construct ground views;
closures/operations/tuples construct opaque views; tuple elements and private
closure environments retain their own whole records. Name/Bind/Return/Case and
dictionary substitution preserve the actual result record and its private
dependencies. None unions the ambient root image into the result's public view.
Therefore RootCompReturn can end only its matching execution and return the
same actual result record. This is the native representation of the matching
result map, under those original constructor premises; it supplies no complete
Function-view inference or new adapter semantics.

An induction on the actual result constructors establishes unchanged value,
interface, view and dictionary coordinates. An induction on nested execution
delimiters establishes that inner completion removes only that inner execution;
outer executions remain live until their own completion. Request crossing and
template View re-entry already retain the original view/receipt and create only
a new execution occurrence. Applying the same completion case after each actual
reuse preserves this invariant for every finite legal reuse history. Captured
computation bindings stay in private environments and can later be consumed at
their real Name; returning a closure neither executes them nor changes their
original receiver activity. Expired receiver and exact-operation checks remain.

Implementation packet: retain the existing primitive-only schema constructor's
contract and tests. Add a source-guarded constructor for the actual-result-view
completion protocol and use it at the original Lambda/member parameter producer.
Replace RootCompReturn's unconditional ground-view construction with identity
return of the authenticated actual result view. No eligibility, force schedule,
operation payload/response rule, receipt creation or boundary identity changes.
Test original source execution, exact tuple/closure view preservation, nested
and repeated continuations, missing permission and expired/captured receivers.
This is a conditional direct-primary construction, UNREVIEWED; unrestricted
source/native adequacy, profiles, principal schemes and original A/B remain OPEN.

#### Source-owned annotation holes: construction before implementation

The pinned Y2 reference (`a58eefc31e22141574b6f20c6a5748151c6d79f1`,
`web/docs/reference/types.md:192`) defines `_` as an inference placeholder, not
an additional type constructor. Its annotation builder allocates a distinct
wildcard identity at every occurrence (`annotation/builder.rs:185–189,399–406`).
Its bounds implementation uses Bottom/Top for a wildcard (`constraints.rs:324`),
so no equality between two different holes follows from their common spelling.
This is source evidence for the existing meaning, not adoption of F5 inference.

The candidate paired annotation route checks a negative projection and exposes
a positive projection. Replacing a hole by Bottom/Top there would discard the
actual inferred result at exposure. Construct instead one fresh ordinary Value
row h for each pair (actual annotation scope, original hole SourceNodeKey).
Both polar projections of this same hole use h. Different holes and named type
variables have disjoint identities. No row is identified merely because two
hole occurrences spell `_`, share a formal owner or have equal inferred shapes.

For a formal hole at existing row a, the two generated bounds are h <: a and
a <: h. Projecting away the new h leaves exactly the old assignments to a:
any old assignment extends with h=a, and the new constraints impose no condition
on a beyond that equality. The two directions still carry their original
constraint occurrences. For a structural annotation, perform this construction
at each original hole position and use the existing Function variance rule;
every hole is filled once in the shared annotation assignment used by checking
and exposure. This preserves the inferred information carried from the checked
value to the exposed value. It does not claim that an unconstrained positive
Bottom alone could expose an actual type. Soundness of the enclosing annotation
route and its source-typing correspondence remain the previously open premises.

The native representation retains the original type-expression key for each
hole; an arrow's head and result have different original nodes. Parentheses
forward the inner hole key. A source-scoped hole-to-row table is separate from
the existing named-variable table so ordinary named annotations incur no larger
key or extra per-entry payload. The original source owns the table entry; a
FreshUse copies the resulting graph by the existing simultaneous row map,
without querying or recreating a source hole. Repeated visits within one paired
construction reuse exactly the same row. Local annotations retain their actual
Local scope; inherited levels and generalization boundaries are unchanged.

Expected table cost is O(H) storage and O(1) lookup per hole occurrence for H
retained source holes, plus the existing graph work. The source parser's depth
limit and resource accounting apply. Failure either removes journaled entries
with their attempted graph or withholds the attempt. A hole does not certify a
monomorphic operation signature; generic operation/arm opening stays unavailable.
The RootComp actual-result protocol can accept a hole result because its local
permission proof never inspects the result's shape. Effect-row wildcard syntax
and complete Function-path profiles are separate obligations, not inferred here.
This is provisional, conditional and UNREVIEWED; it is not principal-type or
all-source closure.

#### Handoff verification, 2026-10-23

The resumed primary inspected HEAD `f040ea8e2` and adopted the unfinished
RootComp result-view and source-hole changes. The HIR hole test initially did
not compile because its iterator compared an extra reference; the corrected
comparison retains the original identity assertions. The source-node and solver
hole tests each pass, including rollback and distinct hole/scoped rows. CLI
coverage exercises independent holes, local polymorphic use, later member
constraints, rejected incompatible results, and the original effect permission.
All native playground tests pass: **251** (67 library, 50 CLI, 134 other
integration tests). Fresh `npm --prefix web/playground run check` passes with
**35** execution examples and unchanged Types/Console outputs; TypeScript passes.
Logs for this verification are repository-local `target/r332-handoff-native.log`,
`target/r332-handoff-web.log`, `target/r332-holes-hir.log`, and
`target/r332-holes-solver.log`. No existing expectation was weakened.

The complete pinned Y2 catalog contains **19** samples, including three intended
diagnostic examples. The exact Effects source still fails candidate lowering:
its `our ask()` empty formal is rejected by `plain_binding_header`. A diagnostic
probe replacing only that formal with `(unused:())` produces the intended
`42\n`, identifying the next owning construction; this probe is not the original
sample regression or completion evidence. Preserve the exact source in the next
regression and implement the Unit formal at its original pattern position.

These are direct-primary construction and execution receipts, UNREVIEWED.
The prior document-reading turn supplied guidance, not compiler-goal completion.
Source adequacy, principal schemes, all remaining Y2 samples, original A/B,
independent review and production remain OPEN. The whole goal is unchanged.

#### Original catalog correspondence and next source gate

The parent is still the complete **19-entry** original catalog in pinned Y2
`web/playground/src/main.ts`, commit `a58eefc31e22141574b6f20c6a5748151c6d79f1`,
blob `e6bec9fe44d673ccbf98af078ef4562c9267ef6c`. The template-literal values were
extracted without changing their source bytes; no selected definition or added
entry expression was substituted for whole-module execution. Each was run with
`yu-playground --run-module --steps 100000` against its own file. The initial
source hashes and exact stdout/stderr are in
`/tmp/yulang-r332-root10-catalog/{manifest,results}.json`.

| Original entry | First observed gate before the hole implementation |
| --- | --- |
| Tour | Syntax diagnostics |
| String Match | Syntax diagnostics |
| Config | Syntax diagnostics |
| Data & Methods | Candidate source unsupported |
| Named Defaults | Candidate source unsupported |
| Button | Syntax diagnostics |
| Local Change | Syntax diagnostics |
| List Update | Syntax diagnostics |
| Sub Return | StructuralProjection |
| Callback Hygiene | SourceImportResolutionUnavailable |
| Nondet List | Syntax diagnostics |
| Nondet Once | SourceImportResolutionUnavailable |
| Junction | Syntax diagnostics |
| Types | Exact `(42, Yulang)` write |
| Console | Exact `hello from Yulang`, then `3` writes |
| Effects | StructuralProjection at the `_` result annotation |
| Type Mismatch | Expected Bool-to-Int candidate conflict |
| Parameter Provenance | Expected Int-to-Bool candidate conflict |
| Tuple Arity | StructuralProjection, not the required arity diagnostic |

Effects has an additional independent gate: `module.rs::plain_binding_header`
returns None for the empty PatternCallTail in `our ask() = ...`. Replacing only
`_` with a named variable leaves candidate source unavailable; replacing only
that empty formal with an unused identifier after the hole is resolved reaches
`42`. Those changed sources are **isolating probes only**, not passing receipts
for the original sample. Their exact sources/results are the three
`/tmp/yulang-r332-root10-effects-probes*.json` files. The next source construction
must retain the original empty Unit pattern, its argument position and ordinary
Value entry/Unit constraint, without inventing an identifier or changing the
sample. General formal patterns and the all-source parent remain obligations.

The module startup classifier is a separate open source law. R167's
`R167-CASE-FETCH-1`, the unapproved R168 tuple-extension proposal, and the ordered
Tuple construction distinguish evaluation of a demanded Tuple from scheduling
an otherwise unreferenced binding at module startup. HIR generalization
eligibility does not establish that schedule. No Tuple/Case/effect-shape
heuristic was added to the source schedule in this continuation.

### Unit formal construction for the unchanged Effects sample

An empty source formal `()` introduces one anonymous Value-entry slot, matching
the Unit argument produced by the existing empty Call constructor. Preserve the
original PatternCallTail/ParenthesizedPattern key and parameter identity; retain
an explicit Unit-pattern flag and no lexical identifier. Empty display spelling
is metadata for this anonymous slot, never a generated source binding. Ordinary
identifier parameters keep their existing representation and lookup.

For parameter row p, admit Unit+ <: p- and p+ <: Unit- at the same original
Lambda occurrence. These are the ordinary formal-domain constraints, with the
negative domain retained for Function construction; they introduce no permission
or effect-row annotation. Any compatible invocation therefore supplies Unit.
Conversely any Unit argument satisfies this pattern's added value constraint;
the argument's effects follow the existing strict Value-entry rule unchanged.
After evaluating the whole delayed argument, runtime checks its actual Unit
constructor and enters the same body/environment without binding a name.
For a request during argument evaluation, the ValueEntry frame (including the
pattern discriminator) remains in the raw suffix, so resumption performs the
same match before the same body. The existing receiver boundary is retained.

This supplies the Unit-pattern cases of source construction and runtime
preservation conditional on the existing Call/solver correspondence. It does
not prove all-source adequacy or full principality. Tests must include original
Effects bytes, top/local Unit formals, mixed currying, wrong argument rejection,
and argument effects/resumption. No fallback or source rewriting is used.

#### Qualified-name formation exposed by Unit admission

Admitting the pinned ops module's `loop_last()`, `loop_next()` and `loop_redo()`
exposes their original multi-segment paths under an import-free source projection.
Retain those valid paths as Name/Unresolved, with their original source position,
just as unqualified unresolved identifiers are retained. This creates neither an
import receipt nor an operation identity. `candidate_source` rejects Unresolved
before constraint construction. The source-adequacy plan requires retaining actual
source constructors and imported ownership; a projection must not fabricate an
import merely to become supported. This is a representation extension under the
user's authorized source implementation, not permission to execute missing imports.

The inherited fmt inventory test froze a *current unsupported boundary* for
`Display.say` with empty imports. That expectation now becomes too restrictive:
its `std::io::out::write` path can be retained without resolving it. Before
changing the assertion, record the replacement contract: require Supported source,
require the exact original qualified spelling and source span, require Unresolved,
and retain candidate rejection for missing imports. All runtime outputs and all
language diagnostic expectations remain unchanged. Primary-only reasoning is
UNREVIEWED; no independent reviewer or theorem-closure claim is made.

#### Unit-formal checkpoint evidence (2026-10-23)

The unchanged Effects fixture has SHA-256
`ec7f06dfe455bbffc258f1a665d915840177f6ae198671da03d2ec6b1efd2699`;
it equals the original pinned template value byte-for-byte. Native CLI and
fresh Web/WASM whole-module reports both produce exactly `42\n`. The UI now
exposes that original sample. Empty and spaced Unit formals, local declarations,
leading/trailing/multiple Unit slots, independent polymorphic uses, wrong
arguments, and effectful arguments with repeated resume are covered. HIR keeps
three distinct pattern keys and no anonymous lexical binding. Solver constraints
retain the Unit domain, create no permission/contribution, and roll back together
with the owning route. Source Unit is still one argument, not zero-arity execution.

Final checks: `cargo test -q -p yu-playground` **254 pass** (67 library, 53 CLI,
134 other); HIR `unit_formals` **2 pass**; solver
`unit_formal_source_constraints` **1 pass**; fresh `npm --prefix web/playground
run check` passes its **35** ordinary execution examples plus the separate
Types/Console/Effects whole-module reports; TypeScript passes. Logs are
`target/r332-unit-{native,hir,solver,web}.log`. The initial missing HashSet import
was fixed. The full run exposed the qualified-name projection issue above;
final runs pass after retaining unresolved paths and updating the documented
internal boundary assertion. An additional CLI regression confirms missing
qualified imports remain unsupported and produce no output.

These are UNREVIEWED primary-only construction/check receipts. Source/native
adequacy outside these constructors, all remaining original samples, original
A/B, principality and independent review remain OPEN. Next, rerun all 19 original
catalog entries using JavaScript's cooked template values: raw template extraction
left escape sequences in Tour and Callback Hygiene, so those two earlier rows
are not reliable receipts for original editor contents. Effects, Types and Console
have no such decoding difference; their byte identity remains established.

### Ordered product annotation construction

The cooked original catalog was re-run after `0144862ce`; its 19 sources and
results are in `target/r332-catalog-cooked/{manifest,results}.json`. Template
escaping affects Tour and Callback Hygiene; their first remaining categories
are still syntax and source imports respectively. Types/Console/Effects succeed;
Type Mismatch and Parameter Provenance produce their intended candidate conflicts.
Tuple Arity needs its written `(int, int)` product retained before the existing
ordered-product constraint can compare it with the three-component argument.

For a written product `(T0, ..., Tn)` retain all components in order. Unit `()`
and grouping `(T)` stay distinct; trailing punctuation `(T,)` is a one-element
product under `syntax-reference/en/src/types/type-expression-core.md` §6. No
arity-specific sample shortcut is permitted. Positive/negative products contain
the corresponding child polarities without reversal; Function reverses only
its argument. Existing ordered Tuple term, Capture and FreshUse constructors enumerate all
children. Direct inspection found the extrusion case missing; construct it as
described below before claiming full product transport. Annotation producers use
the same terms, retaining repeated variables and distinct source holes.

Formal effect permissions nested inside tuple-valued arguments need an explicit
Element(index) path before any Function argument/result step. Product traversal
does not manufacture an effect port; the final permission step still names a
real Function effect port. Captured formal-root lookup must include negative
products when such paths start at a product. Every index and original negative
root must be checked; no shape-based permission is invented. This extends the
source-to-product constructor cases conditional on existing graph transforms.

Tuple component-root computation annotations are retained by HIR but stay
unsupported in candidate preflight until a component computation contract exists;
ignoring them would silently erase effects. Effects inside Function components
retain their normal four-port meaning. Monomorphic operation matchers retain
their existing scalar boundary. RootComp results that are tuple values preserve
the actual ReceivedValue and its view as other general results do. These are
UNREVIEWED construction obligations, not full-source/parent proof closure.

The old HIR rejection probe for `(int,)` is superseded by the syntax authority
above: add positive single-component preservation and use genuinely malformed
`(int,,)` for recovery rejection. Record this causal expectation change before
writing it; no language type-error or output expectation is weakened.
The empty-type-group test also froze `(int, int)` as unsupported. Replace that
part with a separate ordered-product preservation test (including both one and
two components); keep all Unit/grouping assertions intact. The original Tuple
Arity program already reaches the existing Tuple(3)-to-Tuple(2) conflict at its
unaltered argument span after the constructor connection.

#### Product propagation and receiving boundaries

The actual source constructor now produces ordered positive/negative Tuple
terms through `with_term_events`; recursive temporary child buffers are charged
while live and released on both successful and failing routes. Each child keeps
its original polarity; the existing Function constructor supplies variance
reversal. Capture uses the same Tuple child indexes already reconstructed by
FreshUse. Its retained formal-domain map is generalized from Function roots to
composite roots, preserving original terms and demand root identity. Export walks
Element indices and checks that the final permission port is a Function effect
row; Tuple has no synthetic effect port.

The new native source test exercises two different nested permission paths,
`element[0]/result` and `element[1]/element[1]/result`, with the same io family but
distinct source rows/tails. A state callback passes through that annotated tuple
and the invoked callback's state support remains connected to the answer
Function's effect row. This applies the user's negative `[io] = [io,'e]`
correction inside the product constructor. The same annotation constructor is
rolled back after publication and retried; domain, permission and scratch state
are checked with the owning route checkpoint.

A tuple RootComp result containing a polymorphic Add closure and an effectful
integer retains the closure's dispatch dictionary; after resumption and tuple
matching, the original body returns 14. Ordinary tuple components, grouping,
singletons, nested products, local annotations, expression ascriptions and
independent hole/variable uses are covered separately.

The general callback-receiving premise remains OPEN: a probe that catches a
callback invocation directly through a tuple field still reports HandlerEvidence,
as does the corresponding existing Function-value receiving boundary. No
handler grant is invented to pass that probe. This does not block the original
Tuple Arity diagnostic or RootComp tuple-result construction, and is not
misreported as general higher-order runtime closure.

#### Missing native extrusion case and its construction

Direct owner inspection found `candidate_extrusion::Work::Visit` treats Tuple as
an unchanged terminal: only Function and EffectView have structural continuations.
The earlier assumption that all existing transforms already traversed products
is corrected above. This is not established by green example tests. Implement
Work::Tuple with an operation-local arena of (child Key, original Term), retaining
order/arity and scheduling children at the SAME polarity and target level. Rows
use the existing shared operation memo, so repeated coordinates share one copy;
Function children still reverse argument polarity through their own constructor.
Rebuild only when a child endpoint changes. Changed child Tuple endpoints must be
convertible back to terms, including when nested inside a Function. Pending row
bounds are still visited after structural reconstruction; no alternate copy link,
new permission or different scope rule is introduced. Charge the arena and the
reconstruction buffer while live, drop both on every error/success path, and use
with_term_events for new product terms. Existing begin/finish extrusion owns all
new row parents, origin transfer and later intrusion qualification.

The added constructor lemma is conditional on each child transport: for n>0,
map((t0,...,tn-1))=(map(t0),...,map(tn-1)); the same joint map is used for every
child, hence aliases across children and outside fixed anchors remain identical.
Every target child has the required scope by the child premise, so the product
does too. Value inclusion is checked componentwise at equal arity; unequal arity
has no product rule. This composes with the existing Function/effect cases; it
does not establish their open source premises or the whole A/B theorem.

Native evidence for the added extrusion constructor now checks both polarities:
ordered nested products, repeated same-polarity coordinates shared across a
Tuple/Function boundary, unchanged level-zero anchors, Function argument reversal,
Function effect-row copies, complete route rollback, and identity on a second
already-scoped extrusion. Opposite-polarity copies remain distinct until the
existing intrusion rule qualifies them; the test does not equate them merely
because their parent is the same. Three actual source schedules reach the new
Work::Tuple constructor (4, 8 and 5 observed completions respectively), including
`my outer x = { my local (pair:('a,'a)) = pair; local (x,x) }`.
The trace is observation only and has no role in production admission.

The final native package run after this repair passes 257 tests. Source annotation
HIR checks pass 4 tests, with a separate malformed-ascription regression passing.
The tuple FreshUse reconstruction test passes. An additional authentic-demand
filter still fails with ReceiptMismatch at
`structural_bound_scoped_payload_authentic_capture_uses_shared_reconstruction`;
this is the exact failure independently baseline-reproduced earlier in this
note, not a newly certified green solver suite. The broader Tuple filter yields
14 pass / 1 fail at the older deferred-selection readback expectation; comparison
against the immediate parent is recorded at the checkpoint below.

#### Product checkpoint (2026-10-23)

Exact original Tuple Arity source SHA-256:
`a7fca5148dd1af2a5ff6a32095b76e41984fc51b04b12fe790b1cfe86610829d`.
It now reports Tuple(3) against Tuple(2) at the unchanged argument bytes 97..106
(line 3, column 6), through native CLI and Web whole-module reporting. The UI
includes the original fixture. All 19 cooked original sources were re-run;
`target/r332-catalog-cooked/results-after-products.json` preserves complete
stdout/stderr. Three ordinary examples and all three intended diagnostic examples
now meet their checks. The other 13 examples remain blocked by the previously
identified syntax/source/import gates. This does not claim all-sample completion.

Final evidence: native package **257 pass**; source annotation HIR **4 pass**;
malformed-ascription HIR **1 pass**; Tuple solver filter **14 pass / 1 fail**;
fresh WASM **40** execution examples plus unchanged Types/Console/Effects module
outputs and **3** original diagnostic examples; TypeScript and diff checks pass.
The three added solver tests cover actual source-to-native Tuple extrusion,
both polarities/alias/anchor/Function scope transport with rollback, and nested
permission paths with state residual preservation. `tuple_fresh_use_reconstructs_each_captured_child_in_order`
also passes separately. Logs: `target/r332-tuple-native-final.log`,
`target/r332-tuple-hir-all.log`, `target/r332-tuple-hir-recovery.log`,
`target/r332-tuple-solver-all.log`, `target/r332-tuple-web.log`.

An isolated clean worktree at the immediate parent `0144862ce` reproduces
`post_schedule_readback_recovers_receiver_tuple_shape` with the same failed
DeferredSelectionUnavailable expectation (baseline Tuple filter **11 pass / 1
fail**). It also reproduces the exact ReceiptMismatch in
`structural_bound_scoped_payload_authentic_capture_uses_shared_reconstruction`.
Logs: `target/r332-tuple-baseline.log` and
`target/r332-tuple-baseline-demand.log`. The temporary worktree was removed;
its tracked files were unchanged. Neither expectation was altered. These open
baseline gates are retained as obligations, not hidden by a green suite claim.

Primary only, no subagent or independent review. All derivations remain
UNREVIEWED and conditional where stated. The original A/B/source adequacy,
principality, remaining 13 original samples, general callback receiving and
operation/component computation gates remain open. The next shared source path
is ordinary pinned arithmetic used by the record/range/search samples, followed
by their remaining constructor/iteration gates; no sample rewrite is authorized.

### Pinned subtraction and multiplication construction

Authority is the unchanged pinned `lib/std/int.yu`: sub/mul are curried
`int -> int -> int` values backed by `builtin_op::int_sub`/`int_mul`.
`lib/std/num.yu` supplies the authentic Sub/Mul role methods, and
`lib/std/core/ops.yu` supplies prefix minus and the infix operators. Retain this
entire import/member/primitive path; recognizing a source `*` or `-` directly
in runtime is not the construction. Existing runtime integers are arbitrary
precision signed decimal strings, so no machine-width truncation is allowed.

Subtraction is addition of the sign-normalized negated second integer, reusing
the existing magnitude addition/subtraction algorithm. Multiplication uses
base-10 school multiplication with at most n+m output digits. One kernel step
normalizes one digit pair: sum = accumulated digit + a_i*b_j + carry, which is
at most 99. Replace that digit by sum mod 10 and move floor(sum/10) into carry;
at row end the next untouched high digit receives carry. Thus each step
preserves the represented partial product, and induction over row/column indices
finishes with |a|*|b|. The output sign is XOR of input signs, except canonical
zero is unsigned. Equal source operands are read as values, never mutated.

The kernel is a pure Machine state after both curried arguments have returned.
It performs one digit pair per machine step, preserving all frames, views,
invocations and environments. Budget exhaustion retains the same private kernel
state and publishes no partial value. Resuming uses the remaining rows/columns;
completion returns one ground Int through the existing primitive return path.
The number of digit steps is finite and bounded by n*m; allocation and final
normalization are linear in n+m, with checked lengths. Handler capture before
argument completion keeps the existing PrimitiveArgument frame unchanged.

The HIR unsupported-primitive probe and solver unsupported-operation probe used
int_sub solely as an example of the then-unimplemented intrinsic. With this
source-backed constructor added, move that negative probe to still-unsupported
int_div and add positive Sub/Mul identity, type and execution checks. This is a
recorded extension justified by the pinned signatures, not weakening the
unsupported-intrinsic-as-operation invariant. Parent theorem/source completeness
and independent review remain open; the local arithmetic derivation is UNREVIEWED.

Arithmetic source correspondence continuation: ordinary whole-source imports
previously omitted fully qualified value paths although selected member roots
already resolved them. Reuse that exact public-export resolver on the consumer
parse root, preserving missing/ambiguous outcomes and source identities. Explicit
`use` statement admission is a separate HIR item gate; this change does not claim
it closed.

Prefix negation exposed a second representation gap: association already owns
unary prefix/suffix applications and their declaration receipts, but LocalSource
accepted only binary infix. Generalize the retained operator application to one
required operand and an optional second operand. Formation checks the exact
fixity/arity (prefix or suffix = 1; infix = 2), syntax-node range, source key and
association receipt. The proof is a constructor case extension: instantiate the
original operator provider once; generate one ordinary Apply demand for unary,
two ordered curried Apply demands for binary; restore exactly the same FreshUse
and dictionary evidence. Unary's first result/effect are the final result/effect;
no fictitious second operand, computation or effect is inserted. Runtime mirrors
this by pushing one or two Callee frames in source evaluation order. Existing
binary slot numbers and source/use identity remain stable. This is constructive
source/native work, still UNREVIEWED, not parent A/B or general receiving closure.

The arithmetic constructor probe also found a source-name defect inside the
original prefix-minus provider: `IdentifierExpression::to_string()` retained
leading trivia, so ` std::int::sub` failed public-export lookup although the
LocalSource spelling was `std::int::sub`. Both qualified operation/value scanners
now take the Identifier token rather than the whole node text. This changes no
namespace rule and does not trim string literals or reinterpret source ranges.
The exact pinned prefix body `\x -> std::int::sub 0 x` consequently projects its
actual std/int dependency before capture. Whole-consumer and selected-provider
qualified paths now share the same identity-based resolver.

Parent application: the admitted literal/Name/Lambda/Apply constructor map gains
IntSub/IntMul's pure curried signatures and the unary operator's single real
Apply. Subtraction is composition of checked sign negation and the existing
signed-add routine. For multiplication, after complete row r the accumulator is
`sum(i<r, a_i * B * 10^i)`; inside row r, each advance replaces the current digit
and forwards its quotient carry, preserving that sum plus the unprocessed row
suffix. Base 10 division yields digit < 10, carry <= 9, and exact sum. Finishing
all rows yields |A|*|B|; the exclusive-or sign and normalized zero yield signed
A*B. At every step only the private Product changes; the machine's public result
is allocated once, after all rows finish. None of these local derivations closes
the original graph/source adequacy, principality or general receiving theorem.

More explicitly, write D for the numeric accumulator, c for the private carry,
and B = sum(b_k*10^k). During row r at column j the invariant is
`D + c*10^(r+j) + a_r*sum(k>=j, b_k*10^(r+k))
 = sum(i<r, a_i*B*10^i) + a_r*B*10^r`.
For s = old_digit + a_r*b_j + c, replacing old_digit by s mod 10 and carry by
floor(s/10) preserves the equality at j+1. At j=m, the untouched high digit
receives c, establishing the next row's base case. All previous rows have
largest possible written position <= r+m-1; this justifies assigning the carry
to position r+m rather than adding to an occupied digit. The machine kernel
stores these exact coordinates as row/column/carry and uses checked n+m sizing.

### Arithmetic checkpoint (direct primary, UNREVIEWED)

Connected pinned IntSub/IntMul signatures, arbitrary-precision decimal runtime,
resumable digit multiplication, qualified consumer/provider imports and unary
operator association/Apply/runtime transport. Exact source cases cover direct
primitives and std exports, binary precedence, prefix negation, generic and
partially applied products, large values, recursive handled operand effects,
left-to-right module writes, type rejection and withheld budget-exhausted output.
The dedicated live-machine test pauses inside multiplication and resumes the
same frames, cache and private accumulator. Source HIR checks both prefix and
suffix receipts/arity, including mixed binary and nested unary forms.

Verification: native yu-playground 262 pass (70 library, 58 primary CLI, 134
other integration tests); HIR shadow unary 1, primitive registry 1, import
resolution 2; solver candidate unsupported-primitive 1 and operator schedules 4;
fresh release WASM 46 execution examples plus original Types/Console/Effects
module output, three identity definitions and three expected diagnostics;
TypeScript passes. An initial HIR invocation without the candidate `shadow`
feature failed on feature-gated fields/types; the above HIR receipts explicitly
use `--features shadow`. No default-feature HIR success is claimed.
Logs: `target/r332-arithmetic-{native,hir-unary,hir-primitive,hir-imports,
solver-primitive,solver-operators,web,typescript}.log`. Rechecking unchanged
cooked original sources retains 6/19 expected behaviors; the remaining 13 gates
are recorded in `target/r332-catalog-cooked/results-after-arithmetic.json`.
Original sample bodies were not rewritten. Prior two solver baseline failures,
all-source adequacy, general receiving, principals, A/B and independent review
remain OPEN; those baseline tests were not reclassified or rerun in this slice.
Next: explicit import item admission and the remaining record/range/pattern
constructors through their actual source owners.
