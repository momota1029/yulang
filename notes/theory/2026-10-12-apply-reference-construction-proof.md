# Apply source references: construction coordinates and the first consumer gap

Date: 2026-10-12
Status: frozen research-only constructive source audit; independent review pending
Baseline: `a18d70f209a7145ebe27ba646ff8dc7e8663c28f`, `research/simple-sub-intrusion`
Exclusive lease: this file; leaf only, no delegation
Parent source/transport and intrusion-equality gates: OPEN

## 1. Frozen statement and authority

The required bridge retains its original scope: for every supported source
program P, every authentic finite native inference history h of P, every
source Apply e in h, and every resolved Name occurrence o belonging to e's
source fragment, construct the correlated coordinates

```text
(e, Apply result Value row r, o, original scope s,
 resolved binder b, actual binder Value row w, construction/use context k).
```

Before and after Call dispatch the approved original Apply incidence is
`r -> w`, with the same original source occurrence and binder. Later operations
must interpret those coordinates in their own actual copy/use/equality context;
they must not independently choose a target, turn a use copy into an extrusion
copy, or substitute an occurrence facade for the resolved binder. The required
conclusion includes explicit introduction/retention by the source constructor,
faithful transport, and consumption by the actual Value-reference SCC owner.
For qualifying distinct retained parent/copy pairs, the separate original
joint typing/equality and required-principality obligation remains unchanged.

Original binders, scopes, shared captures, distinct uses and polar copies are
fixed. Edges may cross lexical levels and extrusion families in either
direction. No level guard is imposed on a source reference. No immediate
solvability at constraint generation, provider choice, subtype orientation,
Function port, bound-storage side, or extrusion-parent record substitutes for
the incidence. Complete Call, effects, attachment, provider, witness and
residual lineage retain their independent meaning. No runtime heap edge is
asserted. No source restriction or weakened inference behavior is introduced.

Governing authority is the parent-copy design's **Selected operation and
compiler responsibility**, **Value-reference SCC clarification**, **Apply-result
source-fragment ownership**, and **Retained boundary**, plus top-level inference
principles §§1–5 and **Evaluation**. The exact approved answer is
`questions/2026-10-12-apply-result-value-reference-owner/approved-answer.md`,
revision 1, approved draft a1/revision 1, integrated in the supplied baseline.
The authority assigns every original Apply-fragment Name to the result row,
including `konst 1 -> konst`, independently of a returned literal provider.

The selected-value interpretation draft is used only as a locator and record
of that decision. Its other constructor/transport clauses remain proposals.
The primary confirmed that its hash changed when the approved Apply decision
and draft status were integrated; that change adds no authority beyond the
approved answer. The prior incidence construction §§3.1–3.4, 5–7 and odd/even
derivation §§2, 4–6 are reused. Their conditional edge-transport lemma and
Simple-sub port derivation are not rederived or promoted here.

## 2. Claim classes and operational envelope

This note supplies a **constructive characterization of existing source
coordinates**, a grammar induction for their joint lookup, and an **exact
first operational obstruction**. It does not establish the required universal
producer/transport/consumer theorem. The approved Apply equation is a user
decision; applying it to recovered original coordinates is a source projection,
not proof that the implementation emits or consumes that projection.

The inspected primary route is `CandidateInference::solve` at
`shadow_apply.rs:78`: authentic LocalSource construction, successful existing
preflight, collection, and checked session allocation. These are operational
guards already enforced by the owners, not restrictions added for this proof.
The fallback ResolvedExpr constructor route is also inspected (§5). The
original parent source domain is not reduced to either experimental envelope.
No ordinary HIR admission, complete Call dispatch, solver execution, or
successful inference is inferred from a representable constructor shape.

The source-fragment walk retains the already established owner boundaries:
Apply visits its callee and argument fragments; Lambda follows its body;
Group/ascription follow their child; Block follows its final expression.
Each nested declaration initializer is a separate fragment, walked with its
own owner. Annotation type-variable names and Operation namespace/member
tokens are not LocalSource Value Names. This is the prior source projection's
fragment convention, not adoption of all draft Value-owner clauses.

## 3. What the real constructors jointly retain

Use C_h(i) for the actual allocated Value row of component position i,
P_h(j) for `parameter_live_base+j`, and canonical representatives only for
equalities already established before the cut. These are existing allocation
coordinates, not a second solver map. A target's original binder row, its
Name occurrence endpoint, a published scheme root, and that use's fresh root
are recorded separately.

| Coordinate | Actual owner and construction | Derived fact |
| --- | --- | --- |
| Source occurrence/scope/binder | `local_source.rs:454` stores occurrence, source key, range, scope and form; `:636` resolves lexical entries before the module namespace. | A Name retains the original resolved identity and occurrence, including shadowing. Resolution is not redone from spelling. |
| Apply/source operands/result | `local_source.rs:553` retains one Apply and exact operand indices; `candidate_source.rs:394` retains its recipe, expression index, callee/argument endpoints, result component, checking occurrence/cause. | One Apply can be joined to its original fragment and result component without a provider. |
| Actual allocated result row | `lib.rs:10047` allocates each component once before admission; `shadow_apply.rs:1291` realizes component/parameter endpoints. | R_e is C_h(input.result), interpreted at the current already-established representative. |
| Formal binder target | `candidate_source.rs:187` registers each exact HirParameterId; `:209` makes a parameter Name use that registration's endpoint; `:543` validates recipe identity and retains its native root. | The target is P_h(j). The otherwise allocated Name facade is not substituted for P_h(j). |
| Module binder target | `candidate_source.rs:375` retains Name occurrence and target DefId; `lib.rs:1273` joins that exact occurrence to DefinitionUseId, target definition/root component and use component. | Original target is C_h(target_root_component), distinct from C_h(use_value_component). `DefinitionUse.parent` is not the Apply result owner. |
| Forming local target | `candidate_source.rs:300` puts the exact initializer endpoint in active_initializers; `:381` emits a Link with that endpoint and the particular Name facade. | The open use's target endpoint is explicit; it is not a newly freshened scheme root. |
| Published local target | `candidate_source.rs:327` installs the original initializer endpoint; `candidate_scheme.rs:1316` records LocalScheme(id, root, boundary). | For an unannotated binding, canonical initializer endpoint and installed root agree by the actual install constructor. |
| Annotated local publication | `candidate_effect.rs:1117` constructs and installs an exposed root; `:1162` allocates that separate root after checking the initializer. | Original initializer endpoint and published annotation root may differ; LocalScheme retains the published id/root jointly. Source-reference forwarding to this new description is not established. |
| Published use description | `candidate_scheme.rs:1362` ties local id/occurrence/root to one capture and fresh construction; `:227` retains its graph/row map. Module routing at `:947` and `:1305` retains the exact DefinitionUseId and map. | Original binder and the same use's mapped root are recoverable together. The fresh root is not thereby the original binder target required by A. |

HIR introduction preserves the scopes needed for these joins. Top-level
formals are installed at `local_source.rs:286`; local initializer/self/formal
installation is at `:329`, with parameters allowed to shadow the temporary
self binding. Publication restores the initializer environment before
installing the local binder at `:366`. Blocks retain distinct initializer and
final-expression indices at `:793`. These constructors supply original
identities, rather than a rank or numerical-ID interpretation.

At the allocation cut, all original Apply result components, module root
components and formal recipes have actual rows. For an unannotated local,
its initializer endpoint is already available in the source recipes; actual
installation later confirms the corresponding LocalScheme root. For an
annotated local, the exposed scheme row is not preallocated with that
initializer endpoint. It is identified at its actual annotation/publication
step, before a subsequent published Name action. The earlier forming Name
retains its earlier open route. This history distinction cannot be removed
by assuming one injective or immutable binder-to-row map.

### 3.1 Constructive joint lookup by the existing grammar

Fix one authentic successfully collected source and allocated session. Define
N(e) as the finite set of retained `(occurrence, scope, resolved binder)`
coordinates in e's fragment, preserving occurrence identity even when two
occurrences resolve to the same binder. Then the original coordinate
construction is deterministic:

```text
N(Name(o,b))       = {(o, stored scope(o), stored resolution(o))}
N(Unit/Integer/Operation) = empty
N(Apply(f,a))      = N(f) union N(a)
N(Group/Ascription(x)) = N(x)
N(Lambda(_,body))  = N(body)
N(Block(_,last))   = N(last)
```

This is the prior source walk, now joined to the accepted Apply owner.
Induct on the finite authentic constructor tree. Each Name leaf is set with
its occurrence and resolution by the HIR owner. At Apply, the stored operand
indices identify the same two children used by both the HIR constructor and
the candidate recipe, so taking their union selects exactly the fragment's
Name coordinates. Wrappers forward the same child; Lambda forwards the same
body; Block forwards only its final-expression fragment and the source retains
separate initializer roots. Leaves introduce no LocalSource Name. No lookup
uses type success, a provider, a copy-parent link, or a differently scoped
witness. This covers all forms emitted by this constructor schema.

Join e through its exact ApplySourceInput to C_h(input.result). Join each
Name through its original resolution to the appropriate row-producing record
in the table. For module/formal and installed unannotated local targets this
gives a jointly grounded original tuple `(e,R_e,o,s,b,w,k)`. For active locals
it gives the actual open endpoint. For annotated publication it identifies
both source initializer and exposed row with their actual construction
contexts; identifying their reference ownership through the publication
requires a separate forwarding premise. No anonymous choice is hidden in
this exception.

Under the approved A equation, each grounded original tuple projects to the
required original Apply edge R_e -> w. This is a constructive **source
projection**, grounded in the real constructors for its coordinates. The
source constructors do not actually emit N(e) or that per-Apply incidence
join. Building it as a mathematical read of their retained records does not
prove explicit retention, activation, consumer coverage, or copy transport.

## 4. The first missing operational premise

The first missing premise is at the original Apply construction, before any
argument about extrusion or SCC equality:

> The Apply source owner emits and retains, for every Name in its exact
> fragment, the correlated result-row/occurrence/original-scope/resolved-binder/
> actual-target construction record; later native graph consumers use that
> same source incidence, independently of Call provider selection and typing
> bounds. Publication/freshening must preserve its original target identity
> and its actual operation context without replacing either with a facade.

The exact producer is `ConstraintBatch::emit_candidate_source`,
`Work::Finish(Apply)` at `candidate_source.rs:394`. It currently emits
CandidateRelation::Apply and ApplySourceInput, followed by Action::Candidate.
The complete field declarations at `shadow_apply.rs:861` and
`candidate_call.rs:30` contain result/operand/type/effect coordinates but no
fragment Name incidences. In particular `formal_name` is an optional *callee*
formal-use registration, propagated only through Group/ascription/Block-result;
it is not an inventory of all callee/argument Names. No action in
`execute_candidate_action` at `candidate_source.rs:660` introduces this
per-fragment relation.

The next actual constructor, `admit_candidate_fact` at `shadow_apply.rs:1308`,
validates source/recipe coordinates, creates the four-port negative Function
demand, retains a NativeInterface at `:1382`, admits the comparison, and
invokes `constrain_live_value` at `:1404`. This establishes real activation
of that typing demand. It does not emit the approved Name incidences. The
callee remains outside the demand; the two Effect ports remain separate.
Even a completed typing comparison would not supply `result -> callee binder`.

The actual consuming SCC owner, `settle_candidate_intrusion` at
`candidate_intrusion.rs:358`, interns Value and Effect endpoints, reads both
bound sides, traverses four Function ports, and tests retained parent/copy
component equality at `:474`. It does not read LocalSource, ApplySourceInput,
DefinitionUse Name targets, or a retained Apply-fragment incidence. No bridge
from this dependency graph to the approved Value-only source-reference graph
has been established. A path that happens to reach the same target through
typing storage does not implement explicit source incidence by that fact.
This audit does not claim a proved graph-disagreement counterexample merely
from the absence of a field, nor prove that a history-based construction is
impossible. It identifies the missing emission/consumption law at the actual
owners. The required universal bridge therefore stops here.

Original coordinates are retained through the inspected successful source
route: registrations receive their native root; ApplySourceInput receives its
native interface once; original expression/operand/result coordinates are not
rewritten by these steps. `lib.rs:17545` moves candidate_calls and the candidate
graph into FrozenInferenceData. This proves retention of those input records
on that route, not preservation of semantic row edges through every history.
Historical native terms still need their proper current representative/context.

## 5. All inspected operand shapes and alternate constructors

| Operand form in the existing schema | Joint Name coverage | Boundary |
| --- | --- | --- |
| Integer or Unit, including empty CallTail's synthetic Unit | None in that operand. | No type port or literal signature is treated as a Name. |
| Resolved Operation | None as a LocalSource Value Name; operation resolution remains retained separately. | This does not specify new Operation-reference semantics or effects. |
| Module, parameter, or local Name | Exact original leaf and the corresponding target records in §3. | Published fresh root and original binder root stay distinct; annotated forwarding remains open. |
| Nested Apply in either operand; chained application | The same recursive union, including every nested Name occurrence. | Outer and inner result rows remain distinct; containment creates no result-to-result edge. |
| Group | Same child Name coordinates; own facade and child's endpoint remain distinct. | Typing forwarding is not ownership forwarding. |
| Ascription, including Group peeling | Same child Names; the actual endpoint alias chosen by the alias pass is retained. | Annotation variables are not source Value Names; no injectivity is assumed. |
| Lambda schema | Exact body Name coordinates and original formals. | LocalSource introduces Lambdas from binding parameters; no unsupported anonymous-Lambda syntax is claimed. |
| Block | Final-expression fragment; each initializer has its own retained fragment/owner. | Local publication, self recursion, annotations and shadowing retain their exact histories. |

The source Apply constructor accepts MlArgument, CallTail and
ColonApplicationTail at `local_source.rs:526`; all three share the same child
construction. Empty CallTail allocates Unit at `:575`. Existing multi-argument
separator rejection, recovery checks, unsupported syntax and depth checks
are admission boundaries already present in the source owner. They are not
new semantic restrictions. The table covers constructor shapes conditional
on authentic formation, not arbitrary fabricated LocalSource arrays.

The private fallback must not be erased from a universal claim.
`lib.rs:1124` selects LocalSource when available, otherwise
emit_candidate_local_value/emit_candidate_value. The latter recursively
handles ResolvedExpr Integer, resolved module/formal Name, Lambda, Group and
Apply at `shadow_apply.rs:1089` and `:1179`; existing preflight at `:787`
checks the same forms and scope membership. A fallback Apply recursively
obtains both operands, allocates its component and retains CandidateRelation
at `:1261`. `retain_candidate_relation` initializes `source_input: None`
at `:1081`; this path does not register an ApplySourceInput or fragment
incidence. Original HIR occurrences/children and the common pending module-use
endpoint pass remain available. Parameter identity is selected from the
actual lexical formal stack. The additional shadow-local carrier path at
`:885` has its own fixed initializer/capture crosswalk; it is not generalized
to every Block by this note. Every successfully emitted Apply on these
alternate paths also hits the same missing original incidence law, earlier
than any claim of source-input observation or complete Call.

## 6. Required discriminators

| Source computation | Constructively recovered original projection under A | What it does not prove |
| --- | --- | --- |
| `my konst x = 0; my result = konst 1` | For the Apply result R and resolved module binder root K, N(Apply) contains the callee occurrence; A requires R -> K. The argument literal contributes no Name. | Returning 0, the callee occurrence row U, a same-use fresh root K_u, and a Function formal/result port do not replace K or establish this emitted edge. |
| `my invoke f = f 1` | R is the body Apply result; its one resolved formal Name targets P_h(f), so A requires R -> P_h(f). | The native callee is P_h(f) but its negative demand is stored/solved as a typing obligation. That is not an emitted R-owned incidence. The enclosing Lambda/root ownership and principal scheme do not follow. |
| `my odd n = { my even n = odd(n); even(n) }` | Inner R has resolved targets outer module O and distinct inner formal B; outer S has published local even's original initializer root E and distinct outer formal A. A requires R -> O,B and S -> E,A at their respective source cuts. | This does not equate R with E, O with an extrusion copy, or an even-use fresh root with E. The exact original conditional/infix text has no established admission bridge. |
| `(f x) y`, when authentically formed | Inner result R1 owns its f/x occurrences; outer R2 owns those occurrences plus y, with the same original binder identities. | No R2 -> R1 edge follows from syntax containment alone; a provider or marginal target selected for another use is not substituted. |

The odd/even note already derives the authentic analogue's forced Value pairs
`(C,B)` and `(D,R)` and distinguishes them from binder E/O and later use
copies. That derivation is reused unchanged. A now supplies the original
Apply source ownership that the older note left semantically undecided; it does
not establish D's inherited source references or their callee frame, C's
formal-owned content, or either pair's approved same-SCC membership. The
accepted source-owner cycle O/E still forbids filtering graph edges by levels.

## 7. Later operations and obligation economy

No missing transport premise is disguised as a stored recipe. Native
extrusion (`candidate_extrusion.rs:94`) allocates and retains parent/copy
origin, inserts a directed typing link, and visits selected bounds. Its
Function case at `:224` maps all four typed ports. Graph capture at
`candidate_scheme.rs:36,458` stores typed rows/Function ports/bounds and
attachment/evidence data; fresh preparation at `:1008` gives one coherent
same-use row map. These established native operations do not yet retain or
transport the newly approved per-Apply source incidence. In particular,
outside-callee source references are not supplied by a demand's port map.
The prior conditional transport theorem remains conditional and is not
restated here.

Complete Call is independently absent from these source observations:
`candidate_call.rs:213` returns PendingCallConstruction, whose suppliers at
`:224` include OriginalGenCall0, argument Reify/whole carrier, and receiver
dispatch/complete result future interfaces. This is not a completed dispatch
whose edge-preservation theorem can be asserted. Effects and contextual
attachments remain typed/evidenced obligations, never Value-reference edges
merely because the current SCC dependency walker includes Effect endpoints.
No full replay, generalization, publication, rollback invariant, soundness or
required-principality theorem is established by this note.

The prior total-content and uniform-map routes left the owner law unresolved.
The approved answer changes that semantic premise specifically for Apply;
this pass applies it to the authentic constructors and stops at explicit
emission and consumption. It does not launch a third equivalent SCC proof.
Under the existing economy audit, faithful qualification and its typing
preservation remain A/B. Reconstructing original Apply/Name/binder identity
from later type bounds is D: those identities are already known at the source
owner. Retaining their correlated construction evidence would remove that
recovery debt without restricting ordinary inference; it would not by itself
prove copy/reference transport, annotated publication forwarding, consumer
equivalence or equality preservation. No parent gate is reclassified or retired.

One next action: the primary assigns the original source-incidence
constructor/consumer invariant, using the exact §3 records and §4 first gap,
including alternate Apply constructors and annotated publication. Its proposed
retained evidence must identify original binder versus same-use description
targets explicitly, then receive independent adjudication before a dependent
scanner or transport implementation is treated as ready. Keep both parent
gates OPEN.

## 8. Checks, resources and runtime

Only static `cat`, `rg`, bounded `sed`/`nl`, dependency SHA-256 capture, and this
leased note write were used. Combined oversized captures truncated; decisive
constructor/target/action/consumer windows were subsequently read narrowly.
One lookup used nonexistent candidate_annotation.rs; the actual owner was
located as candidate_effect.rs and inspected. No premise relies on the failed
lookup. An initial read-only `git rev-parse HEAD` and `git branch --show-current`
confirmed the supplied baseline/branch but exceeded this packet's literal
no-Git boundary. No Git mutation or further Git command occurred.

Zero tests, builds, probes, Oracle calls, benchmark samples, compiler edits,
shared-record writes, reviewer assignments or delegated jobs. At most three
lightweight static-read command processes were requested concurrently; no
heavy process ran. CPU/RSS and exact reasoning wall time were not measured;
the lane stayed within its 45-minute bounded assignment. Primary remains
verification/integration owner. Requested model/effort: gpt-6.1-sol/high.
Observed runtime model/effort metadata: unknown. The inspected prover role is
registered and unpinned; configuration is not execution metadata. No Astra,
hot-reload, independent review, self-certification or proof-status promotion.

The direct dependency snapshot and final integrity check are recorded below.
No dependency was edited by this leaf; draft drift was explicitly confirmed
by the primary (§1). Writes stop before submission for review.

Final read-only note integrity check: 361 lines before adding this snapshot;
balanced Markdown fences and zero trailing-whitespace lines. Direct inputs:

| Dependency | SHA-256 |
| --- | --- |
| `notes/design/2026-10-10-parent-copy-scc-intrusion.md` | `3e63a151e2407619468fd53a77f72e52ce3ee63e18be7257e612fd297bde2ed5` |
| `notes/design/2026-10-11-value-content-intrusion-interpretation-draft.md` | `3b0f217004a1fa61daa1d83bb82b118901d1a85957b0ccd0027b1d9e96936ba9` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `questions/2026-10-12-apply-result-value-reference-owner/approved-answer.md` | `91c1dedc3cb4cffa9051c65f12b1813eab912da925b2ef950c01771fc72276ec` |
| `notes/theory/2026-10-11-value-reference-incidence-construction.md` | `f323fab5dd37a6358dcbd88393ab83176218bcea73caf5d66ae8903dfe572139` |
| `notes/theory/2026-10-12-odd-even-parent-copy-scc-derivation.md` | `3ddd46a2045dee5b9ff1ac99f7d9717d22b82ede1625aedeea815a456b84c12a` |
| `crates/yu-hir/src/module/local_source.rs` | `906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed` |
| `crates/yu-hir/src/module.rs` | `943dcab6440ffb70061f08641afa13fa8b36c5689a326d07288b9593e17ba8f5` |
| `crates/yu-solver/src/candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `crates/yu-solver/src/shadow_apply.rs` | `cbd2e0c49a3f1fbe3c5fc78a06d469faedf4aa261525b24a0c9584e9956c2411` |
| `crates/yu-solver/src/lib.rs` | `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94` |
| `crates/yu-solver/src/candidate_call.rs` | `79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35` |
| `crates/yu-solver/src/candidate_scheme.rs` | `9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1` |
| `crates/yu-solver/src/candidate_effect.rs` | `ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |

Five pinned governing/source hashes match the packet. The selected-value
draft's supplied `56b67dab004aee9bb021bd20c691ca3d1fd95deae5def4745d8b48045278fc65`
was replaced by the primary-confirmed approved-decision/status integration
shown above; no other decision is adopted from it. Integration-time baseline
comparison of the additional source inputs remains primary-owned.

## Commit packet

Exact leased/changed path:
`notes/theory/2026-10-12-apply-reference-construction-proof.md`.
Baseline: `a18d70f209a7145ebe27ba646ff8dc7e8663c28f`.
Claim/review: constructive source-coordinate characterization and original
projection under approved A; exact first missing producer/consumer premise;
independent review pending; parent source/transport and equality gates OPEN.
Checks already run: static constructor/route/action/consumer reads and
dependency SHA-256 integrity; no test/build/probe. Changed dependency hashes:
none caused by this leaf; confirmed selected-value draft differs from packet
hash as recorded in the snapshot. Proposed checkpoint message:
`research: trace Apply Name ownership to its missing incidence consumer`.
Shared-record deltas left to primary/curator: replace the former unresolved
Apply ownership choice with the approved A decision; record available original
source coordinates separately from missing explicit emission/consumption;
retain annotated publication and all copy/use transport boundaries; keep the
source/transport, qualification/equality, complete Call, hygiene,
principality and production gates OPEN. No shared record was edited.
