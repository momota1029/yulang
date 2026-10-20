# R168 ordered tuple construction: source seams and consumer matrix

Date: 2026-10-20. Status: **UNREVIEWED CONSTRUCTION/CONSUMER MATRIX; no native tuple implementation
or complete correspondence theorem**. Author: `/root/r165_native_admission_proof`; no descendants.
Contract `ordered-tuple-construction-20261020-r168`, revision 1, SHA-256
`cb33b37ce48b7b2131e56cf3c3e510c5e24ac9177f743145966abf94479b8ce8`.
Frozen source baseline `6cd25179e573fc5ff822b0626f0ad440e7c58f89`; all eleven listed source pins and
R149/R167 pins matched. Later sprint documentation is not a replacement source baseline.

## 1. Parent application and actual result

R149 adopts arbitrary finite positional product values, preserving element types/order. The unchanged
parent remains proof-backed ordinary inference/evaluation and broad unchanged Web sample execution.
R168 must not encode tuples as nested pairs, erase a singleton to its element, or turn a tuple into
Unit/Group to avoid consumers. This matrix fixes the positional construction relation and identifies
the actual source, live solver, public graph, closed-type and runtime consumers required to realize
it. It applies that relation to the ordinary tuple constructor, rather than a theorem about sorting
an arbitrary list of already-created endpoints.

Current native source formation rejects direct comma tuple forms; current term/closed-type/runtime
algebras lack Tuple. Therefore this is not proof that actual current constructors emit tuple
constraints or execute tuples. The forward argument below is the reviewable construction obligation
for the adopted product operation, with missing native cases explicitly located. No tests or source
execution fill those cases.

Two source syntax seams remain: R149's prose does not explicitly settle the tuple meaning of the
parser-accepted `(x,)`, or multiple parenthesized children separated solely by implicit newlines.
The parser facts in §2 do not themselves adopt those meanings. **NO_SAFE_CODE_SLICE for claiming the
full source-syntax extension while those arity/syntax premises are unestablished.** This does not
reduce arbitrary-finite tuple support to pairs or permanently exclude either case. Luna must resolve
the exact adopted mapping before granting the corresponding code/public support claim.

A second important scope distinction is established from current source: candidate graph export is
not closed public scheme finalization. `run_candidate/finish_candidate` explicitly require
`finalization.is_none()`, `closed_types.is_none()` and empty schemes (`yu-solver/lib.rs:10446–10459`).
`CandidateInference::export` exposes a retained `candidate_scheme::Graph`, not a `ClosedValueScheme`
(`shadow_apply.rs:523–549`). Completing that graph path cannot certify tuple support in the distinct
closed-type pipeline. §4 enumerates both without pretending they are one route.

Original A/B, R166 ordinary-provider incidence, replay residual correspondence, R167 module scheduling,
public scheme correspondence, imports/roles/primitives/host writes and full sample behavior stay OPEN.

## 2. Authentic syntax, arity and recovery

`yu-syntax/expression/delimited.rs::parenthesized_nud_normalized` constructs one authentic
ParenthesizedExpression. Its direct-delimited loop emits actual children and punctuation in source
order. It checks the matching close before the separator/item branch, including immediately after
a trailing comma. It does not manufacture a second child when `(x,)` closes.

| Source shape | Checked current source fact | R168 meaning/obligation |
| --- | --- | --- |
| `()` | No child, matching close | Preserve existing Unit; no fabricated zero-element tuple source |
| `(x)` | One child, no comma | Preserve existing Group, including original child identity |
| `(x,y)` and longer comma lists | Ordered real direct children and commas | R149 positional tuple intent; arbitrary finite arity, not pair encoding |
| `(x,y,)` | Same two real children; accepted final comma adds none | Arity counts real children, never separators or a phantom final element |
| `(x,)` | One real child and direct comma; no recovery required by that close path | Exact singleton-tuple meaning is not explicitly settled by inspected R149 prose; preserve semantic seam |
| Multiple direct children separated only by implicit delimited newlines | Parser can reset Item phase without inserting a comma/missing separator | Parser acceptance alone does not settle Group/tuple source meaning; preserve semantic seam |
| Leading/repeated comma such as `(,x)` / `(x,,y)` | Item-phase separator emits a Missing expression | Preserve recovery refusal; do not count Missing as a value/Unit |
| Missing/foreign close, malformed item | Explicit Missing/Error/foreign-close recovery | No supported tuple carrier from recovery |
| Semicolon in parentheses | Explicit ExpressionDelimitedSeparator with error | Not an alternate tuple separator adopted by this packet |
| Nested tuples/parentheses | Direct children retain their own nested nodes | Never flatten nested products or inspect descendant commas as this tuple's separators |
| Commas in CallTail `f(a,b)` | Separate Call owner; current LocalSource rejects multi-item call tails | No automatic tuple-argument or multi-argument application rule follows from tuple construction |

No separate Oracle checkout/binary/sample was inspected. Luna explicitly required this source-law
audit to remain within this repository and pinned R149 authority. The mathematical relation in §3
is uniform in finite n; unresolved source mapping is not a pair-only theorem or a support reduction.
Existing resource limits remain checked limits, not new fixed arity semantics.

The immediate source supplier is `LocalSourceForm` in `yu-hir/module/local_source.rs:246–290` and
Builder::expression's ParenthesizedExpression branch (`:1107–1137`), which currently rejects every
direct Comma/ExpressionDelimitedSeparator, otherwise retains Unit or a one-child Group. A tuple
extension must retain an ordered vector of authentic `LocalSourceIndex` children; count only actual
supported expressions, validate local ownership, preserve parent/element SourceNodeKey and occurrence,
and push construction work in the appropriate reverse stack order without reversing published order.
The carrier's `order_occurrences` already assigns identities by original source-child order. The
retained-byte census must include new child backing storage.

The ordinary HIR/carrier seam is separate: `module.rs::lower_ordinary_admission` currently admits a
ParenthesizedExpression only as a no-comma one-child Group. Existing rich forms can have authentic
LocalSource alongside an explicit ordinary-HIR UnsupportedExpression placeholder; candidate
`solve_mode` accepts only the source-owner-authenticated placeholder path. A successor design must
say whether it adds canonical ResolvedExpr::Tuple admission or uses that existing carrier path.
It must not erase errors, pretend a tuple is the first child, or call the latter canonical ordinary
HIR tuple/public production support. See M2/A1 below.

## 3. Ordered construction relation and required proof cases

Fix one actual source tuple occurrence t, finite ordered element occurrences `e[0..n)`, their
existing source value/effect judgments, one shared satisfying assignment and original evidence.
For every admitted tuple arity, the desired generated constructor is

```text
T+ = Tuple+(v0+, ..., v(n-1)+)
each element evaluation effect Ei <= Etuple
Tuple+(a[0..m)) <= Tuple-(b[0..n))
    requires m=n, then generates a[i] <= b[i] for each original position i.
```

Every element is covariant within a Tuple of its polarity. A surrounding negative Function argument
still reverses the Function argument port according to its existing rule; Tuple itself performs no
extra polarity reversal. Equal arity is checked before traversal: ordinary zip truncation is not a
rule. Repeated elements preserve repeated positions even when their handles are equal. Nested tuples
retain nested constructors; heterogeneous children remain heterogeneous. This is not Union/Intersection
flattening, sorting or deduplication.

`Ei<=Etuple` is ordinary generation/accumulation, not evidence that every source effect executes or
that a non-least arbitrary satisfying assignment makes Etuple exactly a union. Any least/principal
claim keeps its owning Simple-sub proof premises. Evaluation effects of constructing elements and
latent effects inside returned Function/Computation interfaces remain distinct. A tuple must retain
all original child interfaces under one authentic reconstruction; it must not independently freshen
each element, split shared variables, or collapse provider/witness/residual lineages.

For source-to-native constructor induction the required cases are:

1. **Source formation:** parent t has exactly its authenticated ordered element vector; each child
   keeps its own occurrence and producer provenance. Nested construction applies the same relation.
2. **Generation:** obtain each existing element's Value/Effect components at its original level;
   construct the Tuple term from the ordered Value endpoints; add every effect edge without executing
   source code, constant folding or locally solving a special typing case.
3. **Comparison:** check constructor/kind/arity and derive only equal-position children, inheriting
   the actual relation's current context/source/scoped state with a justified Tuple-element rule.
   Do not reuse Function AE/RE stamp/protect/Swap operations as a shortcut. Diagnostic positions and
   actual relation-local consumers must retain index/arity, rather than only a child count.
4. **Capture/FreshUse/extrusion:** recurse over every same-polarity child using the same operation's
   maps; rebuild in original order. Continue ordinary levels, source-linked parent/copy retention,
   qualifying intrusion and replay. R70/R71's existing conditional premises remain conditional.
5. **Finalization/public view:** reconstruct equal-length ordered child slices with one shared
   quantifier/recursive-binder correspondence. No candidate graph observation substitutes for this.
6. **Evaluation:** under the adopted left-to-right rule, evaluate e0, retain its returned result,
   then e1, etc.; return Tuple only after all n results. Prefix `k` owns exactly the original ordered
   k results and an untouched source suffix. The next step advances k once or suspends in its current
   element; it cannot evaluate an element at a different index or publish a partial Tuple.

The operational source equation is the ordinary ordered Bind fold of the existing element evaluation
computations, ending in Return of the positional product. For Request(q,k), ordinary Bind retains
the same q and composes the remaining tuple suffix with k. A runtime tuple frame must preserve the
completed prefix, next index, environment, tuple source and original element slots through capture
and raw reentry. A cloned continuation retains completed results; it does not rerun earlier elements.
Independent invocations/multishot suffixes can execute their pending source work again under their
ordinary semantics: “once” is per actual tuple evaluation/resumption path, not a global memoization
claim. A tuple inside an unexecuted Lambda/delayed argument does not run when that code is stored.

The returned element value's own SourceSite can be an older definition/closure producer. It must
not be overwritten with the tuple element's Name/evaluation occurrence. Preserve both the original
tuple edge `(t,i,e_i)` and the actual returned value/view. In particular a Vec<ValueHandle> alone is
not proof that ReceivedValue interfaces/views survived: the proposed representation must retain
those actual child views or an equivalent constructor-owned association. An opaque outer tuple view
must not be promoted to a negative/nonprotection certificate by its runtime tag.

These cases are a constructive invariant/design proof obligation, not established native tuples:
the relevant native constructors are absent. Failure/rollback must not publish a partial accepted
tuple or inconsistent inference result; complete abnormal-state/capacity restoration is not promoted
to a new general correctness requirement.

## 4. Exhaustive consumer matrix for the inspected representations

**P** = required owner change for the existing candidate inference/evaluator constructor path.
**C** = additional required change before claiming closed/public type tuple support; not consumed
by `finish_candidate`. **A** = audited unchanged boundary under that declared path, with the precise
condition stated. All entries are obligations, not current code leases. A row spanning several
functions requires the whole named family, including its fallible/rollback adapters.

| ID / class | Exact owner and current consumer | Required correspondence / unchanged reason |
| --- | --- | --- |
| M1 P | `yu-hir/module/local_source.rs`: enum, Builder::expression, source bytes, order_occurrences, projection | Distinct ordered Tuple children; recovery/arity mapping settled first; never first-child Group projection; authentic parent/child identities and dynamic byte accounting |
| M2 P/A | `yu-hir/module.rs`: lower_ordinary_admission, pending projection/finalize_ordinary_admissions, lower_body/direct roots, evaluation_class | Successor must declare canonical HIR Tuple vs existing rich-carrier placeholder path; preserve original error IDs/owner and Unit/Group. Generalization eligibility does not provide module fetch class |
| M3 P | `yu-solver/candidate_source.rs`: Work::Visit/Finish, source action generation, levels/regions, Plan bytes | Visit every original child; one tuple Value constructor; all Ei edges; no Lambda/delay eagerness; scoped traversal/call guards explicitly audited rather than default-rejecting tuple subexpressions accidentally |
| M4 P | `yu-solver/candidate_value_graph.rs::retain_source` owner walk and fragment/incidence traversal | Reach Names in every tuple child under the actual value owner; preserve original Value SCC/qualifying event association. Do not make type-tuple adjacency the intrusion criterion |
| M5 P | `yu-solver/term.rs`: TermView/TermNode, kind/view, matches_endpoint, constructors, intern, pages/checkpoints/rollback/bytes | Positive/negative ordered product children of Value kind and same polarity; validate all branch-owned handles; exact arity/order in Eq/Hash; account dynamic child storage through clone/interner/journal/drop |
| M6 P | `yu-solver/lib.rs`: ValueEndpointKey/value_endpoint, constructor wrappers, ValueShape/incompatible_value_shapes, dispatch_live_item | Tuple endpoints retain structural term; Tuple/other mismatch and unequal arity produce honest diagnostics; equal arity yields all indexed constraints. No incompatible product disappears in `_ =>` or pair-only path |
| M7 P | `yu-solver/lib.rs`: typed drain/function dispatch, diagnostics, field ranks, retained memos, enqueue/route journal | Add/generalize an indexed structural-child protocol without conflating Function fields; actual Tuple child relation/context precedes endpoint memoization; preserve pending child/ack ownership and source diagnostic index |
| M8 P | `yu-solver/candidate_context.rs`: dependency/context construction and task transport | Justified covariant Tuple-element consumer; retain index, parent/source/current residual/scoped flow. Audit every Dependency match/lifecycle/bundle traversal if a new dependency variant is introduced; no identity-context fallback |
| M9 P | `yu-solver/candidate_extrusion.rs`: Visit, structure continuations, endpoint reification, Work::Bound | Same-polarity Visit/rebuild all tuple positions under one map; preserve selected raw BoundKey and exact witness. Dynamic arity/work stacks/resource sampling must be covered |
| M10 P | `yu-solver/candidate_scheme.rs`: Node, Graph bytes/capture/term_endpoint/expand_node, prepare fresh terms, retained maps, mapped_endpoint_at | Distinct Tuple tag plus ordered child storage; capture every child/required bound/context; shared FreshUse maps and reconstruction. Do not reinterpret four Function children as arbitrary elements |
| M11 P | `yu-solver/shadow_apply.rs`: CandidateGraphNode polarity/children/export, native Apply observation, CandidateRelation recipes if used | Keep existing Function children API authentic; add separate tuple-elements observation or tagged general structure. `children()->[Self;4]` currently means Function. Audit recipe Eq/clone/resource handling for a tuple recipe |
| M12 P | `yu-solver/candidate_call.rs::native_port`, source/native call validation | Recognize same-polarity Tuple Value ports where ordinary actual/result values allow them; do not declare Tuple callable. Preserve source-native demand/provider identities; scoped acceptance gates remain explicit |
| M13 P/A | `yu-solver/candidate_effect.rs` annotation traversal and source-bound evidence | Ei constraints reuse ordinary effect accumulation/evidence; structural tuple values do not fabricate new contribution/permission. New Tuple annotations are not supplied by source_annotation today; no accidental effect-tag inference |
| M14 P/A | `yu-solver/candidate_intrusion.rs` merge/recapture/equality/replay | Row parent/copy operations stay generic if Tuple is an exact atom/term whose children were already traversed by extrusion. Audit generic handling and resource fields; no new type-SCC rule or bypass |
| M15 P | `tools/inference-playground/src/render.rs::graph_into` | Tagged ordered product output; traverse all elements. Current structural rendering assumes four Function fields; do not print tuples as Functions or sorted row lists |
| M16 P | `runtime/program.rs`: Instruction, from_hir label/code conversion, source walk, named/self-ref walk, operation-v1 reachability | Lower each tuple's ordered authentic labels; walk every child for reference/closed-universe evidence. Existing module binding predicate needs a separately owned Tuple fetch law; no claim that its default-false branch is complete |
| M17 P | `runtime/machine.rs`: RuntimeValueKind/values, Evaluate, Return/Frame, frame capture/templates, SourceSite/value access | Ordered product result; next-element frame with retained ReceivedValue prefix/element slots; same current execution owner; suspend/resume preserves prefix. No function invocation or forced latent data merely because a Tuple is encountered |
| M18 P | `runtime/primitive.rs::closed_primitive` exhaustive Instruction traversal | Recursively validate all tuple elements before issuing any whole-universe negative certificate, or explicitly withhold that certificate. Tuple tag/ground-looking first element is not evidence for remaining elements |
| M19 P/A | `runtime/receiving.rs` views and RootCompSchema; `runtime/continuation.rs` TemplateNode::Bind | Preserve child interfaces/views; outer opaque unknown is not ground/nonprotected. Generic frame clone/Bind may remain unchanged only after its new frame's prefix ownership is proved. No Tuple receiving schema or projection rule is invented |
| M20 P | `tools/inference-playground/src/lib.rs` execute RuntimeValueKind match | Exhaustive new value kind handling; structural debug observation is distinct from source Display/say/println. No primitive/name special case or source-output compatibility claim |
| C1 C | `yu-types/lib.rs`: IndexedPositive/NegativeNode, indexed_validate, indexed reservation/visit conversion | Separate Tuple spans with arity/order; validate every child kind/polarity/reference; preserve duplicates; no reuse of Union/Intersection normalization semantics |
| C2 C | `yu-types/lib.rs`: PNode/NNode, positive/negative borrowed views, DP/DN, planned nodes, finalizer constructors | Ordered same-polarity product views and draft/plan/permanent constructors; no hardcoded pair; children remain valid arena-scoped handles |
| C3 C | `yu-types/lib.rs`: planning/commit, PermanentLane ordering, ArenaLengths/CommitRollback, scratch/retained accounting | Preflight dynamic backing before node publication; include new lengths/capacities in successful/failure accounting; truncate partial publication safely; draft children cannot escape transaction lifetimes |
| C4 C | `yu-types/lib.rs::alpha_p/alpha_n` and shared binder maps | Check equal length, then positionwise comparison with the same quantifier/recursive mapping across all elements; do not freshen each element or reorder for alpha equivalence |
| C5 C | `f5c_draft.rs`: PositiveNode/NegativeNode, FlatDraft spans/indexed/structural census | Ordered product tags in both polarities; translate spans and retain positional/multiplicity incidence; no Union/Intersection flattening |
| C6 C | `f5c_generalization.rs`: F5cPositive/Negative, F5cSummaryNodeKind, walker/sink tasks, endpoint conversion, finalization draft adapter in solver lib | Traverse/materialize all children under the same level/generalization map; update new kind rankings, semantic equality, bound dependencies and task arity. Full model/parent generalization gates remain open |
| C7 C | `f5c_generalization/flat_source_arena.rs` and `flat_walk_sink.rs`: source nodes, comparison/promotion/materialize tasks, checkpoints | Ordered child spans and same-polarity handles; repeated positions survive promotion; failed partial flat append restores valid source/draft boundaries |
| C8 C | `f5c_tree_analysis.rs`: term_rows, references/incidences/occurrences, guarded traversal, flat/boxed events | Visit every Tuple child; do not let `_=>{}` hide rows/recursive references. Any structural-guard choice needs the corresponding type rule, not a borrowed Function-only shortcut |
| C9 C | `f5c_binder_substitution.rs`: substitute_flat and boxed polarity adapters | One substitution map for all positions; preserve tuple tag/arity/order/duplicates, nested products and binder sharing |
| C10 C | `f5c_replay.rs`: replay_flat and boxed replay tasks | Replay every positional child and keep target variable/quantifier correspondence; reserve before moving ownership; retain rollback/diagnostic lineage |
| C11 C | `f5c_normalization.rs`: NodeKind, walks, sorting/comparison, rebuilding/promotion | Tuple is an ordered constructor. Sorting/dedup of surrounding unions/intersections must not sort/dedup its fields or identify differently nested/arity products |
| C12 C | `f5c_materialization.rs`: summary_flat_checked, iterative/recursive-bound adapters, memoized outputs | Preserve ordered children and per-occurrence multiplicity with one map; all output paths/rollback/resource handoffs covered, not only the flat happy path |
| C13 C | `f5c_draft_heap.rs` and solver/type retained ledgers | Account dynamic Tuple child ownership and transfer/release once; add exact tuple child kind/lane if needed. Do not restore withdrawn F5 source selection merely to expose tuples |
| A1 A | `yu-hir/lib.rs`, `yu-hir/shadow.rs`, `shadow_candidate_source_crosswalk.rs`, `shadow_initialization.rs` | Reexports/cold canonical-ResolvedExpr observers remain outside the selected LocalSource path only if canonical ResolvedExpr stays unchanged. Adding its Tuple variant requires a new exhaustive ordinary-HIR observer audit; no silent canonical support claim |
| A2 A | `yu-hir/module/source_annotation.rs` | Construction uses existing child expression types, not newly parsed Tuple type annotations/patterns. Annotation/destroy/projection support remains separate and explicit; do not change annotation parsing by accident |
| A3 A | `candidate_receiver.rs`, existing scoped Call authentication | Bounded operation/callee-source recognizers are not Tuple constructors; preserve existing explicit deferrals. Do not hide new ordinary Tuple value acceptance behind an unrelated omitted-callback selector |
| A4 A | `runtime/mod.rs`, `runtime/literal.rs`, parser delimiter/sequence owners | Existing exports/literal decoding and parser recovery can remain unchanged for the selected expression carrier extension. New public helper types may need explicit reexport; no parser semantic decision inferred from unchanged parser code |

The matrix enumerates every production structural representation/consumer family located by
TermView/TermNode, LocalSourceForm (including aliases), ValueEndpoint, positive/negative closed views,
indexed/draft/summary node and Instruction/Frame/RuntimeValue matches. Examples/tests were inventory
locators only, not execution or independent certification. A successor code diff must be checked
against these families; any additional owner gets a pin/lease before writing. This is a candidate
exhaustiveness argument for the named representations, not a proof that unspecified backends or
all future source consumers support tuples.

## 5. Clone, finalization, recovery and resource hazards

`term::intern:1062–1098` clones a node into the page, interner key and optional route journal.
Variable-arity children therefore require a real owned/retained-byte design. A shared immutable
backing can avoid three deep copies, but its allocation/temporary dedup peak, interner/page/journal
references, rollback/drop, branch sharing and O(1) retained-byte observations must be accounted.
`size_of::<TermNode>()` alone no longer counts child backing. Preserve branch/lineage validation
before publication and do not let a failed child reserve commit an unfindable node.

Candidate Graph nodes currently use fixed-size Copy structure. Ordered tuple spans or owned child
vectors must update Graph/FreshUse/scratch accounting and retained route transfer together. Source
capture, rows, terms, contexts, effects and attachment maps must remain one use's correlated maps.
The existing raw/canonical source witness gap is not solved by storing a vector.

Closed types have separate indexed, draft, planned and permanent representations, and both flat and
boxed solver adapters. A product in one representation cannot default to Bottom/Top or an unvisited
node in another. Existing positive/negative child buffers may be backing storage, but Tuple requires
its own tag and ordered interpretation. Product span overflow and partial constructor publication
must return honest failure. No pair decomposition or private tuple-to-union conversion is adequate.

Runtime continuation capture stores ordinary frames through TemplateNode::Bind. The new frame's
completed prefix must remain flat handles/views, not a recursively cloned runtime value tree. Each
raw invocation receives its own progression state while sharing only immutable completed results;
capturing a request must preserve the actual tuple environment/owner/suffix and already performed
effects. Step exhaustion/unavailability cannot return a fake completed or partial product.

Source recovery remains owner-controlled: never turn Missing into Unit, silently discard a comma
item, erase a genuine diagnostic, flatten a recovered nested tuple or choose the first child. This
matrix grants no expected-output edit, test, probe, compiler execution or general rollback expansion.

## 6. Remaining premises, falsifiers and implementation boundary

**R168-SOURCE-ARITY-1:** authenticate the exact singleton/trailing-comma and implicit-newline source
mapping under R149's adopted syntax authority. Current parser facts are explicit in §2; meaning is
not independently established by that parser. Owner: source semantic decision -> LocalSource
ParenthesizedExpression constructor. **NO_SAFE_CODE_SLICE for a complete source-syntax claim until
resolved; arbitrary finite scope remains unchanged.**

**R168-NATIVE-POSITION-1:** implement/review P rows and establish every source-to-live-to-capture-to-
consumer-to-runtime positional case in §3, preserving effects, source slots and actual received
views. Native tuple constructors/consumers are currently absent; the construction lemma is not
their source correspondence. Owners: exact P rows; Luna grants exclusive code leases only after
review. Nested/heterogeneous data, shared-variable use and suspended evaluation cannot be replaced
by a literal pair fixture.

**R168-PUBLIC-CLOSED-1:** decide and state whether the successor code grant includes C rows. If it
does, all closed producer/finalization/comparison paths need corresponding updates and proof. If it
does not, public closed scheme tuple support remains absent/OPEN and cannot be inferred from
CandidateGraphExport. This is not permission to revive withdrawn F5 algorithm selection.

**R168-TUPLE-FETCH-1:** before claiming source-required Tuple binding startup, provide its actual
source fetch-class rule at the module schedule consumer. Adding Instruction::Tuple otherwise reaches
the current default-false predicate. This packet authorizes no module completion/schedule change;
R167-CASE-FETCH-1 remains separately OPEN.

Falsifiers for the successor proof/code: unequal arities silently zip; `(Int,Str)` equated to
`(Str,Int)`; nested positions flattened; repeated positions removed; child variables freshened
independently; an element effect/latent interface dropped; a tuple value overwrites a child's
producer SourceSite or loses its ReceivedValue view; an unexecuted argument's tuple runs eagerly;
request/resumption reruns a completed prefix or skips/reorders the pending suffix; failed reserve
publishes inconsistent tuple/type state; candidate graph output is claimed as closed public typing.
These are discriminating obligations, not tests run or source counterexamples found here.

No full native theorem or code eligibility is certified by the author. The original tuple scope,
inference algorithm, shared assignments, original witness/provider identity and parent quantifiers
are preserved. Fresh independent review and Luna's exact scope/authority adjudication remain required.

## 7. Byte pins and stop receipt

Initial pins match the contract; additional inspected owners are pinned below. Hashes identify
read-only dependencies, not write leases. Paths beginning `solver/` mean `crates/yu-solver/src/`;
`runtime/` means `tools/inference-playground/src/runtime/`; `hir/` means `crates/yu-hir/src/`.

```text
R149 adopted design 1644743185363d3c258c606a2e65245b3db8206dddeb666d2994e2471d74f7fa
R149 rev10 contract 31214917352b673c7467873b60d5db8e470e4d16c8370d882c266a7fcef5b3e9
R167 closeout b24bb26e28e6af2b42bc6a48d95b8f013de5224550b137c7bbe6745f479ef7cf
crates/yu-syntax/src/expression/delimited.rs e65c4d500ce0878faf13f1a8d31da816e5db9b6af4690b505c8875d27b700f95
crates/yu-syntax/src/sequence.rs 1a68331e5d16d46471545e673226541dc848123d1c3e286260359cecf41adcd2
hir/module/local_source.rs d9f516993c579ae8f4dd905abb8400ffc0769072a904a4b4c8d4ffbefcde6442
hir/module.rs 153a23ecaa68fd150d8bd0cc0316f3723e1cb5d98a6e3026aadef2bfd08fd907
hir/module/source_annotation.rs b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f
hir/lib.rs 8f6e2b688418dbdb4e2c551cbd9b7b58c809623d492f2da6f7d29cc64189d8d8
hir/shadow.rs ae5f40a9b1d34d08938eb23b8bc3d1756411d146b5c83ba73b7294f5d332a654
crates/yu-types/src/lib.rs c6587027612157c070a1b27b297a9f5aeec066422cf550eb78e3ec4828f0aa6b
solver/term.rs f3a0c3875ba1ba8c80ee48a405faf3dad22b57cba8930394f99181201bc58f60
solver/lib.rs c75bf47b3d0d87e99d4365a587e6b90d5d05d05c335db16880cb2943b8b25985
solver/candidate_source.rs cbc39315f4243b0bae1db74976cf94282bc94cd28b9eb463699c085f421065f7
solver/candidate_scheme.rs 2e64dc8781189b4da21c30f4d1b3208aaef48ca247cae55fb7e77e68b5857850
solver/candidate_value_graph.rs 19da9779e3e7866f5891e019e1cd343136ae0115bd1c47a02a7e7ee0cdfa80e0
solver/candidate_extrusion.rs 7c9a46d327a5e2e3f9e6f8d79f36f11fe21b4a3f68426526e85424a39e2c6332
solver/candidate_context.rs 93ff11f005c9e29e007d2a21479779dd14ff462a41da9c937a0e6a48fc1603be
solver/candidate_intrusion.rs 475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97
solver/candidate_effect.rs c1d7ce19ef5192a46d605faabae34e4437b1f1a15819b5657ec1d70eda7900d1
solver/candidate_call.rs e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479
solver/candidate_receiver.rs 620b09011ec4dc4bfa71998e2b6fc1498b9299b3056662fdaa80b17376ba23c3
solver/shadow_apply.rs 838d862dd34fe2b2bd70c5d92c5ce9af0aa98f10f8b6a8eddf313ae798686543
solver/shadow_candidate_source_crosswalk.rs 392d665579a74810134846e1274c0c9ce975a7eb0e2cfb9ad79a07af2cd2eeb0
solver/shadow_initialization.rs 6ea0914a11a4a05d6dde8d63c413cfd42fb887596b3315d998848d502a91715a
solver/f5c_draft.rs cb67684c633214878c1795d896aca02b525ebf8de4e5cbd3aaf8de7a8e6c433d
solver/f5c_draft_heap.rs a45034e89923711b49c82aceb7937eebf5e0c59e6e9edabd80c114a760424020
solver/f5c_generalization.rs 928607961bff9ab747fd759aed1dacd3aa13abc9e20bf3bb8a957a4c7bd12ffb
solver/f5c_generalization/flat_source_arena.rs 0abc91b90303818bd372bc33d1e391e24a2bb747df70984cad8f54f5d60f3af7
solver/f5c_generalization/flat_walk_sink.rs ff8b117e7578d93f1d441faec132df4859b7118c5a0d56d1044dbb3f2ab913b1
solver/f5c_tree_analysis.rs f69fb7938dd22ba6cc65b8a1474e9e3f05c30af106c3ca110778b4a225807173
solver/f5c_binder_substitution.rs 6b2d9d53546fc2218132dad65fac8619ec125c65817af5fe42239ebc85ffee80
solver/f5c_replay.rs 71fb166c38dbd93571abcbc3ff290b3b79fe2a4ecba8159edd5f60933c8b3b2a
solver/f5c_normalization.rs da57ee8fc3dd3a604ef5bf65457cf0c4d38fb976eb9e080e8520ea6a1e97728a
solver/f5c_materialization.rs a342860980dc14dd6dc10996adf992946e1b420b6d3d8ee176a77937d0c6a93b
runtime/program.rs 28748da0458da92b9d1190b250bbb84bdecc6643718eacbca95a04f5d6c9aa0d
runtime/machine.rs 875213902660c06ffa393c8fef001c4e67d229486fed6ef8773c6abd9a3b23f1
runtime/primitive.rs da1beeb825ffe5263733a88955d3061372e34b74cd585bb4006a070f7adefc57
runtime/receiving.rs 8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9
runtime/continuation.rs 194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3
runtime/mod.rs 64d208743793a03501a76f56bc2b511c50ed40cff3f789757a00b7d608fc846b
runtime/literal.rs 2fff177a7ba0cabb4930251e1facc8f9be701ff3ec7baa695ce4c182fa1da35f
tools/inference-playground/src/lib.rs a0769f77feac552304f0516b0742637f51660c0bb8bf9391d18ae0f9de5e2473
tools/inference-playground/src/render.rs 86dba831366995d4c36e2446c9b8e6847f7bff524d5e7e7b6d12d02ff337fc66
```

Checks: exact hashes, direct constructor/consumer inspections and bounded source searches; no tests,
builds, compiler/runtime/Y2/Y3 execution, instrumentation, source/code edits, network, Git commands
or descendants. No generated/scratch paths. Requested model/effort UNKNOWN/UNKNOWN; observed
UNKNOWN/UNKNOWN. Fresh launch observation 14:23:12 UTC; cap 1500 seconds, Astra 0, no carryover or
extension. The exact remaining source seams/consumer scopes are the stop condition, not a claim
that a tuple implementation or the original goal finished. Frozen for fresh independent review;
all writes stop with the exact result handoff, no descendants/background activity or other leases.
