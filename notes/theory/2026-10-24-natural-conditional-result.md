# Natural conditional results: retained graph and positive lower-head display

Status: candidate characterization and static source correspondence; unreviewed.
Author: `/root/natural_conditional_result_prover`, sole author, no descendants.
Assignment: `NATURAL-CONDITIONAL-RESULT-20261024/positive-projection`, note rev1.
Active contract: rev4, `tasks/agent-loop/sprints/natural-conditional-result-20261024-rev4.md`
in the primary checkout, SHA-256
`0009f4e037a1edbda567d3cf418bd43a7016e664ad20340f76a614e9946b7603`.
Source baseline: `d788d94da66385bf09947932f0aae1972cd51f21`;
assigned worktree `/tmp/yulang-natural-conditional-result-20261024`, branch
`codex/natural-conditional-result-20261024`; primary record-only start `b1130f5c8`.
No Git operation was performed to establish these parent-supplied identifiers.

## Parent and exact result

The original parent is implementation of Yulang inference and evaluation from
established proofs. Original Simple-sub/evaluator A/B, including their independent
quantifiers, remain OPEN. This note addresses the existing ordinary-inference
obstruction at `scheme.rs::heads`: two distinct concrete lower heads cause an
error before public display. The approved source rule in the October 11
principles §1.1 requires both branches of `if true { 1 } else { "str" }` to
contribute statically. This rule does not depend on evaluating the condition.

The result is a construction for a graph-generic display summary, applicable to
positive Value Leaf, Function, Tuple, Record and Variant heads, including nested
positive occurrences. It preserves the existing exported graph exactly and
shows every distinct concrete lower head together. It does not add a graph
union constructor, identify a row with a union, infer a principal scheme, or
establish accepted source typing. Source-to-parser/HIR observation and global
source/native adequacy are not supplied by this static audit.

## Frozen source dependencies

Paths below are relative to the assigned worktree unless otherwise stated.
All source hashes were read and matched; source files were not modified.

| Dependency | SHA-256 |
| --- | --- |
| `tools/inference-playground/src/scheme.rs` | `82019fd22ad565c753461d8962934fcfe8e6663f8a7971b4fcbc5f5067026be0` |
| `crates/yu-solver/src/candidate_source.rs` | `57b119592a6a8d4afd42aca10c5e2bb749cfdf0fb0fdea967dd437d552a1a04e` |
| `tools/inference-playground/src/lib.rs` | `45bf78af436efa50e02ca97ba3b639c11f7dd88272d87c47f2822643786653d4` |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `crates/yu-solver/src/candidate_scheme.rs` | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` |
| `crates/yu-solver/src/candidate_context.rs` | `33af2efb6ed782e4f143cccff03c62087e6ba8d0fbe90415846537fc2a08cec5` |
| `crates/yu-solver/src/shadow_apply.rs` | `f8d92f2d59353e5b9cda014545b352c8d6356cc0aff3b4eeae0e81893e78202d` |
| `tools/inference-playground/src/render.rs` | `cfdfdbc031ccc672c7eaa5b73355ec5f6bf5b1a97081e2ff9c9bb0060ab16568` |

Governing principles SHA-256:
`7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`.
R149 Types/Console authority SHA-256:
`1644743185363d3c258c606a2e65245b3db8206dddeb666d2994e2471d74f7fa`.
The directly called `output.rs` owns atomic byte/work limits; its hash is in the
handoff. No historical theorem or historical failure is a dependency here.

## Actual source action path

Use `my answer = if true { 1 } else { "str" }` to expose the exact approved
subexpression through `infer_types`, which displays binding roots. A bare
expression has no `HirItem::Binding` entry. This note has not executed either
source string or observed its parser/HIR identities.

Let the actual lowered `LocalSourceForm::If` occurrence have condition `c`,
then body `t`, else body `e`, result Value component `R`, and Effect component
`E`. Let the binding export root be `D`. These stand for source-owned identities,
not equalities introduced by this proof.

1. `candidate_source.rs::emit_candidate_source` assigns components to actual
   expression occurrences (around 1094). `Work::Visit` (1235) schedules the
   condition, body and else at the same level/region. It does not inspect the
   condition's Boolean value to choose a static branch. Source expressions
   start at level 1; `initialize_candidate_source_levels` installs those levels.
2. Literal `Work::Finish` (1556) emits `IntPositive <: V(l_int)` and
   `V(l_int) <: IntNegative`, similarly `StrPositive <: V(l_str)` and
   `V(l_str) <: StrNegative`, for the actual literal occurrences. Each literal
   also emits Effect-bottom and empty-Effect bounds. `append_source_facts`
   retains these as `Action::Fact` entries. If a branch body is a Group,
   Block or StatementBlock, its finish arm (2046/2082) emits an
   `Action::Candidate(CandidateRelation::Group)` from its final expression to
   that body's own component. Literal and branch identities are not assumed
   equal. Under rev4 the actual Group consumer was also inspected:
   `shadow_apply.rs::admit_candidate_fact` maps the child endpoint to Positive
   and its result component to Negative (4010). The shared tail (4160–4180)
   records the Group occurrence with slot 0 and its cause, then calls the same
   `constrain_live_value` on that pair. Thus the literal lower propagates
   through the body's actual Group endpoint before the If branch link.
   Group Effect admission (4195) is conditional on
   `self.batch.candidate_graph_effects`; when enabled it calls
   `admit_candidate_effect` at slot 1 with actual child/result Effect ordinals,
   records provenance and invokes `constrain_live_effect`. No unconditional
   Group Effect transport or general effect-hygiene theorem is claimed.
3. The actual `If` finish arm (1632) emits slot-50 `ValueConstraint` actions
   `V(c) <: BoolNegative`, `V(t) <: R`, and `V(e) <: R`; both branch actions
   have their own direct child's occurrence. It separately emits slot-51
   Effect links from the condition and both bodies into `E`. With no else,
   this owner instead discards body values and emits Unit for the conditional;
   that different existing rule is preserved.
4. For an unannotated binding the final `Action::Link` (2171) links its body
   endpoint to `D`. `execute_candidate_action` (2441) resolves every branch
   endpoint with `Polarity::Positive` and calls
   `admit_candidate_value_link`; the binding Link does the same with slot 30.
   The source schedule advances only after the action returns successfully.
5. `candidate_scheme.rs::admit_candidate_value_link_wide` (4781) records the
   source occurrence/cause, constructs the polarized live Value pair, and calls
   `constrain_live_value`. Solver `lib.rs` routes candidate sessions through
   `constrain_live`/`run_candidate_typed_drain` and its actual typed worklist;
   `apply_value_task` dispatches to `candidate_extrusion.rs::candidate_apply_value`.
   The legacy non-candidate transition is not evidence for this path.
6. Candidate Value application canonicalizes row identities and chooses a
   polarized owning bound from the actual levels. `candidate_insert_bound`
   appends into the appropriate `direct_lower_rows`, `direct_upper_rows`,
   `exact_non_variable_lowers` or `exact_non_variable_uppers` vector. Its
   immediate physical-slot readback checks the complete appended bound key.
   `candidate_replay_bound` pairs an inserted bound with every current opposite
   bound and queues the resulting typed task through the retained context join.
   For equal-level branch-to-result links, the branch owns an upper-row bound;
   replay against its literal lower queues `IntPositive <: R` or
   `StrPositive <: R`. Other level orientation uses a lower-row owner and its
   corresponding opposite replay. The final binding link transports these
   lower contributions onward to `D` through the same operation.
7. Ordinary source Value contexts are IDENTITY: `candidate_context_source`
   adds a weight only for a closed Effect allowance. Identity/identity replay
   remains IDENTITY, and `candidate_context_execute_relation` returns false
   for it, preserving ordinary dispatch. Replay children keep both input-bound
   identities, source sets and dependency records. The drain consumes queued
   tasks and diagnostics before successful return. This finite straight-line
   source trace is not F1/FK1, general termination, or whole-context adequacy.
8. `execute_candidate_graph_plan` completes source schedules before capture.
   `Capture::expand_row` copies every lower/upper lane for each captured local
   row; `Capture::bound` retains kind, side, endpoint identities and evidence.
   Shared rows intentionally stop expansion: their bounds stay at the outer
   owner. `CandidateInference::export` exposes the same captured graph only
   for an owned definition and an error-free candidate result.

Definition-root locality was checked under rev3. `add_definition_root` inserts
the DefinitionValue into `batch.components`; startup (`lib.rs` 10345–10363)
initializes every collected Value component at level 1 with `non_generic=false`.
Expression components receive the same initialization, with source-level
installation retaining level 1 for this straight-line example. This is not an
inference of final locality from initialization alone: the selected scalar
extrusion returns its original atom, equal-level row links do not copy a row,
and candidate bound insertion/replay does not lower levels or mark rows
non-generic. There is no annotation, function port, local instantiation or
copied parent/child pair on this selected path. Accordingly its root is local
at capture boundary 0. The rev4 Group consumer adds only the corresponding
positive-child/negative-result constraint on this path and does not change that
metadata.
The older non-candidate level-lowering loop in `lib.rs` 13579 is bypassed by
the candidate dispatch and is not used as evidence for this result.

The branch-specific upper `V(l_int) <: IntNegative` does not imply
`R <: IntNegative`. Transporting that upper to the join would incorrectly
reject the approved heterogeneous conditional. Preservation below concerns all
bounds already present in `CandidateGraphExport`; it does not claim capture
contains every branch/source fact or every top-level computation Effect.

## Representation and lower-head lemma

Let `G` be one successfully exported finite candidate graph and `P(G)` its
existing `CandidatePublicScheme::project` carrier. For each canonical Value
row `r`, collect `H(r)`: every distinct complete positive non-row Value node
`h` with an exported Value bound `h <: r`. Keep all original bounds, including
row-to-row bounds. Use exact node identity for collection; equal-looking nodes
remain distinct graph nodes. Effect nodes/leaves never enter `H`.

`H(r)` accepts Leaf, Function, Tuple, Record and Variant uniformly. It never
compares only outer constructor tags, merges payloads, selects a first head,
or distributes unions through constructors. In particular,
`(int, str) | (str, int)` must not become `(int | str, int | str)`;
two function alternatives must not become a function of unioned ports.
Record optional flags, ordered tuple elements, variant tags/arities and all
function ports remain the children of their original complete node.

For every interpretation satisfying all exported bounds, each `h` in `H(r)`
is below `r`; consequently their finite join is below `r`. For the selected
scalar heads this says `int | str <: r`. It does not give the reverse bound.
An arbitrary additional lower row, upper constraint or shared anchor remains
authoritative. Even in the elementary set interpretation, `r` may contain an
additional Boolean value and still satisfy those two lowers. Thus lower heads
alone cannot justify `r = int | str` or a principal/accepted scheme. If `G` is
inconsistent, unchanged constraints remain inconsistent; this lemma supplies
no satisfiability or acceptance certificate.

The display operation is a view `Summary(r; h1 | ... | hk)` for `k > 1`,
explicitly labelled as positive lower heads. It is not a new graph term.
The text may put `r` inline (for example `LowerBounds(α7; int | str)`) or use
an explicitly linked detail, but must preserve that identity and the summary
meaning. Render each whole head with ordinary constructor syntax and required
parentheses. Recursive descent uses the actual child polarity: only positive
Value-row occurrences may expand to this summary. Negative row occurrences
print the row reference with their retained constraints. A positive head's
negative function argument must not acquire a guessed union domain.

For newly summarized multi rows, mark the row referenced/free even when its
body expands. Retained-bound details must use the same named row (or an
explicit identity alias), not an unbound `rN` that loses locality evidence.
Existing zero/single-head presentation can remain unchanged; this construction
does not require adding vacuous binders to existing concrete single-head output.
Any change to negative single-head abbreviation must be explicitly reviewed;
there is no authorization here to infer a negative union from positive lowers.

## Preservation argument

The key separation is between retaining `P(G)` and computing `H`/text.

* **Nodes and structure:** `project` enumerates all graph nodes before resolving
  edges, stores each original `CandidateGraphNode`, its polarity and exact
  identity, and resolves every child to its corresponding node. Head collection
  and rendering read this carrier. Distinct equal leaves, whole structural
  heads, repeated row references and nested sharing are not identified.
* **Rows, anchors and quantifier identities:** rows are interned only by the
  export's existing canonical identity. Kind/locality disagreement is an error.
  First coordinates remain stable. `Capture::row` sets local exactly from
  `level > boundary && !non_generic`; display neither freshens nor changes this
  predicate. Value and Effect row kinds remain separate. A visible local row
  may receive the existing textual local binder; a visible nonlocal row receives
  the shared-anchor annotation and never a binder. Multi summaries must expose
  their row name as specified above. No principal generalization theorem follows
  from this display binder convention. Rigid/non-generic data remain owned by
  the untouched source state; the API does not expose a separate rigid flag.
* **All exported upper/lower constraints:** `project` iterates every `bounds()`
  entry, keeping its original `CandidateGraphBound` and exact lower/upper node
  references. No bound is replaced by a join equation or filtered because it
  conflicts with a displayed head. Render retains the complete bound-detail
  loop with shape abbreviation disabled. Hidden evidence remains at the source
  bound/graph owner; the text is not an injective serialization of all evidence.
* **Effects and permissions:** every exported Effect node keeps its complete
  typed operand (Contribution, AnnotationMember, OperationInterfaceMember,
  PermissionView or SupportView), including origin/owner/position/declaration,
  occurrence/member, labels, route/instance, and exact open-tail node/row.
  Every exported formal permission retains its occurrence, source row, port
  path, permitted prefix and typed Effect tail. Missing/empty paths or wrong
  tail kinds still error. Open tails remain open; different permitted labels,
  routes, instances, providers or witnesses are not unioned or identified.
  Effect bounds and their exact endpoints remain in the full constraint loop.
* **Solver operations:** all new work is after graph export. Generation,
  accumulation, typed propagation, levels, extrusion, qualifying intrusion,
  generalization and execution receive identical source and graph state. No
  solver operation is skipped or supplied a summary as an inferred equation.

Thus the retained references/fields recover the same nodes, bounds and
permissions, with rows interpreted modulo the export's already-established
canonical row identity. Raw alias-coordinate multiplicity is not a new
identity theorem: the existing projection keeps the first coordinate and
checks kind/locality agreement. The underlying export is unchanged, and the
set of retained constraint interpretations is identical before and after the
display extension. This argument concerns the carrier; pretty text can
abbreviate equal-looking leaves and does not prove all source constraints
were exported.

## Cycles, unsupported cases and bounded publication

Use an explicit rendering stack and an active-row set. A positive row expansion
keeps that row active until all its heads have been rendered. Re-entry into an
active row prints its identity, marks it referenced and ends that expansion.
This represents row-mediated cycles by references without solving a recursive
equation or dropping another head. Cross-row cycles eventually repeat an active
row. Negative occurrences remain references throughout. This also applies to
nested alternatives inside functions, tuples, records and variants.

Constructor-only cycles without a row backreference cannot be finitely unfolded
by this display. The existing per-step `Output::observe`, pending-stack limit
and byte cap must still reject them. Direct Effect operands where the existing
shape renderer reports an unsupported type node remain explicit errors; their
retained Effect details are not permission to invent Value syntax. Missing
identity/child/tail routes, malformed polarity/kind carriers, permission failures,
source conflicts and exhausted limits likewise withhold the whole result.
Ordinary structural multi heads are not an unsupported category: they are
rendered generically with their original children, subject to these exact limits.

Collecting heads requires one bound scan and identity deduplication, with at most
one collected entry per bound. A `(RowId, NodeId)` set plus per-row vectors gives
expected O(bounds + rows) collection work/storage; it avoids repeated linear
scans of a large head vector. Graph projection already bounds rows/nodes/bounds
by 4096. All alternative visits, delimiters and stack pushes must be charged;
`Output` caps observation work at 16384 entries and bytes at 1048576. Rendering
may repeat shared shapes until this cap; no uncapped expansion is required.
`infer_types` accumulates privately and returns `Err` on projection/render
failure, so a failed later binding cannot publish an earlier binding prefix.

## Parent application, falsifiers and remaining premises

For the selected binding, both emitted branch links feed distinct positive
heads into its result path. Given successful capture of that path, `H` contains
both IntPositive and StrPositive. Baseline `heads` rejects this pair by exact
node identity. The generic construction instead displays both as a positive
`int | str` lower-head summary, keeps all exported bounds and does not inspect
the source spelling or the condition. The public owner chain is
`infer_types -> prepare -> candidate_public_types -> CandidateInference::export
-> render::public_scheme -> CandidatePublicScheme::project/render`.
The same-HIR and conflict checks remain unchanged; failure returns no Types text.

Remaining evidence is explicit:

* `NCR-ROOT-1`: initial metadata and its capture join are established by the
  rev3/rev4 audit above for this finite path. Owner: solver initialization and
  `Capture::row/expand_row`; no local initialization premise remains here.
* `NCR-SOURCE-1`: the exact input's successful parser/HIR ownership and actual
  graph instance were not observed. Owner: `prepare`, HIR lowering and candidate
  source collection. The static argument starts at its actual lowered If form;
  existing test source is not substituted for this observation or proof.
* `NCR-GROUP-1`: the brace-body Group/Block/StatementBlock Value transport and
  its occurrence/slot/cause join are established by the rev4 audit above.
  Conditional Group Effect admission remains guarded by `candidate_graph_effects`;
  the note does not assume this guard establishes general effect transport.
* `NCR-IMPLEMENT-1`: Luna must implement the reviewed representation in
  `scheme.rs`, preserving every carrier field and fail-closed publication.
  This producer has not implemented, compiled, run or independently reviewed it.

Decisive falsifiers for review/implementation are: either branch slot-50 action
missing; a source constructor selecting only the true branch; a retained bound,
upper constraint, permission or row identity disappearing; negative-domain
union substitution; tuple/function/variant alternatives structurally merged;
an external anchor quantified; an open Effect tail closed; distinct effect
route/instance/evidence merged; a row cycle omitting an alternative; a malformed
or contradictory candidate published despite its error; or a cap returning a
successful truncated prefix. A root exported without the two heads falsifies
the claimed selected-path application and returns `NCR-ROOT-1` to its owner.

Reuse: the frozen candidate source actions, candidate-specific physical bound
retention/replay and existing borrowed projection are reused within their actual
premises. No historical failed proof or test was promoted to source evidence.
First-head selection, constant folding, scalar-only widening, union equations,
structural union distribution and inference bypasses are rejected constructions.
The next step is Luna intake, source-observation scope adjudication and fresh independent
review of these frozen bytes, followed only then by the leased implementation.
No parent A/B, F1/FK1, source/native or production gate is closed by this packet.
