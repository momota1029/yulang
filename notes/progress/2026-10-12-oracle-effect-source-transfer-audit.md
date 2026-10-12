# Pinned Oracle effect source transfer audit

Date: 2026-10-12
Status: frozen unreviewed research checkpoint; parent hygiene and negative-formal gates OPEN
Method: independent pinned-source correspondence audit, not constructive theorem review
Y3 baseline: `0e621f549035537e4d3e799c78f79dd9385df350`
Oracle baseline: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Exclusive lease: this file only; leaf, no delegation or Git mutations

## 1. Objective and authority

Trace the actual Oracle composed-negative formal Function result-effect
constructor through its direct formal call and enclosing output. Map each
operation to Y3's existing approved contract and actual owners. This packet
is independent of the current Value/type-occurrence association investigation.
It supplies source evidence and a minimized missing bridge, not a replacement
proof of that investigation or of universal hygiene H.

Authority: [annotation effect hygiene integration](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–5; [concrete annotation implementation](../design/2026-10-10-concrete-effect-annotation-implementation.md)
in full; [contextual attachment admission](../design/2026-10-10-contextual-attachment-admission-design.md)
§§3–6; [top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
in full. The referenced [residual lineage selection](../design/2026-10-10-contextual-residual-lineage-selection.md)
fixes constructor lineage rather than residual-key coalescing. Governing sections
are semantic authority; Oracle code is comparative implementation evidence.

Retain the accepted decisions: composed-negative `[E]` permits function-local
subtraction at the exact position; composed-positive `[E]` permits concrete E;
symbolic variables retain connections and later concrete checks. One exact
annotation set owns one attachment identity with member ordinals. Same nominal
support does not merge attachments or independent contributions. The withdrawn
`run_io` callback scheme supplies no expected result. Concrete-formal admission
and generic mixed-component termination remain later gates. Abnormal paths need
no wrong typing and no inconsistent publication; full restoration is not a
general premise.

Inputs include the independently reviewed conditional singleton
[negative formal source proof](../theory/2026-10-11-negative-formal-effect-source-proof.md)
§3, the independently reviewed bounded P/Q
[Y3 source bridge](../theory/2026-10-11-oracle-effect-hygiene-source-bridge.md),
and the frozen, awaiting-review [global H derivation](../theory/2026-10-11-oracle-global-effect-hygiene-proof.md)
§§1–5. Their review/status boundaries are retained. This audit does not certify
those artifacts independently or promote their claims.

## 2. Claim classes and explicit hypotheses

**Derived bounded source construction:** in the direct formal singleton spine,
the paired annotation PUSH and direct-call/frame-output POP have the same
fresh SubtractId and declared concrete set. The derivation below checks pinned
owners independently of the prior note's prose. It proves emitted construction,
not universal contribution preservation or successful worklist completion.

Hypotheses: one live Oracle arena; successful source resolution and completed
constructor calls; fresh allocation without ID exhaustion; an ordinary
non-wildcard nullary concrete result-effect row; a callable annotation with no
effect wildcard anywhere (the actual `callable_annotation_has_effect_wildcard`
guard scans the whole annotation); actual local formal binder; actual direct
`Expr::Var` application in the corresponding defined-lambda frame. No
intervening generalization transformation is included in this local statement.
This last exclusion bounds the lemma, not H or supported language. No provider
body is selected: the recorded singleton has a formal callback but no
implementation of its actual future provider.

**Conditional algebraic fact:** given the emitted ordered operations, composing
PUSH_i({E}) with POP_i cancels that ID's unit count. A POP_i does not modify the
j entry for j != i. This is ID-local arithmetic, not a theorem that every
independent source emission has such a j, reaches an output, or survives every
row projection.

**Missing semantic transfer:** the original H quantifies over every successfully
lowered source, negative occurrence, actual copy/use and coupled call/output
route, including future lowers and independent same-family contributions. The
local construction above does not establish its export/use or all-path consumer
premises. No counterexample to H is claimed. Source files are available;
the necessary source observation-preservation argument is underdetermined.

## 3. Exact Oracle constructor and direct call/output spine

All Oracle locators in this note refer to Git objects at the Oracle baseline,
read with `git -C /home/momota1029/rust/yulang2-oracle-capture show <SHA>:<path>`.
No Oracle worktree source or its uncommitted instrumentation was consumed.

Use the previously recorded shape `my f(cb:(() -> [tick] ())) = cb ()` solely
to name the spine: f is the owner, cb the formal, a the row occurrence, E the
resolved nullary nominal operand, k the actual application. This packet did
not execute it or revalidate its historical binary dump.

1. `annotation/constraints.rs::connect_parameter_computation_detailed:251–282`
   enables the parameter Function boundary. `connect_value_detailed:124–137`
   emits `A+ <: cb` and `cb <: A-`, returning `output_subtracts`. These are
   actual paired edges, not imagined equalities.
2. `lower_value_bounds:363–390` constructs both four-port Function interfaces.
   Argument ports reverse; result ports preserve. `lower_ret_effect_bounds:424–470`
   obtains q and allocates the stack via `effect_row_stack:657–690`. For a
   nonempty concrete set it allocates one fresh i for the entire set, excluding
   annotation variables at `effect_atom_con:741–748`. `function_boundary_effect_stack_inner:602–620`
   takes the actual named tail or may reuse a closed-row coordinate. Sharing q
   does not share this freshly allocated i. `connect_effect_tail_exact:636–654`
   emits both variable directions where an exact separate tail connection is
   needed.
3. The immediate result Effect pair is
   `Stack+(q,PUSH_i({E}))` / `Stack-(q,FILTER({E}))`. Declared stack facts are
   registered at `590–599`. `predicate_weights:921–924` returns
   `POP_i.with_filter({E})`; the positive returned Value also carries it in
   `NonSubtract` (`373`, `848–851`). Only this Function's immediate result
   `ret_eff.subtracts` is returned at `389`. Descendant Function predicates
   are not automatically this binder's immediate call predicate; tuple
   concatenation at `335–348` is a separate branch.
4. `lowering/expr/lambda.rs::connect_lambda_pattern_annotation:1244–1341`
   retains the connection as `call_predicate`. `lambda_annotation_predicate_constraints:1581–1626`
   has wildcard and Effectful-specific branches. For the ordinary Function
   spine, its immediate parameter-output predicate is empty
   (`lambda_parameter_output_predicate_constraints:1571–1578`). The actual
   pattern locals are formed and then marked at `708–741`;
   `mark_lambda_param_call_predicate:919–942` stores the exact weights on those
   locals and records their frame. Declaring the Function formal alone does
   not install its POP into the enclosing output predicate.
5. `lowering/expr/tail.rs::local_callee_def:844–852` accepts the actual
   `Expr::Var` and resolved DefId. `local_callee_call_projection:690–705`
   retrieves that local's predicate. `make_app_with_origins:535–624` extends
   the current frame's latent predicate using those exact weights (`551`,
   `719–725`), builds the four-port call demand, and connects both callee
   evaluation Effect and this call's return Effect to the application Effect.
   `unannotated_local_callee_return_effect:740–798` returns bare call ports for
   the annotated formal (`756–758`); its different unannotated-argument ID
   mechanism is not the concrete annotation constructor.
6. `tail.rs::lambda_predicate_subtracts:1058–1072` collects the defined frame's
   latent predicate. `lambda_output_predicate_vars:1092–1109` wraps both
   actual body Value and Effect. The defined skeleton likewise wraps the
   current body endpoints and forwards to actual output coordinates at
   `lambda.rs:1195–1237`. `expr/constraints.rs::wrap_pos_with_subtracts:137–144`
   creates `Pos::NonSubtract` with the same weights. Thus the emitted output
   POP_i is paired with the source constructor's PUSH_i, through the actual
   local call, not through a guessed equivalent row or provider.

The separate signature owner is not interchangeable with this paired formal
owner. `lowering/mod.rs:571–663` reverses Function arguments and preserves
results. `signature_effect.rs:78–107` builds ordinary positive row/tail
operands; `162–178` builds a negative result filter around the boundary row;
`19–37` instead connects ordinary negative argument effects to a concrete lower.
No blanket rule that every negative textual port emits the same pair follows.

## 4. Actual consumption and its limits

`constraints/machine/propagate.rs:11–56` prefixes positive Stack/NonSubtract
weights and checks the negative Stack before consuming its filter wrapper.
Its Function case `210–267` swaps Argument Value and ordinary Argument Effect
contexts, preserves Result Value/Effect, and separately uses `both_from_right`
for pure argument passthrough. `constraints/mod.rs:3566–3607` implements swap,
prefix/suffix and ordered replay mix. `directed_weight.rs:145–170,399–419`
selects the exact ID before merging its counts/family. Equal E is not the
cancellation key.

Retained filters have live consumers: `bounds.rs:3213–3255` registers on the
actual variable before scanning existing lowers; `3285–3360` invokes weighted
checks and recursively registers on encountered variables. The new semantic
lower insertion calls that routine at `714`. This corroborates the prior
machine-local invocation lemma. It does not prove every queued payload check
drains or every source/copy reaches this variable. The prior H derivation also
identifies alias-count subsumption and omission paths; this audit does not
redo their all-path coverage.

`constraints/row_effect.rs::add_effect_row_upper_bound:88–234` is the real
weighted residual owner. It checks concrete heads against the left filter,
checks the self-tail branch, computes retained heads, and can forward directly
when no heads remain. With retained heads it builds gamma and emits BOTH:

```text
source <: Row(retained_heads, gamma)             feedback, empty weight
gamma  <: this exact tail                      residual left / actual right
```

The key at `180–184` is `(source, sorted retained families, residual_weight)`.
Reuse retains derivations and still emits both edges (`185–233`). These are
real enqueues, not proof that an independently chosen gamma/output witness is
correct. `subtract_row_items_from_left_stack_weight:1190–1216` processes every
active left entry's family; the earlier ID-local cancellation lemma alone is
therefore insufficient to justify the complete row reduction. Independent
source-contribution coverage and correlations must be established at these
consumers. This is a proof boundary, not a demonstrated bug.

Oracle residual-key coalescing is not transferred. Y3 requires distinct
constructor lineages even if sources or residual keys become equal, applicable
current/future lower fan-out to each recipe, and each recipe's exact outgoing
gamma projection. Row equality remains governed by selected extrusion and
qualified parent/copy intrusion.

## 5. Correspondence to current Y3 owners

| Oracle operation | Y3 owner at baseline | Established scope / missing operation |
| --- | --- | --- |
| Resolved row, symbolic tail, lexical formal | HIR `source_annotation.rs:349,399–505`; `local_source.rs:289–300,730–788`; `candidate_source.rs:184,274–282` | Retained source occurrence, operands and scope; metadata is not an emitted contribution. |
| Paired formal Function graph | `candidate_effect.rs::candidate_formal_pair:1034–1070`, `candidate_formal_annotation:1073–1111` | Both Value edges and retained formal domain exist for admitted forms; Negative concrete rows reject at 1035/1070. Source preflight rejects at `candidate_source.rs:98,117–121`; signature constructor rejects at `candidate_effect.rs:1507`. |
| Set-wide attachment identity and PUSH | `candidate_signature_view:733–774`; `candidate_context.rs::source_weight:2174–2195` | Source set/ordinal/scope retention exists for supported views, but executable words are empty. `SourceUnitPush` is only positive preparation; `materialize_unit_push:2200–2222` is detached and creates no live relation/bound/recipe. |
| Actual four-port call and Effect forwarding | `shadow_apply.rs::admit_candidate_fact:1308–1447`; `candidate_source.rs:394–408` | Validates actual source input; allocates invocation row at application level; forwards invocation and callee evaluation effects. No concrete formal call-local subtraction predicate is emitted here. A native interface record does not prove whole-argument provider compatibility or complete Call. |
| Function context transport | `candidate_context.rs::candidate_function_port_admit:2557–2608`; `lib.rs:12493–12563,12643–12668` | Actual parent post-check context, argument Swap, result Preserve. The inferred-entry certificate is separately retained by the Lambda owner; it supplies no missing attachment or general `both` permission. |
| Enclosing lambda Value/Effect output | `lib.rs::admit_lambda_fact:11233–11369` | Uses retained formal domain; joins actual body Effect and inferred entry into return Effect; publishes the actual Function. No paired concrete annotation POP wraps body Value/Effect here. |
| Current/future concrete checking | `candidate_effect.rs::candidate_check_effect_operand:888–958`; `candidate_extrusion.rs:406,763,840`; `candidate_context.rs:2911–3110` | Support/Allowance with actual opposite-bound/context replay; admitted same-E comparison succeeds, unmatched atom forwards unchanged to tail. This is not attachment subtraction. Queue generation is not complete drain. |
| Concrete residual feedback/projection | `candidate_context.rs:2744–2813` | `discharge_residuals` records the remaining context after a zero-word filter discharge, not a concrete-head/gamma residual recipe. The audited Effect consumer has no corresponding attachment-qualified concrete subtraction/gamma construction. |
| Copying/export/use | `candidate_effect.rs:806,832`; `candidate_extrusion.rs:265–318`; `candidate_scheme.rs:691,965,981,1054,1062,1097,1221` | Existing view/tail remapping and capture/freshening owners. They cannot prove preservation of negative attachment relations that have not been emitted. |

The abstract required invariant for a prospective local coupled cut is:
the actual formal occurrence supplies one retained set identity and tail;
its actual call route carries that same instance into both actual output
components; every applicable current/future lower encounters its check and
attachment-local reduction; every feedback/projection retains its own lineage,
shared parents and exact tail. Plain type-coordinate equality creates none of
these facts. The emitted Oracle pairing establishes only the first route's
constructor portion, conditional on its named successful operations.

## 6. Minimized missing bridge and prototype decision

There are two different open premises.

**Oracle H:** generalized observations must preserve the complete coupled
provider/call/check/contribution/output observation, or discharge/export each
discarded obligation. `generalize/core/stack_ids.rs:23–49` selects IDs by live
covariant occurrences. The prior H §5 additionally locates pruning and compact
projection. `compact/finalize.rs:586–603,837–839` resets principal variable
filters to All, while `instantiate.rs:741–787` both consistently renames retained
IDs AND adds `u32::MAX` root POPs for quantified IDs. Renaming alone proves
neither that transformation nor correctness of discarded filters. Complete
replay/omission and source coverage remain separate requirements. For nested
annotations, immediate predicate return at `constraints.rs:389` already prevents
an induction that assigns every descendant attachment to the outer direct-call
predicate. These transformations are available source, not missing files.

**Y3 local transfer:** given genuine negative formal attachment formation,
establish the complete coupled insertion/replay/residual/output observation
for the actual consumer, preserving independent same-family contributions and
constructor lineage. Its premise is currently absent: source rejection plus
empty executable words plus an Allowance-only atom consumer. Removing a guard
would not establish it. The existing P/Q bridge's 56 concrete positions are
composed-positive; endpoint polarity cannot relabel them as negative authority.

The **syntactic paired source/call/output invariant is derivable** for the
bounded direct-formal Oracle spine. It is useful guidance for a separately
authorized provisional private constructor/consumer experiment that retains
the known occurrence, binder and lineage evidence. It is **insufficient as a
correctness justification for a negative-formal mechanism or admission**:
attachment-local complete consumption is unproved, and the approved admission
gate explicitly excludes general enabling. This packet grants no code/prototype
lease. It neither waits for optional all-view metatheory nor silently treats
the required A/B local consumer invariant as optional research.

One recommended next action: assign the constructive lane the local Y3
coupled consumer obligation above, using this exact source-owned pairing and
distinct recipe lineages as construction inputs; resolve or refute its decisive
invariant before authorizing the dependent implementation slice. Keep Oracle's
global export observation bridge separate. Another checker supplied with
PUSH/POP rules would leave these premises untouched.

## 7. Evidence, resources and omissions

Independent `compiler_referee` review found no blocking or major issue and one
minor scope clarification: the direct local pairing lemma must exclude effect
wildcards anywhere in the callable annotation, because the actual predicate
guard is whole-annotation. The hypothesis above now states that guard exactly.
The recorded `() -> [E] ()` spine is unchanged. This repair narrows only the
local derivation's hypotheses and does not narrow H or the supported source
domain.

Checks: bounded source/document `cat`, `rg`, `sed`, `nl`; pinned Oracle
`git show` and `git grep`; sequential `git rev-parse <SHA>:<path>` blob census;
Y3 dependency byte equality against `git show <baseline>:<path>`; leased-note
whitespace/link inspection and final dependency check. No Git mutation,
build, test, runtime, probe, random seed, search range, mutation, timing sample,
model change or delegation. One foreground lightweight read pipeline/script
at a time; shell pipelines can contain several small utilities. Aggregate
CPU/RSS and wall-clock were not instrumented; the assigned wall budget is
30 minutes. No heavyweight process ran. Early combined output was truncated;
governing and decisive source sections were subsequently read in bounded chunks.

Oracle independence: these are original pinned source objects, independent of
Y3 code and current Oracle instrumentation. The local algebra and source
characterization share those Oracle implementation assumptions; their agreement
is not independent proof of approved semantics. No execution oracle was used.
Historical acceptance and output are not newly verified here.

Omissions: source-wide H, every compact/prune path, live replay omission
soundness, executable source-to-binary equivalence, provider compatibility,
aliases/returned callees, multiple/nested calls and pattern forms, parameterized
effects, full capture/generalization/extrusion/intrusion preservation, mixed
recursive admission, Catch/runtime elimination, soundness/principality and
production cutover. The original source domain is not narrowed by these limits.
Dirty theory drafts and question bundles were untouched and not used as authority.

## 8. Frozen dependency identity and commit packet

The tables appended below contain exact Git blob IDs. All named Y3 inputs
matched the baseline bytes at inspection. Oracle IDs resolve from the pinned
revision; Oracle worktree identity is irrelevant. No dependency hash changed.

- Exact changed/leased path: `notes/progress/2026-10-12-oracle-effect-source-transfer-audit.md`.
- Baseline: Y3 `0e621f549035537e4d3e799c78f79dd9385df350`; Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none; exact pinned blob identities below.
- Review: unreviewed producer audit, frozen at handoff; no independent certification or theorem promotion.
- Checks already run: static pinned owner tracing, source/dependency byte checks, note whitespace/link and lease inspection; no builds/tests/runtime.
- Proposed message: `research: audit pinned Oracle effect source transfer boundary`.
- Shared-record deltas left for primary/curator: link this checkpoint to the negative-formal lane; record emitted-pairing/local-consumer/export-observation distinctions; retain NEGATIVE-FORMAL-SOURCE-STEP, global H, complete Call and cutover OPEN. No task/index/theory record was edited.


Y3 dependency blobs:

| Path | Git blob |
| --- | --- |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `2a2517f94df2969ed4c865298cb8395998b07c65` |
| `notes/design/2026-10-10-concrete-effect-annotation-implementation.md` | `c8c64dee1b19c864e8d6ac558162d4c3989f8c06` |
| `notes/design/2026-10-10-contextual-attachment-admission-design.md` | `c99873544ca90aa817c77941514f7868a8023d65` |
| `notes/design/2026-10-10-contextual-residual-lineage-selection.md` | `93a510c65eed2538fb67997215b8f8dd32395834` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `00b9bf7191c0d96cd64b5758ac8e7df5671cef25` |
| `notes/theory/2026-10-11-oracle-effect-hygiene-source-bridge.md` | `249c6ef2809d5b7b2514367e1279a75d0e47b1e6` |
| `notes/theory/2026-10-11-oracle-global-effect-hygiene-proof.md` | `abc5540c3869704a26e76d08cae55eb6acf32b05` |
| `notes/theory/2026-10-11-negative-formal-effect-source-proof.md` | `2af172dedd6f57ff5caf3e1ef6dbbe7a1e54bcb3` |
| `crates/yu-hir/src/module/source_annotation.rs` | `c6a738cd219d7ac5054971dc80739b350a1807e4` |
| `crates/yu-hir/src/module/local_source.rs` | `cc0f08da32b8cf3884597c53dee8d74d474f3bed` |
| `crates/yu-solver/src/candidate_source.rs` | `632fb512ea8086ea8ed2065997ad619d582576ee` |
| `crates/yu-solver/src/candidate_effect.rs` | `8e902f3331aa576f84179892f2916b6e84dcdc6d` |
| `crates/yu-solver/src/candidate_context.rs` | `c38e880f2a2d3df1a97c33845004415baab154e8` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `8637ae9217b01ece8d536fc51f4ced220064015f` |
| `crates/yu-solver/src/candidate_scheme.rs` | `a774de6f69f5177014bec22c2db0bdf904d0a7b8` |
| `crates/yu-solver/src/shadow_apply.rs` | `b5f0401efa7752d889c437b734b40bfecabcbb89` |
| `crates/yu-solver/src/lib.rs` | `a436989febc4e9a3203af0552332821859857709` |

Oracle dependency blobs:

| Path | Git blob |
| --- | --- |
| `crates/infer/src/annotation/constraints.rs` | `d2cf0e18266233c1e3c2943448244ee2a3499529` |
| `crates/infer/src/lowering/mod.rs` | `3d379d9a2ace1afce956da335a2b4c17ea3c92ae` |
| `crates/infer/src/lowering/signature_effect.rs` | `7d976863a257925d916f01fd5817890857f8a5e4` |
| `crates/infer/src/lowering/expr/lambda.rs` | `724b103cda8b4e2c457aacf0a674372fb191e3d6` |
| `crates/infer/src/lowering/expr/tail.rs` | `8289bfdc6a17b2469ae168ac7939d34813fda474` |
| `crates/infer/src/lowering/expr/constraints.rs` | `bf76fa1a18b18e0ccce4b09c6652f22b31b89b11` |
| `crates/infer/src/constraints/machine/propagate.rs` | `d558e7b9c17d33e91c5bb39c4cd85ebbfa4a8b09` |
| `crates/infer/src/constraints/machine/bounds.rs` | `365ed25a8b3b7e468a7a4e57159125be53209708` |
| `crates/infer/src/constraints/mod.rs` | `14860e3664a7ac05f7493f1d51fe69a6f34216e5` |
| `crates/infer/src/constraints/directed_weight.rs` | `a5998519c74f89a8bd65b22defd8f0a1e4fd59d9` |
| `crates/infer/src/constraints/row_effect.rs` | `d33c8d34f14dd5acc3b995050f4e9f7fa07ade25` |
| `crates/infer/src/instantiate.rs` | `7a0039439955b399f2bf526dc39f1d1aeddd008d` |
| `crates/infer/src/generalize/core/stack_ids.rs` | `584131ed3816672ab96c1abc20a149568a0b1a4e` |
| `crates/infer/src/compact/finalize.rs` | `2b6c586aa180338e1ce6a1e66b2dede21e8dbedf` |
