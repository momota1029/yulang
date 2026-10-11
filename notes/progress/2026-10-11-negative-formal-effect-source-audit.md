# Negative formal concrete effect row: Oracle-qualified source audit

Date: 2026-10-11
Status: independently reviewed bounded Oracle/source observation; current Yulang3 bridge OPEN
Claim class: one executed Oracle characterization plus static constructor/consumer correspondence; no general theorem or implementation authority
Yulang3 baseline supplied by primary: `e899d1acd0f40b3b29b9f651f6cb658be316fbc1`
Oracle revision supplied by primary: `a58eefc31e22141574b6f20c6a5748151c6d79f1`, checkout `/tmp/yulang2-oracle-read`
Exclusive lease: this note only

## Objective, authority and exact premises

Audit the smallest non-root Function formal row needed to exhibit the selected
composed-negative subtraction gap, using one existing Oracle invocation and
static source owners. This lane does not duplicate native value-conflict work.
Authority is [annotation hygiene integration](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–5 and [top-level inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5. The selected meaning is fixed: a concrete negative `[E]` permits
function-local subtraction of exactly E at the scoped position; a positive
`[E]` allows E; variables are not concrete annotation atoms. Neither the
retracted callback scheme nor the expansive `my ans: [E] int` witness is used.

The [conditional contravariant derivation](2026-10-10-contravariant-effect-conditional-proof.md)
requires supplied source attachments and actual consumers. This audit supplies
one authentic Oracle source constructor/call-consumer path; it does not supply
that missing Yulang3 transition. The [contextual admission design](../design/2026-10-10-contextual-attachment-admission-design.md)
§§5–6 explicitly keeps concrete-formal enabling behind the later admission
gate. Its blanket rollback requirements are subject to the top-level principles.

Hypotheses for static source claims: the inspected files retain their snapshot
hashes below; the actual annotation tree has one Function formal whose result
has the single resolved nullary effect `tick`; the body directly invokes that
formal. Revision identity is supplied, not revalidated with Git. Executable
identity is the binary hash below; build-to-source correspondence was not
independently reconstructed in this lease.

## Single discriminating source and complete Oracle result

Exact source supplied on stdin, including its final newline:

```yulang
pub act tick:
    pub ping: () -> ()
my f(cb:(() -> [tick] ())) = cb ()
```

Source SHA-256: `d003d56a881c08d0767dfe6f093b2b6b9d3d1ccdba9d112b2863f6e1bb469c05`.
One formal, one Function node, one nullary concrete row and one application.
There is no symbolic tail, nested callback, local capture, recursion, handler,
operation invocation or provider body. This is structurally minimal within the
non-root Function-result formal-row class: deleting the row removes the grant;
deleting the Function removes its result-effect slot; deleting the application
removes the call-local consumer. No claim of globally shortest syntax is made;
no deletion variants were executed.

Command inside a Python `subprocess.run` wrapper:

```sh
/tmp/yulang2-oracle-read/target/debug/yulang --no-prelude --no-cache dump /dev/stdin --poly
```

The wrapper supplied the exact source above with `text=True`, captured stdout
and stderr, and enforced `timeout=30`. Result: exit 0; stderr empty; stdout
196 characters, completely reproduced here:

```text
roots d0:tick d2:f
pub d0:tick mod {
}
my d2:f: (() -> [tick] ()) -> () = e3:(fn p0:d3:cb -> e2:(e0:r0:cb->d3:cb e1:()))
detached {
  pub d1:"tick.ping": () -> [tick] () = <missing>
  d3:cb arg
}
```

Observed wall time 0.018227 s; child user CPU 0.013127 s, system CPU
0.004375 s; child maximum RSS 35,840 KiB. Binary SHA-256:
`0afe6aa1d0d4019dd5778fec012a2ee2aad57ea6a58ac42e347c0f6199cf1e58`.
The declaration-only `tick.ping` body is explicitly `<missing>`; this run is an
inference dump, not execution of an effect operation.

The displayed scheme retains `[tick]` in the callback's output and omits an
output-effect row after **f's outer arrow**. Thus it directly records absence
of `tick` in f's displayed invocation-result effect. It does not directly prove
absence from every raw solver variable, the effect of evaluating the declaration
of f, runtime request removal, or soundness. The ordinary formatter routes
Function result effects through `pos_row_inline`/`neg_row_inline`
(`poly/src/dump/type_format/formatter.rs:480–519,900–926`), and `fun_text`
(`type_format.rs:591–598`) omits absent rows. No raw constraint dump or typed
intermediate IDs were obtained. The scheme is an observed result for this exact
source; it is not a new expected-output contract or a theorem about all callbacks.

## Actual Oracle constructor and call-local POP consumer

The owning formal path is **AnnConstraintLowerer**, rather than merely the
separate SignatureLowerer illustration cited in the earlier policy record.
All paths below are relative to the Oracle checkout.

1. `infer/src/lowering/expr/lambda.rs::connect_lambda_pattern_annotation`
   (1244–1283) builds the actual formal annotation and calls
   `connect_parameter_computation_detailed`. The latter
   (`annotation/constraints.rs:251–280`) sets `parameter_function_boundary`
   while constructing it. `connect_value_detailed` (124–137) emits both
   annotation-positive-to-formal and formal-to-annotation-negative constraints.
2. `lower_value_bounds`, Function case (363–390), reverses argument bounds,
   preserves return bounds, and calls `lower_ret_effect_bounds` (424–470).
   For the closed `[tick]`, `function_boundary_effect_stack_inner` (602–620)
   retains a boundary variable q. `effect_row_stack` (657–690) allocates one
   fresh SubtractId i with `PUSH_i(Set(tick))`; `register_stack_facts`
   (590–599) registers this declared fact. `effect_atom_con` (741–748) omits
   variables from concrete sets. `subtractability_from_atoms` (1004–1009)
   makes the singleton resolved constructor/operand set, not a spelling grant.
3. The paired result effect is positive `Stack(q, PUSH_i(Set(tick)))`, negative
   `Stack(q, FILTER(Set(tick)))`, with returned predicate
   `POP_i.with_filter(Set(tick))` (`predicate_weights`, 921–924). The returned
   value positive also retains matching `NonSubtract` weights (363–389,
   848–851). No concrete body `tick` event is fabricated by these constructors.
4. `lambda_annotation_predicate_constraints` (1581–1596) forwards these
   weights into `call_predicate`; `mark_lambda_param_call_predicate`
   (919–936) stores them on cb's actual local binding; the defined parameter
   path marks its frame (735,938–943). Crucially,
   `lambda_parameter_output_predicate_constraints` (1571–1578) returns an
   **empty immediate output predicate for Function annotations**. The row is
   not subtracted unconditionally at outer binding formation.
5. The body's authentic application enters
   `infer/src/lowering/expr/tail.rs::make_source_app` (629 onward), then
   `make_app_with_origins` (539–565). `local_callee_call_projection`
   (690–705) retrieves cb's exact `call_predicate_subtracts`;
   `extend_current_latent_predicate` (719–725) adds them to the current
   Function frame. The application emits its ordinary callee Function demand
   and forwards the call-result effect (563–624).
6. `lambda_predicate_subtracts` (`tail.rs:1058–1072`) merges/deduplicates that
   frame's latent weights. The actual defined-lambda skeleton consumer
   (`lambda.rs:1176–1241`, especially 1232–1237) wraps both the current output
   effect and value with those exact weights before linking the output slots.
   `wrap_pos_with_subtracts` (`expr/constraints.rs:137–145`) creates
   `Pos::NonSubtract` wrappers. The ordinary lambda helper also preserves this
   operation at `tail.rs:1090–1109`.
7. `constraints/machine/propagate.rs::step_subtype` (11–56) normalizes positive
   Stack and NonSubtract wrappers into retained left weights; Function result
   propagation preserves direction (210–263). `ConstraintWeights::compose_for_replay`
   (`constraints/mod.rs:3598–3607`) composes lower-to-upper left operations.
   `LeftStackWeight::push_entry` (`directed_weight.rs:145–170`) and
   `compose_same_id_counts` (399–405) cancel exactly a matching i's
   PUSH then POP: `(m,n)=(0,1)` composed with `(p,q)=(1,0)` gives `(0,0)`.
   A different SubtractId is a separate entry. This is the actual attachment
   cancellation owner; it is not nominal set deletion.
8. Negative filters are real consumers: `propagate.rs:38–56` checks before
   normalization; `bounds.rs:3213–3255` records the filter and checks current
   lowers; `3285–3301` checks future insertions; `3303–3360` preserves recursive
   row/stack/union/variable checks. This source inspection covers their owner
   paths, not an executed foreign-effect or late-lower test in this packet.

The source establishes constructor/call/output wiring and named cancellation
operations. The one dump establishes admission and the displayed outcome.
The run did not instrument the exact intermediate q/i values or prove that
this entire static path exhausts every path contributing to the printed root.

## Yulang3 lowering and the exact missing seam

Equivalent Yulang3 spellings use `act tick`, `our ping`, and the parser-required
space in `my f (cb:(() -> [tick] ())) = cb ()`. No Yulang3 run occurred.

- `yu-hir/src/module/local_source.rs:289–300` retains the original formal
  annotation on `LocalSourceParameter`. `source_annotation.rs:335–362`
  retains owner/annotation position; `400–480` forms Function argument/result
  trees; `503–558` retains exact row position and resolves nullary `tick` through
  the effect namespace. This is a supported structural lowering route by source
  inspection; executable admission of this exact Yulang3 text is not claimed.
- `yu-solver/src/shadow_apply.rs::CandidateInference::solve:92` calls
  `candidate_source::preflight` before inference. At `candidate_source.rs:98`
  a formal begins at `positive=false`; `preflight_formal:117–120` reverses
  arguments and preserves results. The callback result stays false, and the
  row has one concrete member and zero variables, so the predicate
  `row.concrete.is_empty() && row.variables.len()==1` fails. The public private
  entry returns `CandidateError::Unsupported` before emitting this annotation
  action. This conclusion follows statically; it is not a new test result.
- On admitted formals, planning schedules `Action::FormalAnnotation`
  (`candidate_source.rs:282`) before visiting the body; execution routes it to
  `candidate_formal_annotation` (`663`). That owner starts paired construction
  at `Polarity::Negative` (`candidate_effect.rs:1090`).
- The independent paired guard at `candidate_effect.rs:1035` rejects the same
  negative concrete row; Function recursion (1045–1052) retains result variance.
  `candidate_formal_effect_port:1054–1070` has only omitted, singleton-symbolic,
  or positive concrete/empty constructors. General signature construction also
  explicitly rejects negative concrete at `1507–1509`. Bypassing preflight
  alone therefore cannot create the transition.
- `candidate_signature_view:733–782` and `candidate_context::source_weight`
  (`2174–2195`) already retain owner, exact row position, resolved members,
  composed polarity, lexical scope and member ordinals. Their source weights
  have empty left/right words; `materialize_unit_push` (`2200` onward) is a
  detached adapter with no live consumer. Existing Support/Allowance formation
  and zero-word filters are not this Oracle call-local PUSH/POP pair.

The smallest construction gap is at the paired **formal result-effect owner**,
with its matching source-call/output consumer: construct an attachment for this
one row occurrence and connect its actual callback use to the scoped retained
subtraction. Do not manufacture permission from endpoint polarity or support
membership. HIR already knows the owning facts; retaining them avoids inverse
reconstruction. The selected implementation carrier exists as approved internal
work, but §§5–6 forbid enabling this row now by deleting rejection guards.
This audit grants no compiler edits or broader admission authority.

## Coverage, limits and next action

Oracle is independent of Yulang3's candidate transition model. Both readings
share the supplied revision identities and accepted language policy. There was
one deterministic hand-selected input, no random seed/range, enumeration,
mutation test, variant run, build, test, formatting, child delegation or Git
command. Static searches/read captures included truncation for broad task
records; the specific decisive owner excerpts were read directly. Overall audit
CPU/RSS was not measured; the one Oracle child metrics are reported above.
The primary stopped further investigation after obtaining this discriminator.

Open scope: source-to-binary build provenance, instrumented intermediate trace,
Yulang3 execution, symbolic/foreign/current-future lowers, same-family independent
contributions, returned-function use, recursion/mixed admission, freshening,
extrusion/intrusion, complete effect hygiene, soundness/principality and F5 cutover.
This is neither a general counterexample nor a proof that a selected annotation
subtraction theorem already applies to Yulang3.

Recommended next action: give the prover this exact source-qualified
constructor/call/output chain as the smallest negative-formal premise in the
normal-inference mathematical lane; keep implementation/admission gates open
until the corresponding candidate construction and consumer invariant are proved.

## Dependency snapshot and commit packet

Snapshot hashes were recorded at note formation and rechecked unchanged.
No dependency is reported changed by this leaf; comparison to a different
primary baseline or concurrent revision remains the primary's integration duty.

| Dependency (Oracle paths prefixed `Oracle:`) | SHA-256 |
| --- | --- |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `notes/design/2026-10-10-contextual-attachment-admission-design.md` | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
| `notes/progress/2026-10-10-contravariant-effect-conditional-proof.md` | `faeaffecbd2aa6a50e4d82bc8924870148f784448d29aa893e9f5ddb89cb2ef9` |
| `notes/theory/2026-10-11-oracle-effect-hygiene-source-bridge.md` | `51be142a399a4c1b65281292141c0d12b65b3996f960f5d4962423aec024ebb8` |
| `crates/yu-hir/src/module/local_source.rs` | `906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed` |
| `crates/yu-hir/src/module/source_annotation.rs` | `a348a47530e57c2b3475a4c0d9f020e24ba04ea58a06292847892640567e61cb` |
| `crates/yu-solver/src/shadow_apply.rs` | `6bea8808153b8b71a57e4a8583284e49284ec9aa35118a61f44a3a387a8a32f6` |
| `crates/yu-solver/src/candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `crates/yu-solver/src/candidate_effect.rs` | `ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df` |
| `crates/yu-solver/src/candidate_context.rs` | `4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987` |
| `Oracle:crates/infer/src/annotation/constraints.rs` | `3c0482d4549a2bfc7e651a6b2cc15fa4e70488fe8f68fcbfca34c1bfb72920db` |
| `Oracle:crates/infer/src/lowering/expr/lambda.rs` | `2e0206bdcfdfbe98d13c12eec7ba8f7964383bc08c92947352ad370754024db9` |
| `Oracle:crates/infer/src/lowering/expr/tail.rs` | `ac406b309fbb0ba558a18e37aba63a8e7ffeabbc377a111566b1f97d786f93b8` |
| `Oracle:crates/infer/src/lowering/expr/constraints.rs` | `2800250aa516c519d91aa11b0d46455f0a86f14a009be3588c7e039d2c5cbe20` |
| `Oracle:crates/infer/src/constraints/machine/propagate.rs` | `8695fa5d7dfac805cd7d66e9e0760c8c298002b952b0cd8a43dcd1f8eb6f7086` |
| `Oracle:crates/infer/src/constraints/machine/bounds.rs` | `c300c8c0c495da46822e1e1df38b833a6bffe5f3707642ae2cd26910b0608df7` |
| `Oracle:crates/infer/src/constraints/mod.rs` | `ad3cf5fd60462cb1a08ef1a5d6fc57c4fd640148597bc3b331d09729616d8392` |
| `Oracle:crates/infer/src/constraints/directed_weight.rs` | `de71ae7ed5a5aed22f3e5d35ca0ebcd52872ff965fcc22523a662cffdd6f28db` |
| `Oracle:crates/poly/src/dump/type_format.rs` | `49800841ea8059b007076b8018076baa91ae275c76f3f07eb24a57341fe35bd7` |
| `Oracle:crates/poly/src/dump/type_format/formatter.rs` | `10ef65e06243dff901d83e37bde22b99065c05dc92a31872fb8179397c3c2265` |

Commit packet:

- Exact leased/change path: `notes/progress/2026-10-11-negative-formal-effect-source-audit.md` only; writes stop at handoff.
- Baseline: `e899d1acd0f40b3b29b9f651f6cb658be316fbc1`; Oracle revision `a58eefc31e22141574b6f20c6a5748151c6d79f1` supplied by primary.
- Dependency changes: none made; snapshot above rechecked stable; no Git baseline comparison performed.
- Claim/review: executed singleton characterization and static source audit; unreviewed research checkpoint, no independent certification or gate closure.
- Checks already run: bounded source reads/searches; one existing Oracle dump with 30 s timeout; dependency SHA-256 snapshot/recheck; note whitespace and local-link check. No build/test.
- Proposed checkpoint message: `research: audit Oracle negative formal effect subtraction path`.
- Shared deltas left for primary/curator: link exact Oracle witness and call-local consumer chain to NEGATIVE-FORMAL-SOURCE-STEP; retain its OPEN A/B status and concrete-formal admission gate; prioritize this premise in normal-inference mathematics. No shared task/index/design/theory record edited.
