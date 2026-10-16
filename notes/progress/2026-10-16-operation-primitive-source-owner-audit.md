# Source operation declarations and the original primitive boundary

Date: 2026-10-16
Status: frozen research source audit; unreviewed
Claim class: bounded constructor/consumer characterization and conditional source map
Baseline: `48ef843ef20fe8856bc51c59a4264c3e7a62e584`, `research/simple-sub-intrusion`
Exclusive lease: this note; source/contract audit only, no compiler changes

## Objective and governing premises

Trace a real resolved `SourceOperationDeclaration` through HIR, signature
construction, Call and Catch, and identify which inputs it supplies to the
original primitive telescope. This complements the constructive proof lane;
it does not reconstruct the already established IF placement theorem.

The governing contracts are source contracts
`notes/design/2026-10-05-source-contracts-and-common-allowance.md`
§§2.1–2.2,3.7; the selected source-interface definition
`notes/design/2026-10-08-call-source-interface-definition.md` §§2–3;
its construction proof `notes/theory/2026-10-08-call-source-interface-construction.md`
§§3.1–3.2; and typed core
`notes/design/2026-10-02-typed-computation-core-elaboration.md` §§3–4,9
("Entry is part of the interface, even with a pure body").
The original alternative discharge artifact is consumed at its current frozen
hash below. The top-level inference principles retain normal source behavior.

Accepted Option 2 permits whole contractual alternatives without source
execution. Its original grammar remains

```text
H_G(R) = least X:
  X(y) iff G(y) and (R(y) or Z(y) or exists x,z. X(x) and W(x,y,z)).
```

The complete final guard, original shared witnesses, scopes, output provider,
response/current-state and dependent future remain attached. This audit neither
selects W/Z nor equates this complete production relation with its source base R.

## Actual source owners

Paths in this table are repository relative; line numbers refer to the pinned
source contents whose hashes appear below.

| Owner | Actual construction or consumer |
| --- | --- |
| `crates/yu-hir/src/module/source_annotation.rs:34–100` | Family identity is module plus declaration `SourceNodeKey`; operation identity adds the member declaration key. The operation record retains spelling, visibility, name/signature positions, range and `SourceAnnotationType`. The type contains an optional effect row and Unit/Int/Bool/Str/variable/Function; rows contain concrete family IDs and symbolic names. |
| Same file `:138–310`; `crates/yu-hir/src/module.rs:1040–1053,1234–1245` | First collect all family headers, then parse every admitted bodyless member signature. Reject a member `BindingBody`, parameters or non-Function signature. Register each original member under `(family ID, spelling)` in `operation_namespace`, preserving multiplicity. This is the ordinary source resolution index. |
| `crates/yu-hir/src/module/local_source.rs:943–966,1088–1099,1130–1173` | Qualified expressions and operation patterns resolve through that same index. Missing, ambiguous or private members have explicit resolutions. Catch retains original operation-pattern source key, payload and continuation binders, arm scope/body and arm order. |
| `crates/yu-solver/src/candidate_source.rs:428–446,779–805,923–940` | Preflight requires an outer Function without an outer computation row and the supported annotation envelope. Catch additionally requires one payload and a monomorphic signature. Pure lookup emits bottom/empty effect constraints and an `Action::Operation` carrying the same declaration `Arc`, owner, occurrence, target and level. Catch passes the same declaration plus original scrutinee Value/effect and actual payload/continuation binder endpoints. |
| `crates/yu-solver/src/candidate_effect.rs:806–824,1472–1703` | Each lookup uses fresh signature-variable maps at level+1 and admits the positive Function at slot42. Recursive signature construction reverses argument polarity/variance. Only the outer Function's result-effect constructor receives the owning family. Missing operation rows otherwise produce bottom/empty. Explicit rows preserve all original members and the symbolic tail, prepending the outer family where applicable. |
| Same file `:153–180,748–793`; `crates/yu-solver/src/shadow_apply.rs:373–407` | Signature views retain operation declaration, original lookup occurrence, owner/signature position, members and tail. Diagnostics expose `OperationInterfaceMember`, preserving the member ordinal. This is interface provenance; it does not manufacture an operation execution or license from a matching family. |
| `crates/yu-solver/src/candidate_source.rs:1008–1052`; `crates/yu-solver/src/shadow_apply.rs:1534–1630`; `crates/yu-solver/src/lib.rs:12642–12671` | Apply retains the actual callee, whole argument, argument/evaluation effects, result and original checking occurrence. Admission constructs a negative Function demand and records its invocation row before constraint admission. Function propagation compares the four Argument/ArgumentEffect/ResultEffect/Result children with their original parent. These scalar consumers do not evaluate Prim or an arbitrary whole contractual alternative. |
| `crates/yu-solver/src/candidate_effect.rs:826–890` | Catch opens argument/result signatures in one shared environment. Slots60/61 pair the payload Value. Slots62/63 pair raw-k's Function, taking declaration result B as its response and original scrutinee Value as its result. Slots64/65 retain response-entry effects and provisional full-scrutinee effects in raw-k's return row. Slot65 is expressly not exact suffix construction. |

The separate approved source-owned registry gate
`notes/design/2026-10-10-source-owned-registry-design-gate.md` authorizes
design/review, with no concrete registry/API adoption. It cannot turn this
ordinary HIR name index into a selected registry of complete W/Z primitives.
The operation producer integration gate likewise expressly distinguishes
interface operands from execution contributions and complete Call suppliers.
At `candidate_effect.rs:779–784`, operation views specifically receive no
annotation `source_weight` or executable `closed_weight`; retained operation
identity is not an executable annotation filter.

## One direct family: `signal::exchange`

The retained source artifact
`tools/inference-playground/examples/catch-operation.yu` declares

```text
act signal:
    our exchange: int -> str
```

and calls that operation under a matching arm whose raw continuation receives
`"resumed"`. No execution of this example was performed in this audit.
Let D denote its actual declaration, with family ID from the `act` node and
member ID from the `exchange` binding node. No numeric source key is invented.
The actual signature constructor gives the ordinary positive interface

```text
Function(Int−, EmptyEffect−, eD+, Str+),
where eD has the original positive Support view [D.family].
```

Lookup is pure. The family is attached to the declared result computation;
it is not an effect of reading D. At Catch, payload Value is paired with Int
and the raw continuation response with Str. Its result remains the original
scrutinee Value, rather than the operation's native request carrier.

The runtime correspondence is independently inspectable at these owners:

| Runtime owner | Direct source-generated behavior |
| --- | --- |
| `tools/inference-playground/src/runtime/program.rs:431–432`; `runtime/machine.rs:533–534` | An operation expression becomes `Instruction::Operation` and inert `RuntimeValueKind::Operation` retaining its resolved declaration. |
| `runtime/machine.rs:740–792,645–649,1428–1443` | Calling D establishes its actual invocation. A Value argument is executed before payload construction; a computation argument is retained. Native code returns a computation carrier containing `ExecutableValue::Request { declaration, payload, source }`. `ReceiverReturn` precedes the distinct `OperationResultConsumer`, which executes that carrier. |
| Same file `:1572–1595,1338–1399` | Executing the carrier creates the original request event, observations and an initially empty local suffix. Propagation accumulates actual crossed frames/receiver/handler boundaries. The initializer escape boundary remains active. |
| Same file `:1222–1338,1002–1072`; `runtime/continuation.rs:15–45` | Ordered handler selection checks actual operation identity and existing visibility/receiving evidence plus payload compatibility. Selected capture retains this declaration, event lineage and actual raw suffix. The selected handler is popped before its arm. No source arm is inferred merely from matching support. |
| Same file `:560–597,1076–1161` | Response compatibility is checked against D's result, then raw-template entry supplies it to the original Hole, reinstalls actual saved frames and borrows live owners or creates fresh invocation owners as specified. Entry uses the current machine state; the template stores no old store snapshot. |

Thus the source segment has the typed-core §3 shape

```text
ExecuteCallable(D,t)
 = Invoke(entry_D; Return(MakeRequestThunk(D,payload)), t)
     >>= Execute_decl_result
```

The native return is a request carrier, not the declared Str response. Its
explicit declaration-derived consumer is what exposes the request. At that
request, the local response continuation returns the supplied Str; ordinary
Bind appends the actual remaining source context, so a suspended argument also
retains unfinished entry, native return, result consumer and caller suffix in
their actual order. This is the structural source map, conditional on the
existing typed-core derivation/owner/receiving hypotheses. It is not a whole
typed-source adequacy theorem for the playground or inference engine.

`NativeReturn` is a proposed Q-clause name in the source-suffix construction
note §3.1. There is no solver variant with that name in the inspected crates.
Its operational witness here is the native return sequence above. Keeping
that distinction prevents a proposed source record from being counted as an
already implemented complete relation consumer.

## Exact primitive-telescope handoff and obstruction

For the source base, the enriched input `(D, actual source derivation, actual
Call/Catch context)` supplies declaration identity, argument/response types,
source owner/occurrence, receiver entry, request payload/event, current state,
actual raw continuation and its source-dependent future context. The context
and execution rules supply the latter fields; D alone does not contain them.
This witnesses the structural source alternative under its actual original
binders, and can be inserted/referenced by IF at its real source slot.

The complete generic input has a different explicit premise:

```text
P_alpha |- w : Prim_alpha(h,y;xi),
q = Prim(alpha,m),   IF(q) = T_alpha[m].
```

Construction §3.1 assumes the independently interpreted whole primitive
relation, full dependent telescope, original license/hard constraints and
lawful provider/world/admission/future actions. IF-Insert and IF-Use preserve
and place them; they do not define those relations. SourceOperationDeclaration
has no field selecting Z, W, their complete guards, or their legal transformed
future-to-upper action. The inspected producer/Call/Catch path supplies no
replacement field. Native Support/Allowance operands and four Function fields
do not establish the active complete-root interpretation of source contracts
§2.2, or the whole alternative's membership/admission grammar.

Consequently the source construction above cannot discharge the unanchored
Z case. No source execution for it is assumed. At its original leaf the same
obligation remains: original admission, original guard, Prim evidence and the
actual shallow image must imply membership in the exact original upper U at
its lawful output-dependent indices. NativeReturn/request suffix construction
does not give that primitive image/upper action. W also retains its original
shared predecessor and rewrite witness; this audit selects no replacement.

This is an absent selected contract at a precise owner boundary, not an
impossibility theorem, source-invalidity result or source counterexample.
There is no additional executable experiment or toy model assuming the missing
transition rules. Oracle independence therefore is not claimed: runtime and
inference share the same HIR declaration and this is a source audit, not an
independent semantic oracle. The independently specified typed-core equations
support the conditional structural map only at their existing hypotheses.

One recommended next action: obtain/adopt the actual complete primitive
declaration and finite membership/image-checking contract at the original
Prim owner, or explicitly establish that no concrete instance has yet been
selected. Preserve the generic parent's original scope and OPEN status.

## Checks, resources and frozen dependencies

Commands: bounded `rg -n`, `sed -n`, `cat`, and `sha256sum` on the named owners
and governing sections; final note existence/fence/whitespace and hash checks.
An initial combined task-record read exceeded output bounds; only relevant
current checkpoint and source-gate material was used. A mistaken playground
path and mistaken integration-gate directory were corrected before use.
No exhaustive repository absence claim follows from those searches.

Budget: at most 18 minutes; lightweight sequential static commands only.
Zero builds, tests, executable probes, network calls, benchmark processes or
samples, Git commands and children. CPU/RSS and exact elapsed time unmeasured.
Runtime model/effort metadata unknown. No independent review performed here.
No production/lifecycle, all-source, opaque-primitive validity, generic image
discharge, principality, adoption or cutover gate closes.

Current SHA-256 pins follow. Baseline identity is supplied by the primary;
no Git command independently revalidated it. The direct hashes already pinned
by the original-alternative artifact match that artifact's dependency list.
Other source hashes record this audit snapshot; no dependency was edited.

```text
b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f  crates/yu-hir/src/module/source_annotation.rs
ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5  crates/yu-hir/src/module/local_source.rs
2e0c579a525efd5ac4c7ce0f06189c568ed46c7382d4576698a0b8d846c2228e  crates/yu-hir/src/module.rs
2dffd7fd6542eed9fd3346e0672e76197c248be9c84334f341c4d612234b7ee9  crates/yu-hir/src/shadow.rs
efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38  crates/yu-solver/src/candidate_source.rs
44ee33d077c61c9dea6359299ca49218afc6ca1b5b6807690838309b25c731c9  crates/yu-solver/src/candidate_effect.rs
cbad9cf51a05343eb7a29ab77aac520891467a8aa4edc3201ea3d91f978984a1  crates/yu-solver/src/candidate_call.rs
357b274d0de509931bda3015a99b1a1cf2ac86d75a45d230d62ab456c56740ba  crates/yu-solver/src/shadow_apply.rs
2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f  crates/yu-solver/src/lib.rs
b9798ac4c5d93e761582d712114615defa913f858d70e91f170471c8b8912748  tools/inference-playground/src/runtime/program.rs
04024174d88223e252e1d093eaee96c17d9f43d4d32bea5c41631017c9da208c  tools/inference-playground/src/runtime/machine.rs
194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3  tools/inference-playground/src/runtime/continuation.rs
af360172c74483e4ce009c8ad853d0398bfff3e9b5f0f3f481641f1731c86ed7  tools/inference-playground/examples/catch-operation.yu
17fda1a477d451652fb9e8088cd7fb92ff763195cbdcc8ce7467763c0aaaa24f  notes/theory/2026-10-16-image-demand-original-alternative-discharge.md
11a058d90ca46c9cb58fdff38d532efe3401f0a0131e8ba8567e91af89d689b4  notes/theory/2026-10-16-call-suffix-image-demand-construction.md
1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186  notes/design/2026-10-05-source-contracts-and-common-allowance.md
20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c  notes/design/2026-10-08-call-source-interface-definition.md
278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98  notes/theory/2026-10-08-call-source-interface-construction.md
0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e  notes/design/2026-10-02-typed-computation-core-elaboration.md
22054cebe0f5554cef713b32ab9a2f81b11efdd2b165dcab2ac90f7c2be0252b  notes/design/2026-10-10-source-owned-registry-design-gate.md
```

Commit packet:

- Exact lease/change: `notes/progress/2026-10-16-operation-primitive-source-owner-audit.md`.
- Baseline: `48ef843ef20fe8856bc51c59a4264c3e7a62e584`; no dependency edits.
- Review: frozen unreviewed research characterization; no self-certification.
- Checks: static owner/contract reads and note integrity/hash checks only.
- Proposed commit: `research: trace operation source owners to primitive contract boundary`.
- Shared deltas intentionally left for primary/curator: retain the distinction
  between source-operation signature/runtime construction, IF placement and
  complete opaque W/Z primitive semantics; preserve every parent gate OPEN.
