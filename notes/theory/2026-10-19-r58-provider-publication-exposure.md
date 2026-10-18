# R58: exact pre-annotation obstruction for the pinned top-level provider

Status: candidate static source/native obstruction; independent review pending.
Sole author `/root/r53_ordinary_mixed_capture_proof`, session
`current-conversation-2026-10-19-r58`; no descendants.
Contract `original-name-prepublication-exposure-20261019-r58`, revision 1,
SHA-256 `87491930517debeea7c96baf14a74fe6cdd6a94dd8619554512ec672a6f71223`.
Baseline `13e1e65da38e64992bc53f9e7f2cd2e12696ee3d`.
Exclusive outputs: this note and `tasks/agent-loop/inbox/20261019-r58-proof.md`.

## Result and parent application

For the exact intended resolved source carrier below, the CURRENT ordinary
candidate solver rejects the whole-function argument annotation in
`candidate_source::preflight`, before constraint collection, inference-session
creation or `Action::Annotation` execution. Its result is Unsupported. This is
a static branch derivation, not an invocation or observed solver result.
No compatible successful ordinary constructor prefix reaching this Annotation,
physical original-provider exposure, or first native capture is established.

This is a constructor-specific implementation obstruction. It is NOT a
language/source-domain exclusion, annotation compatibility counterexample,
parent counterexample or proof that the annotation is semantically invalid.
The direct-Name/current-formal constructor conditions match the original
fragment; whole-source typing and compatibility remain separate. The parent
forwarding-preservation §§1,6–7 and Simple-sub A/B remain OPEN 0→0, with their
original quantifiers, source domain and independent continuation obligations.
R50 remains NOT ADOPTED. R55's definition-annotation completeness seam remains
unresolved; this candidate cannot currently supply its exposure witness.

## Exact source and three distinct annotation positions

```text
act io:
    our tick: int -> int

my forward (t:[io] int): [io] int -> [io] int = t
my outer (q:[io] int) = forward q
```

The source fixes one concrete io declaration identity and a monomorphic
Int→Int operation signature; it invokes no operation. HIR's local-source mode
forms effect declarations before root plans (`yu-hir/src/module.rs:1176–1184`);
all family headers exist before signature rows are resolved
(`source_annotation.rs:220–228`). `parse_row` retains the row's own SourceNodeKey
and resolves each concrete spelling to its unique declaration identity
(`source_annotation.rs:531–585`). Three `[io]` rows do not have the same
source position merely because they refer to that same family:

| Position | Stored source meaning |
| --- | --- |
| parameter t annotation | its own outer Computation row, input Int |
| whole-function left annotation | Function.argument.effects={io}, input Int |
| whole-function right annotation | Function.result.effects={io}, result Int |

The whole-function type itself has `effects=None`. For an arrow,
`parse_type_source` moves its leading row into the argument type and returns
a Function whose root has no row; it recursively parses the result row
(`source_annotation.rs:411–425,452–500`). It is not a root evaluation annotation
and not the parameter's annotation. `source_annotation::form` reads the
binding-header annotation (`:317–340`); LocalSource stores it separately from
the annotated Lambda parameter (`local_source.rs:598–625,714–721`).

Forward's body is exactly its original formal Name t, and the whole argument
to forward is outer's current Computation-formal Name q. This matches the
parent's displayed constructor conditions without a higher-order argument.
It does not supply a complete monomorphic typing derivation or compatibility
proof for the whole annotation. Original formal `[io]` permission leaves
incoming E open; the authoritative annotation policy §§1,1.1–1.2 requires
permission, actual inflow and residual/allowance to remain distinct. This
report imposes no closed cap or declared-io inflow on that original formal.

## First exact ordinary-route obstruction

Ordinary `CandidateInference::solve` calls `solve_mode(hir,false,false)`
(`shadow_apply.rs:270–281`). In `solve_mode`, every available LocalSource
carrier is passed to `candidate_source::preflight` with `?`, before the
collect/session/run calls (`shadow_apply.rs:385–435`). Conditional on the
intended HIR/source carrier forming, the relevant predicate reduces as follows:

```text
source.annotation() = Function(argument=[io]Int, result=[io]Int)
preflight_annotation(Function, true)
  -> preflight_value(Function, true)
  -> preflight_annotation(argument, false)
  -> false: !positive && !argument.effects.concrete.is_empty().
```

`preflight_annotation` rejects a concrete row at negative composed polarity;
`preflight_value` reverses polarity for the Function argument
(`candidate_source.rs:603–615`). The root annotation check at `:460–463`
therefore returns `CandidateError::Unsupported`. The result branch need not
execute because the conjunction short-circuits. This does not depend on
unknown solver state, row equality, later replay or an assumed transition.

The explicit parameter annotation follows a DIFFERENT check: Lambda formals
check the row-variable count and `preflight_formal_value` of the VALUE shape
(`candidate_source.rs:477–480`). For t:[io]Int, the value is Int and there is
no symbolic tail. That formal Computation position is not the failing
whole-function argument position. Removing the distinction would incorrectly
turn a supported formal permission into a global rejection or a closed cap.

No parser, preflight, collector or solver was executed. The deduction is from
the exact intended source type and these frozen owner predicates. It makes
no independent claim that parsing/HIR formation or complete source typing was
observed. Even with that formation premise supplied, the ordinary native
annotation path is blocked at this precise guard.

## Scheduling and physical/capture boundary

The source producer would append definition `Action::Annotation` only after
its body actions (`candidate_source.rs:1450–1467`), preserving the whole
annotation, original body endpoint, evaluation-effect component and definition
target. In source mode, execution does not blanket-admit all collected facts
(`lib.rs:10424–10439`). Its source-action interpreter calls
`candidate_annotation` at `candidate_source.rs:1693`.

Those producer/consumer facts establish code ownership and intended order;
they do not establish that an action was emitted or executed for this ordinary
attempt. Its earlier preflight failure prevents collection itself. There is
no native original Function, e_t/e_n/e_R allocation, level/non_generic record,
physical BoundKey, typed worklist, retained signed parent, source-event set,
qualified settlement or annotation admission to report for this route. These
are UNREACHED, not observed empty structures or preserved native rows.
The HIR formal and source positions must not be relabeled as those native rows.

The next native owner that WOULD process an Annotation is
`candidate_annotation_pair` (`candidate_effect.rs:1605–1704`): construct a
negative checking signature and positive exposed signature, then admit the
original endpoint<=checking signature at slot40, check any root evaluation
row at42, and admit exposed signature<=definition target at41. Signature
construction precedes either original value-link admission. In the checking
Function constructor, argument variance is reversed; its concrete argument
row hits the matching refusal in `candidate_signature_effect`
(`candidate_effect.rs:1820–1853,1933–1935`). This is a corroborating consumer
boundary, not authorization to bypass preflight or an executed alternative.
No slot40/41 physical writes or original-row eligibility change follows.

Likewise the first top-level graph capture would occur after executing the
dependency component's source schedule, at boundary0
(`candidate_scheme.rs:1397–1424`). A later module Name would recapture the
live published root and instantiate it (`:1473–1492,1910–1960`). Here both
owners are unreachable after the preflight refusal. No partial FreshUse map
exists on this native route, and an image of e_n cannot be invented from a
source identifier or an unexecuted schema. No statement about actual exposure
or eligibility can be inferred from planned level1 body positions.

## Exact remaining premise, falsifier and handoff

Mutual TODO R58-DEFINITION-NEGATIVE-ROW-1, owner Luna for disposition at
`candidate_source::preflight_annotation` and
`candidate_effect::candidate_signature_effect`: establish an approved native
constructor/consumer correspondence for this exact whole-function negative
concrete annotation, retaining separate formal/argument/result source positions
and open incoming E, before attempting the requested prepublication trace.
The exact falsifier of this obstruction is an EXISTING ordinary route for
the unchanged source whose real source type is accepted by the guard and whose
annotation reaches physical original-row admission/capture without bypassing
validation. Changing the source or invoking an assumed transition is not that
evidence. No different candidate was constructed or probed here.

If code evidence is needed, the minimal provisional implementation TODO is
the owner-local negative-row admission/construction seam and its first real
slot40 comparison; its required evidence is the same unchanged source and
that exact falsifier. This report authorizes no guard removal, code edit,
instrumentation, execution, new dependency or semantic choice. A successful
constructor would still need actual compatibility, signed physical writes,
levels/nongeneric changes and the first authentic capture before it could
supply a parent-premise instance. No failure branch counts as that exposure.

Reused: original parent/domain and selected annotation meaning; R55's exact
module-Annotation completeness seam; R57 only as a reviewed bounded Local
result with no authority over this definition-level action. Rejected: equal
io spelling as endpoint identity; formal permission as closed cap; emitted
action as executed admission; failure as exposure; consumer/schema inspection
as complete solve evidence; R57 as a top-level publication theorem; a source
implementation refusal as a language restriction or parent counterexample.

Checks/resources: static source/rule reads and SHA-256 validation only. Contract
and all22 pins matched before work/writes and at freeze. Requested Sol/high;
observed model/effort UNKNOWN/UNKNOWN. Current-session active-work receipt
was returned after pin validation. Sol600 seconds charged, no carryover or
expansion; observed duration/CPU/RSS UNKNOWN. No parser/preflight/solver/test/
build/runtime/probe/instrumentation, code/semantic/expected-output changes,
measurements, Git, external contact, scratch or descendants. Only the two
exact leased new paths were written. Stop condition reached: first exact
ordinary native admission obstruction. STOPPED / WRITES_STOPPED /
NO_DESCENDANTS upon final hash submission. Fresh review/adjudication and any
further grant belong to Luna; producer cannot certify this result.

Frozen direct dependency manifest follows.

```text
d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79  notes/theory/2026-10-15-computation-forwarding-preservation.md
a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18  notes/design/2026-10-10-annotation-effect-hygiene-integration.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
7766aff08cedde1ebc796b8927cd1d44f459df72a632e0c0d35d4bfcd28d335e  notes/theory/2026-10-15-computation-formal-permission-construction.md
38d42183fdc4f2c0136112d8b305816241d8f449367b473e4de3a5135dc49895  notes/design/2026-10-10-local-self-recursive-binding.md
db5e8115e3f853e7831ffaf525e4c794bdca9892a18d7fb153f395451f94a40b  notes/theory/2026-10-19-r55-original-name-core.md
4c292a24c7fba19c40587fcc2cb9374fdbff3dd7059533548e4e1be1420546d1  tasks/agent-loop/sprints/original-name-core-20261019-r55.md
9603acbd00419111821aa0e808258d5b744f5afc0b2d8601be2cc7ffd8f883ff  notes/theory/2026-10-19-r57-original-name-two-capture.md
b8fb35aa130304ab459b1c8ead188c5ebd6c86bb177420842f279a1d17f4c5a9  tasks/agent-loop/sprints/original-name-two-capture-20261019-r57.md
b61c52cc4afa02b98828df76cc8182d15a60cb5d240dde4a73085f50ae08e0ce  notes/progress/2026-10-19-r57-original-name-owner-trace.md
ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5  crates/yu-hir/src/module/local_source.rs
c40ebde1755d300c83aafba0a81a85d19ed5200dfc2163ab72c8a3bb08baf29a  crates/yu-hir/src/module.rs
b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f  crates/yu-hir/src/module/source_annotation.rs
66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c  crates/yu-solver/src/candidate_source.rs
6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0  crates/yu-solver/src/candidate_effect.rs
d4ff8a9e98eb667a5eb85aff9c0feec1f0227e86257bb56892493ac1d04a9278  crates/yu-solver/src/candidate_scheme.rs
fc0d948d884a406746066f3df8db257d5c6686505166b330bef839a9b9e2f35d  crates/yu-solver/src/candidate_extrusion.rs
8a1f531be9fb5e5f160bf4f75c6eb98bbc35ce0a30acaf06424c531840504ba4  crates/yu-solver/src/candidate_intrusion.rs
42f89dcf5fa6d7095db1e220c89308a2a35f4e74b05c3e8821d4fb2e3e32b0ca  crates/yu-solver/src/candidate_context.rs
8738c1b1699228b1a4dfd30af7e03d0afb100ca6124d23037c645246d888dc50  crates/yu-solver/src/candidate_value_graph.rs
5bbcf27d51906814ba38b2cca2066807d285d0b1817f0ea6e04d70c4a5c8a5cb  crates/yu-solver/src/shadow_apply.rs
2300400e87d0a487225f207d414ac71fa4f21c6f80279fea4f793e43c7809aee  crates/yu-solver/src/lib.rs
```
