# R301 source signature bridge — frozen obstruction and extractor handoff

Assignment `R301-SOURCE-SIGNATURE-BRIDGE`, revision 1. Contract: direct `/root` assignment, confirmed by `/root` message that no separate R301 contract exists. Baseline supplied by primary: `22d2a09f2`, not inspected through Git. Worker/author `/root/signature_real_source_bridge`; no descendants. Requested role Astra core producer, requested effort medium by role instruction; observed model/effort UNKNOWN, session identity UNKNOWN. Budget 1200 seconds; exact active duration not instrumented, unused reservation not reclaimed here.

Outcome: **source-native-evidence / BLOCKED at authentic extraction and semantic interpretation**. R159 parent-edge delta **zero**. No Rust execution or newly proved theorem is claimed. The two leased paths were this handoff and `notes/theory/lean/YulangClosure/SourceSignatureBridgeR301.lean`; the latter was deliberately not created because another syntax mirror or a target-assuming relation would not establish the assigned bridge.

## Actual source route and available evidence

The exact retained object already exists; its source contents need not be reconstructed from native effect rows.

1. `crates/yu-hir/src/module/source_annotation.rs::declarations_selected`, lines 351–384, calls `parse_type_source`, requires an outer Function, and creates `Arc<SourceOperationDeclaration>` containing full `SourceOperationId`, `signature_position`, and recursive `signature`. `parse_type_source` (495–599), `parse_group` (601–628), and `parse_row` (630–684) supply the actual syntax. Arrow argument effects belong to the argument subtree; the newly constructed Function has no outer row. Grouping can merge an outer row only when the nested row is absent. Rows retain source position, ordered concrete identities and symbolic variables; ambiguous/missing concrete resolution and more than one symbolic variable reject formation.
2. `candidate_source.rs` Operation case (1718–1731) clones the resolved declaration into `Action::Operation`; action execution (2515) calls `candidate_operation`. The preflight at 629–634 additionally requires no root effects, outer Function, `operation_signature_values_supported` and `preflight_annotation`. Hole/Tuple retention in HIR is **not** a claim that operation signatures with those constructors pass this preflight. No full-language domain restriction follows from this candidate route.
3. `candidate_effect.rs::candidate_operation` (1280–1307) passes the actual `&declaration.signature` with the original Arc-bearing `SignatureContext::Operation` to `candidate_signature_value`, then retains the value constraint at source occurrence slot 42. Its temporary value/effect/view caches are dropped. `SignatureContext::operation` (360) clones the Arc into `OperationOrigin`; `candidate_signature_view` (1219–1265) stores it in `ViewOrigin::Operation`. This retained origin includes operation occurrence; View additionally contains owner, source position, ordered allowed members and tail.
4. Public readback is already available through `shadow_apply.rs::CandidateGraphEffectViewOrigin::OperationInterface` (2701), `CandidateGraphEffectOperand::OperationInterfaceMember` (2979), and `CandidateSourceOperationApplyEffectJoin::declaration()` (3149). A research extractor can start at that returned declaration and traverse `declaration.signature` directly. Existing `source_operation_apply_effect_joins` (2090–2215) checks owned operation/FreshUse/Apply occurrences, exact source callee containment, captured `BoundKey`, source/copy declaration **pointer identity**, owner/position/operation identity, exact FreshUse mapping and native invocation/application effect row. This is stronger than matching a family or canonical row, but remains a structural, successful-candidate observation with a 256-record bound.

The existing R159 source/native audit already establishes item 4 at identical file hashes. It is reused, not counted as new theorem progress. R301 isolates its precise full-signature extraction use-site and the additional path/encoding boundary.

## Why a manually written Lean signature is not authentic extraction

`yu-syntax/src/full_parse.rs::SourceNodeKey` (72–100) compares parse Arc identity, retained green-node identity and start offset. Debug output is intentionally redacted. `yu-hir/src/module.rs::HirOccurrenceId` (1153) is artifact-branded and explicitly nonserializable; its ordinal alone is insufficient across HIR artifacts. SourceEffectId includes ModuleId **and** declaration SourceNodeKey; SourceOperationId includes family **and** its own declaration key. Spelling, range, Debug text, or plain occurrence ordinal cannot replace those equalities.

Existing formal observation code in `candidate_effect.rs::formal_permission_constructor_owner_domain_graph_export_observation` (3685–3968) provides a reusable method: collect actual keys, intern using native Eq, retain the original objects while checking equality/injectivity, and emit path-indexed row data. It currently observes formal-annotation constructors and exported permission ports. Its test-only `FormalCaptureTypedEvent` and `FormalPortStep` traversal originate in `candidate_formal_value_pair`/`candidate_formal_effect_port`; they do not authenticate operation traversal merely by sharing the annotation type.

`candidate_signature_value` (2545–2673) has no path argument or retained per-node source-to-Term incidence record. Its Function branch does recurse into argument/result, flips polarity and variance independently on argument descent, and passes the outer operation family to the **result effect** only when `std::ptr::eq(ty, &declaration.signature)`. The operation name/root identity must not be moved to the nested returned Function. Positive primitive Functions additionally replace both effect ports with a shared fresh entry row; Annotation scope and omission policy also differ. A single generic signature policy would erase these distinctions.

## Exact missing outputs and provisional implementation TODOs

These are research evidence requests, not production authority. Primary reported a separate research-only Rust extractor assignment; this worker does not duplicate or write it.

**R301-EXTRACT-1** — owner: research extractor, source entrypoint above. Parse/lower an authentic source input; obtain the retained declaration through the real origin route (or report that the chosen fixture does not reach it); traverse the original recursive HIR signature, not a reconstructed native shape. Emit one run-local object table whose IDs are assigned by complete native Eq: source roots/occurrences, operation/family IDs, signature/row/hole positions. Retain Function Argument/Result and ordered Tuple Element paths, all value constructors, complete optional rows, member order, variable spelling, and the difference between omitted and explicit empty rows. Emit both original HIR extraction and retained-origin readback and compare them using original native identities. Include source bytes, owner route, relevant source hashes and actual command/exits. This gives bounded actual-source extraction evidence; universal Rust-to-Lean correspondence remains an independent proof.

Falsifiers: parse the identical text twice and reject cross-parse key substitution; lower the same parse into different HIR artifacts and reject occurrence-ordinal substitution; swap same-spelling declarations or sibling paths; compare omitted and explicit-empty rows; use callable result `() -> (int -> int)` to ensure no ground-only decoder replaces it. Do not manufacture an unavailable successful join merely to obtain a sample.

**R301-PORT-1** — owner: candidate signature lowering/observer, only if native field incidence is needed. Add a research-only observer at the real `candidate_signature_value` invocation/return, recording original operation Arc/root identity, structural path, independent polarity/variance, returned Term and all actual Function fields; at `candidate_signature_effect` record source row/family argument, returned Term, actual allocated/cached view/row and complete insertion key. Join this to the same retained operation origin and exact Apply observation. Existing formal tracing is a reusable pattern, not evidence for this route. A post-hoc shape decoder cannot establish that the constructor emitted those pairs. Falsifiers: exchanged sibling ports, moving outer Self to a nested Function, conflating invocation/application effects, cache-hit provenance from another row, and substituting canonical rows without the actual transport chain.

**R301-EI-1** — owner: original source complete-interface construction, independent of extraction. Supply EI-Form/All-Form's real complete computation/function descriptors, independent challenge telescope, whole argument formation schema under actual CalRet binder, full IF maps/guards and original arm tags/descriptors. Construct the GR1 ViewLogic registration and establish its interpretation at the actual R293 source endpoint. HIR syntax and scalar Function/effect Terms do not contain this proof. `candidate_call.rs::PendingCallConstruction` (397 onward), `OriginalGenCall0Input` (252), and `CandidateSourceCall::unresolved` (391) explicitly leave the original suppliers pending. No new semantics or reduced source domain is authorized here.

## Application to unchanged R293/R159 and remaining premises

R300 `lookup_iff_field` proves readback only within `PrimitiveOperation.Annotation E H`. After R301-EXTRACT-1, it may be applied to the extracted **encoding**, but that will not identify the encoding with native execution by itself. R299 `checking_registry_does_not_supply_source_primitive` still leaves `original.atom environment (primitiveAtom context site declaration)` external: neither full syntax retention nor the finite Checking registry proves the declaration's independent source contract.

R293 `app_result_pair` retains arbitrary `Inputs`, state, observation and original arm endpoint list. It requires actual decoding, the original finite computation Checking from `callableImage` to **synthesis**, and original source image membership at the same ViewLogic extension. It produces the outer tagged union-body evidence paired with target membership. No input obtained here instantiates those semantic premises. The generated EI catalogue must not be identified with callableImage or synthesis without the original correspondence; GR5 does not give EI inclusion into an independently fixed target.

R159 `app_admission_iff` still requires both outer annotation alternatives, decode, independent logical admission, every App Local premise (descriptor formation, whole argument compatibility, complete Call certificate, source Call incidence, callable image, conditional singleton-formal origin, value Checking and computation Checking), and both arbitrary source child judgments at the same extension. All remain unchanged. Neither W nor Z nor foreign/independent arm quantifiers are fixed, identified, shrunk, or discharged by a native sample. No source clause or native constructor has been replaced with the desired target judgment.

## Checks and resources

Read-only `elan which lake` resolved `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`. Actual versions: Lake `5.0.0-src+eb6cafb` (Lean 4.35.0); Lean `4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. Isolated project `/tmp/yulang-r301-check`, including copied source/configuration and generated `.lake` outputs; no shared cache writes. The bundled checker with `--timeout 360`, modules R300/R293 and the four roots below passed, exit 0; import build completed 56 jobs. Per-process `-j1 -M1024`, helper `LEAN_NUM_THREADS=1`. No full default build needed: no Lean source/import changes. No Cargo/native tests, no new Rust code, no Git, no children, no user/external contact.

Axiom results: R300 lookup uses `propext`; R299 primitive boundary and R159 admission equivalence use `propext, Classical.choice, Quot.sound`; R293 result pair uses `propext, Quot.sound`. These are checks of existing theorems with their exact hypotheses, not a new proof or independent review. Complete fresh types and axiom outputs follow.

All new/scratch paths: this handoff; `/tmp/yulang-r301-check/**`; helper temporary `/tmp/yulang-lean-audit-x5hzqhgf/YulangProofAudit.lean` (helper cleans its temporary directory). Leased R301 Lean file absent. No other worker paths written. Worker state STOPPED after final freeze; no outstanding processes or descendants. Next step belongs to the already assigned research extractor and original EI source owner. Pending independent review/intake; no production promotion.

## Frozen direct inputs

- `crates/yu-hir/src/module/source_annotation.rs`: `409ce491bc216c6963bf76d20810790aa2756edf260ecc35e76d5cfc05d24b3f`
- `crates/yu-hir/src/module.rs`: `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646`
- `crates/yu-syntax/src/full_parse.rs`: `dd92603f8f5549b8b3f6e45ab6cb39b6598480b7f1cda7897e27b5113107db93`
- `crates/yu-solver/src/candidate_effect.rs`: `4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15`
- `crates/yu-solver/src/candidate_source.rs`: `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49`
- `crates/yu-solver/src/candidate_call.rs`: `fdc39e01fa3665b4dc14e167973de63b275eb0280b831e340b6cdcee5ed0fc3f`
- `crates/yu-solver/src/shadow_apply.rs`: `99d67895c250e5d79fb774728867fe2fc88c4dc22df9bfc38ac9fd1aeb0908e5`
- `notes/theory/lean/YulangClosure/SourceSignatureRealizationR300.lean`: `384ac75df5fe6269b76faf06971cca345a6029f4f6a173296042fcfdceae8449`
- `notes/theory/lean/YulangClosure/ComputedCallUnionRealizationR293.lean`: `50b1ce82dbd81d8c17a99461a78b77a9066094896f38e046d70fb4dd69365543`
- `notes/theory/lean/YulangClosure/SourceAppAdmissionR159.lean`: `5e948a1f8a3aab66028f885ebf16b6ffeed81999039e8a5a4e9c3caf84464408`
- `notes/theory/lean/YulangClosure/AuthenticSourceGraphR299.lean`: `58107dcecfeae237696dab71d9f99196403a96c0145ec5443ba55ee90a2bf217`
- `notes/design/2026-10-24-computed-call-result-constructor.md`: `2f3a5461b6dacaa29e881ba8b3003120b912e441dd5e4c47fc4ccaa27d3b31a6`
- `notes/theory/2026-10-24-generated-computed-result-correspondence.md`: `58ab61f7252818e208cc27be29fcc2c7633b35467c47dda0de126fa8bc87544b`
- `notes/design/2026-10-11-yulang-inference-top-level-principles.md`: `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`
- `tasks/agent-loop/inbox/effect-permission-source-app-r159-source-native.md`: `eb23cb7433fb40fb5a6212325dfa552c256005bc6bbcdd0fc69caa796cbf6445`
- `tasks/agent-loop/history/20261103-source-signature-r300-review.md`: `e76141a4f1ff5ff617cf2b3177b92cc192a80a090cc23a2fd2d01e140ef3f17c`

## Exact fresh theorem types and axioms

```text
YULANG_AUDIT_BEGIN YulangClosure.SourceSignatureRealizationR300.lookup_iff_field
@YulangClosure.SourceSignatureRealizationR300.lookup_iff_field : ∀ {E H : Type}
  (a b : YulangClosure.PrimitiveOperation.Annotation E H)
  (path : List YulangClosure.SourceSignatureRealizationR300.Step),
  YulangClosure.SourceSignatureRealizationR300.lookup a path = Option.some b ↔
    Nonempty (YulangClosure.SourceSignatureRealizationR300.Field a path b)
'YulangClosure.SourceSignatureRealizationR300.lookup_iff_field' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.SourceSignatureRealizationR300.lookup_iff_field
YULANG_AUDIT_BEGIN YulangClosure.AuthenticSourceGraphR299.checking_registry_does_not_supply_source_primitive
@YulangClosure.AuthenticSourceGraphR299.checking_registry_does_not_supply_source_primitive : ∀ {Value : Type}
  {s : YulangClosure.OriginalSourceInterpretation.Sorts} (inputs : YulangClosure.OriginalSourceInterpretation.Inputs s)
  (registry : YulangClosure.OriginalSourceChecking.GuardRegistry inputs)
  (declarations : YulangClosure.OriginalSourceChecking.Declarations inputs registry)
  (reading : YulangClosure.OriginalSourceChecking.Reading s Value)
  (original : YulangClosure.OriginalSource.Kernel Value) (environment : YulangClosure.OriginalSource.Environment Value)
  (context : YulangClosure.OriginalSource.Context) (site : YulangClosure.OriginalSource.Site)
  (declaration : YulangClosure.OriginalSource.Declaration),
  YulangClosure.OriginalSource.SourceJudgment
      (YulangClosure.OriginalSourceChecking.kernel inputs registry declarations reading original) environment context
      (YulangClosure.OriginalSource.Source.primitive { site := site } declaration) ↔
    original.atom environment (YulangClosure.AuthenticSourceGraphR299.primitiveAtom context site declaration)
'YulangClosure.AuthenticSourceGraphR299.checking_registry_does_not_supply_source_primitive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.AuthenticSourceGraphR299.checking_registry_does_not_supply_source_primitive
YULANG_AUDIT_BEGIN YulangClosure.ComputedCallUnionRealizationR293.app_result_pair
@YulangClosure.ComputedCallUnionRealizationR293.app_result_pair : ∀
  {s : YulangClosure.OriginalSourceInterpretation.Sorts} {View : Type}
  (inputs : YulangClosure.OriginalSourceInterpretation.Inputs s)
  (registry : YulangClosure.OriginalSourceChecking.GuardRegistry inputs)
  (readout : YulangClosure.OriginalSourceEnvironment.RuntimeReadout s View)
  (ports : YulangClosure.OriginalSourceChecking.PortReadout s View)
  (declarations : YulangClosure.OriginalSourceChecking.Declarations inputs registry)
  (original : YulangClosure.OriginalSource.Kernel (YulangClosure.OriginalSourceEnvironment.Payload s View))
  (environment : YulangClosure.OriginalSource.Environment (YulangClosure.OriginalSourceEnvironment.Payload s View))
  (context : YulangClosure.OriginalSource.Context) (mark : YulangClosure.OriginalSource.Mark) (occurrence : Nat)
  (data : YulangClosure.OriginalSourceEnvironment.Logical s View)
  (state : YulangClosure.OriginalSourceEnvironment.Decoded s View),
  YulangClosure.OriginalSourceEnvironment.decode readout environment = Option.some state →
    ∀ (arms : List YulangClosure.OriginalSource.Endpoint)
      (raw : YulangClosure.OriginalSourceInterpretation.RawObservation s),
      YulangClosure.OriginalSource.Checking
          (YulangClosure.OriginalSourceChecking.kernel inputs registry declarations
            (YulangClosure.OriginalSourceChecking.environmentReading inputs readout ports) original)
          (environment.extend { site := mark.site, kind := YulangClosure.OriginalSource.BinderKind.viewLogic }
            (YulangClosure.OriginalSourceEnvironment.scopeCandidate environment occurrence
              (YulangClosure.OriginalSourceEnvironment.Payload.logical
                YulangClosure.OriginalSourceEnvironment.LogicalKind.viewLogic data)))
          { mode := YulangClosure.OriginalSource.CheckMode.computation, site := mark.site, context := context,
            lower := { site := mark.site, port := YulangClosure.OriginalSource.Port.callableImage },
            upper := { site := mark.site, port := YulangClosure.OriginalSource.Port.synthesis } } →
        YulangClosure.OriginalSourceInterpretation.Meaning inputs
            (YulangClosure.OriginalSourceInterpretation.Query.trace
              (raw.atInterface
                ((state.logical data).interfaces
                  { site := mark.site, port := YulangClosure.OriginalSource.Port.callableImage }))) →
          (YulangClosure.ComputedCallUnionRealizationR293.unionBody inputs (state.logical data)
                  { site := mark.site, port := YulangClosure.OriginalSource.Port.callableImage } arms raw).Holds
              (YulangClosure.OriginalSourceInterpretation.Meaning inputs) ∧
            YulangClosure.OriginalSourceInterpretation.Meaning inputs
              (YulangClosure.OriginalSourceInterpretation.Query.trace
                (raw.atInterface
                  ((state.logical data).interfaces
                    { site := mark.site, port := YulangClosure.OriginalSource.Port.synthesis })))
'YulangClosure.ComputedCallUnionRealizationR293.app_result_pair' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.ComputedCallUnionRealizationR293.app_result_pair
YULANG_AUDIT_BEGIN YulangClosure.SourceAppAdmissionR159.app_admission_iff
@YulangClosure.SourceAppAdmissionR159.app_admission_iff : ∀ {s : YulangClosure.OriginalSourceInterpretation.Sorts}
  {View : Type} (inputs : YulangClosure.OriginalSourceInterpretation.Inputs s)
  (readout : YulangClosure.OriginalSourceEnvironment.RuntimeReadout s View)
  (admissions : YulangClosure.OriginalSourceEnvironment.LocalAdmissions s View)
  (original : YulangClosure.OriginalSource.Kernel (YulangClosure.OriginalSourceEnvironment.Payload s View))
  (environment : YulangClosure.OriginalSource.Environment (YulangClosure.OriginalSourceEnvironment.Payload s View))
  (context : YulangClosure.OriginalSource.Context) (mark : YulangClosure.OriginalSource.Mark)
  (callee argument : YulangClosure.OriginalSource.Source YulangClosure.OriginalSource.Category.expression),
  have kernel := YulangClosure.OriginalSourceEnvironment.admissionKernel inputs readout admissions original;
  YulangClosure.OriginalSource.SourceJudgment kernel environment context
      (YulangClosure.OriginalSource.Source.app mark callee argument) ↔
    (∀ (premise : YulangClosure.OriginalSource.Premise),
        premise ∈ YulangClosure.SourceAppAdmissionR159.annotationPremises context mark →
          YulangClosure.OriginalSource.Local kernel environment premise) ∧
      ∃ occurrence data state,
        YulangClosure.OriginalSourceEnvironment.decode readout environment = Option.some state ∧
          admissions.logical state { site := mark.site, kind := YulangClosure.OriginalSource.BinderKind.viewLogic }
              YulangClosure.OriginalSourceEnvironment.LogicalKind.viewLogic data ∧
            have candidate :=
              YulangClosure.OriginalSourceEnvironment.scopeCandidate environment occurrence
                (YulangClosure.OriginalSourceEnvironment.Payload.logical
                  YulangClosure.OriginalSourceEnvironment.LogicalKind.viewLogic data);
            have after :=
              environment.extend { site := mark.site, kind := YulangClosure.OriginalSource.BinderKind.viewLogic }
                candidate;
            (∀ (premise : YulangClosure.OriginalSource.Premise),
                premise ∈ YulangClosure.SourceAppAdmissionR159.appPremises context mark callee argument →
                  YulangClosure.OriginalSource.Local kernel after premise) ∧
              YulangClosure.OriginalSource.SourceJudgment kernel after context callee ∧
                YulangClosure.OriginalSource.SourceJudgment kernel after context argument
'YulangClosure.SourceAppAdmissionR159.app_admission_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
YULANG_AUDIT_END YulangClosure.SourceAppAdmissionR159.app_admission_iff
[exit 0]
PASS: YulangClosure.SourceSignatureRealizationR300.lookup_iff_field, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.AuthenticSourceGraphR299.checking_registry_does_not_supply_source_primitive, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.ComputedCallUnionRealizationR293.app_result_pair, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.SourceAppAdmissionR159.app_admission_iff, under its printed hypotheses; axiom whitelist satisfied.
Named declarations only; ordinary-mistake check, not independent review or source correspondence.
```

Full checker log SHA-256: `2fd8c8feab38c4d5a4153af3baacd8e0d1e357344258299b8364ad993a337a4d`.
