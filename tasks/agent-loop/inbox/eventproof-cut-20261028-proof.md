# EventProof actual generated Value cut — proof handoff r1

ID: EVENTPROOF-CUT-APPLICATION-20261028/r1/proof. Author: `/root/eventproof_cut_proof` (registered lean_prover leaf). Observed model variant/effort: UNKNOWN; system identifies Codex based on GPT-6. Claim class: local constructive decoded-field application supporting original soundness/Effect hygiene. Independent review: NOT_RUN, primary-owned.

## Fixed inputs and original claim

Exact launch HEAD `8b93abb3ad45fa01daf7b6080095209f683bccb4`, branch `research/eventproof-cut-application-20261028-r1`, clean at admission. Baseline `8fd68e2618ea6b3ccd5299809c7101ace1da0a98` is distinct from launch HEAD. Contract SHA-256 `c77ecb91ee40abc6d49c77a5b956df146a41277834a5a326ad18f1854737d300`. All 24 contract dependency hashes passed before writes and were rechecked against both original and scratch project after checking. All three output paths were absent before ACK. Start ACK delivered to primary at observed UTC `2026-10-27 17:04:37 UTC`; no write/Lean/Lake preceded it.

Original parent: whole Yulang inference soundness and Effect hygiene, with source/native correspondence; `Contracts.SourceProblem.InferenceSoundness` is a proposition definition, not a proved concrete instance. Source Generalize §§3.2–3.3 distinguishes actual runtime/EventField/OneShot data from description-owned EventProof eta/witness/view evidence. The exact local application target is `YulangClosure.OriginalSourceClosure.generated_value_body_consumer`, using the constructed `closureKernel` and restricted `proofAdmissions` instance. The 2026-10-27 source-closure manuscript's “Application” and “Parent application and remaining owners” sections identify original quantifiers and missing trace membership. Whole-proof closure §§1, 3–4 retains the global source/native obligations. The opening operational/source-safety corrections prohibit treating historical receiver identity as a freshly renamed owner.

Read source hashes:
- `notes/theory/2026-10-08-source-generalize-definition-and-proof.md`: `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`
- `notes/theory/2026-10-27-original-source-closure.md`: `5676be4efea28af30096b9d05a05e57252b8a422393f29da90a3076bc434c112`
- `docs/yulang-whole-proof-closure-ja.md`: `17f7518e72f5977b17ce085523adc788ba72a472041555fd18a24da96b4c79a5`
- `docs/yulang-operational-type-safety-ja.tex`: `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`
- `docs/yulang-source-type-safety-ja.tex`: `2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166`
- `notes/theory/lean/lean-toolchain`: `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`

## Delivered construction

New module: `notes/theory/lean/YulangClosure/OriginalEventProofCut.lean`, SHA-256 `a89e00cffcdb4172688807636a871a47e47ee25b2be197cdf6f4d1be99b1a448`. Its checked scratch copy is byte-identical.

- `ActualFieldsPreserved before after` names exactly the 18 equalities from `proof_packet_preserves`: descriptor, interfaces, installed, value, root, binding, event fiber, eta0, history, current, scope, authority, incidence, dictionary, fixedFrames, callOwners, active and activeRaw.
- `BodyConsumerAtCut` retains every original `BodyConsumer` conjunct and the SAME state/candidate/owner-indexed packet, then concludes preservation for EVERY actual decoded successor of that packet extension. The packet's possibly changed eta, logical witness and view interpretation are exposed as packet values.
- `body_consumer_actual_fields` inverts the existing consumer, applies actual `decode_extend`, rewrites its observed payload, uses `Option.some` injectivity, and applies `proof_packet_preserves` plus `proof_packet_uses_current_evidence`. Preservation is a conclusion.
- `generated_value_body_actual_fields` applies that result to `generated_value_body_consumer`. The original Build/Satisfies premise, Value-entry equality, arbitrary Prior/annotation, original context/pattern/body and exact existential/universal order are unchanged: `∃ description view; ∀ admitted invocation; ∃ receipt; ∀ admitted Return`. The body computation action and all subjudgments use the same EventProof witness.

This construction adds no raw-payload restriction. The restricted proofAdmissions path already belongs to the pinned generated theorem; this does not prove conservativity for arbitrary original opaque/raw logical admissions. Arbitrary original source patterns and bodies and independently admitted Return payloads remain represented. The Computation-entry generated theorem is outside this fixed Value-entry packet. No Decoded/Native.World identification or native lifetime/permission claim is made.

## Actual kernel and audit evidence

Pinned native Lake resolved read-only using `elan which lake`: `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`. Actual versions: Lake `5.0.0-src+eb6cafb`, Lean `4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Release. The one project verifier passed its 23-job selected-module build and complete named-root type/transitive-axiom checks. Only scratch `proof/project/.lake` was written.

Resource totals: 6/8 top-level Lean/Lake calls (four inside the one verifier, two originating audits), `40.182299354s` aggregate measured command intervals out of 300s, one verifier out of one, CPU affinity `[0]`, peak observed child RSS `1009660 KiB` (under 1 GiB target). Cargo=0, tests=0, Astra=0. All subprocesses exited. No source proof failures or premise changes occurred.

- UTC `2026-10-27T17:06:30.580293+00:00` to `2026-10-27T17:07:09.521324+00:00`; `38.941055409s`; exit `0`; peak child RSS `996676 KiB`. Command: `['taskset', '-c', '0', 'python3', '/tmp/yulang-eventproof-lifetime-20261028/.agents/skills/yulang-lean-proofs/scripts/check_lean.py', '--project', '/tmp/yulang-eventproof-lifetime-20261028/proof/project', '--lake', '/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake', '--module', 'YulangClosure.OriginalEventProofCut', '--theorem', 'YulangClosure.OriginalEventProofCut.body_consumer_actual_fields', '--theorem', 'YulangClosure.OriginalEventProofCut.generated_value_body_actual_fields', '--timeout', '240']`
- UTC `2026-10-27T17:07:41.678145+00:00` to `2026-10-27T17:07:42.302225+00:00`; `0.624076758s`; exit `1`; peak child RSS `1009656 KiB`. Command: `['taskset', '-c', '0', '/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake', '--no-cache', 'env', 'lean', '-j1', '-M1024', '--root=/tmp/yulang-eventproof-lifetime-20261028/proof', '/tmp/yulang-eventproof-lifetime-20261028/proof/AuditEventProofCut.lean']`
- UTC `2026-10-27T17:07:53.705756+00:00` to `2026-10-27T17:07:54.322929+00:00`; `0.617167187s`; exit `0`; peak child RSS `1009660 KiB`. Command: `['taskset', '-c', '0', '/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake', '--no-cache', 'env', 'lean', '-j1', '-M1024', '--root=/tmp/yulang-eventproof-lifetime-20261028/proof', '/tmp/yulang-eventproof-lifetime-20261028/proof/AuditEventProofCut02.lean']`

Material audit failure retained: `proof/origin-audit-01.log` exited 1 because the audit program used unsupported option `pp.maxDepth`; this was an audit-program error. The module and named-root verifier were already accepted. An exclusive new `AuditEventProofCut02.lean` removed only that option, then `origin-audit-02.log` exited 0. No existing output or proof source was overwritten.

The complete originating-module audit found exactly FOUR declarations and TWO theorem constants, including any generated/private theorem names by actual module origin. It prints the definitions and every declaration type and transitive axiom list. Results:

| Declaration | Transitive axioms |
|---|---|
| `YulangClosure.OriginalEventProofCut.ActualFieldsPreserved` | none |
| `YulangClosure.OriginalEventProofCut.BodyConsumerAtCut` | `propext`, `Classical.choice`, `Quot.sound` |
| `YulangClosure.OriginalEventProofCut.body_consumer_actual_fields` | `propext`, `Classical.choice`, `Quot.sound` |
| `YulangClosure.OriginalEventProofCut.generated_value_body_actual_fields` | `propext`, `Classical.choice`, `Quot.sound` |

No project axiom, sorryAx, checker bypass or native-evaluation axiom occurs. Focused source scan found only prose occurrences of “admit” in OriginalCheckingAdmission and “axiom” in OriginalSourceInterpretation; no declarations/holes. Origin audit has no errors or truncation. The verifier is kernel acceptance evidence, not independent review.

Complete public theorem types and axiom output:

```text
YULANG_AUDIT_BEGIN YulangClosure.OriginalEventProofCut.body_consumer_actual_fields
@YulangClosure.OriginalEventProofCut.body_consumer_actual_fields : ∀
  {s : YulangClosure.OriginalSourceInterpretation.Sorts} {View : Type}
  (intro : YulangClosure.OriginalFormalAdmission.Introduction s View)
  (assignment : YulangClosure.OriginalParameterWorld.FormalAssignment s View)
  (inputs : YulangClosure.OriginalSourceInterpretation.Inputs s)
  (registry : YulangClosure.OriginalSourceChecking.GuardRegistry inputs)
  (declarations : YulangClosure.OriginalSourceChecking.Declarations inputs registry)
  (readout : YulangClosure.OriginalSourceEnvironment.RuntimeReadout s View)
  (base : YulangClosure.OriginalSourceEnvironment.LocalAdmissions s View)
  (ports : YulangClosure.OriginalSourceChecking.PortReadout s View)
  (original : YulangClosure.OriginalSource.Kernel (YulangClosure.OriginalSourceEnvironment.Payload s View))
  (environment : YulangClosure.OriginalSource.Environment (YulangClosure.OriginalSourceEnvironment.Payload s View)),
  YulangClosure.OriginalSourceClosure.BodyConsumer intro assignment inputs registry declarations readout base ports
      original environment →
    YulangClosure.OriginalEventProofCut.BodyConsumerAtCut intro assignment inputs registry declarations readout base
      ports original environment
'YulangClosure.OriginalEventProofCut.body_consumer_actual_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalEventProofCut.body_consumer_actual_fields
YULANG_AUDIT_BEGIN YulangClosure.OriginalEventProofCut.generated_value_body_actual_fields
@YulangClosure.OriginalEventProofCut.generated_value_body_actual_fields : ∀
  {s : YulangClosure.OriginalSourceInterpretation.Sorts} {View : Type}
  (intro : YulangClosure.OriginalFormalAdmission.Introduction s View)
  (assignment : YulangClosure.OriginalParameterWorld.FormalAssignment s View)
  (inputs : YulangClosure.OriginalSourceInterpretation.Inputs s)
  (registry : YulangClosure.OriginalSourceChecking.GuardRegistry inputs)
  (declarations : YulangClosure.OriginalSourceChecking.Declarations inputs registry)
  (readout : YulangClosure.OriginalSourceEnvironment.RuntimeReadout s View)
  (base : YulangClosure.OriginalSourceEnvironment.LocalAdmissions s View)
  (ports : YulangClosure.OriginalSourceChecking.PortReadout s View)
  (original : YulangClosure.OriginalSource.Kernel (YulangClosure.OriginalSourceEnvironment.Payload s View))
  (prior : YulangClosure.OriginalFormalAdmission.Prior s View)
  (annotation : Option YulangClosure.OriginalSource.Declaration),
  intro.parameter.formal.entry = YulangClosure.OriginalSource.Entry.value →
    YulangClosure.OriginalSource.Satisfies
        (YulangClosure.OriginalSourceClosure.closureKernel intro assignment inputs registry declarations readout base
          ports original)
        (YulangClosure.OriginalFormalAdmission.priorEnvironment intro prior)
        (YulangClosure.OriginalSource.Build intro.parameter.context
          (YulangClosure.OriginalSource.Source.lambda { site := intro.parameter.lambdaSite, annotation := annotation }
            intro.parameter.formal intro.parameter.pattern intro.parameter.body)) →
      have kernel :=
        YulangClosure.OriginalSourceClosure.closureKernel intro assignment inputs registry declarations readout base
          ports original;
      have environment := YulangClosure.OriginalFormalAdmission.priorEnvironment intro prior;
      ∃ description view,
        kernel.admitted environment (YulangClosure.OriginalFormalShared.descriptionBinder intro.parameter) description ∧
          kernel.admitted
              (environment.extend (YulangClosure.OriginalFormalShared.descriptionBinder intro.parameter) description)
              (YulangClosure.OriginalFormalShared.viewBinder intro.parameter) view ∧
            ∀
              (invocation :
                YulangClosure.OriginalSource.ScopedValue (YulangClosure.OriginalSourceEnvironment.Payload s View)),
              kernel.admitted
                  ((environment.extend (YulangClosure.OriginalFormalShared.descriptionBinder intro.parameter)
                        description).extend
                    (YulangClosure.OriginalFormalShared.viewBinder intro.parameter) view)
                  (YulangClosure.OriginalFormalShared.invocationBinder intro.parameter) invocation →
                ∃ receipt,
                  kernel.admitted
                      (((environment.extend (YulangClosure.OriginalFormalShared.descriptionBinder intro.parameter)
                                description).extend
                            (YulangClosure.OriginalFormalShared.viewBinder intro.parameter) view).extend
                        (YulangClosure.OriginalFormalShared.invocationBinder intro.parameter) invocation)
                      (YulangClosure.OriginalFormalShared.receiptBinder intro.parameter) receipt ∧
                    ∀
                      (returned :
                        YulangClosure.OriginalSource.ScopedValue
                          (YulangClosure.OriginalSourceEnvironment.Payload s View)),
                      kernel.admitted
                          (YulangClosure.OriginalSourceClosure.receivedEnvironment environment intro.parameter
                            description view invocation receipt)
                          (YulangClosure.OriginalFormalShared.returnBinder intro.parameter) returned →
                        YulangClosure.OriginalEventProofCut.BodyConsumerAtCut intro assignment inputs registry
                          declarations readout base ports original
                          (YulangClosure.OriginalSourceClosure.retainedEnvironment
                            ((YulangClosure.OriginalSourceClosure.receivedEnvironment environment intro.parameter
                                  description view invocation receipt).extend
                              (YulangClosure.OriginalFormalShared.returnBinder intro.parameter) returned)
                            intro.parameter)
'YulangClosure.OriginalEventProofCut.generated_value_body_actual_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalEventProofCut.generated_value_body_actual_fields
```

Full definition expansions and all-origin types/axioms: `proof/origin-audit-02.log`, SHA-256 `32494a631abcb57ea74ea71f9fa421a0b9e9736f8556709c615fc96d0d35b5e5`. Verifier: `proof/verifier-01.log`, SHA-256 `c22e830fe031841f14fe316dba4caa4ac00e82706c9e409c00e8b1c5cabf5ae5`. Exact UTC/commands/resources: `proof/verifier-01.json`, `proof/origin-audit-01.json`, `proof/origin-audit-02.json`. Frozen scratch/input inventory: `proof/frozen-artifacts.json` (hash sent with STOP ACK; excludes itself to avoid circular hashing).

## Parent application and remaining premises

The generated Value Build now supplies the strengthened actual-cut result directly, rather than leaving field preservation as an isolated packet lemma. It supplies no inference-success, initial membership, Call/Force result-incidence or recursive L4 proof. First remaining source-soundness premise: independently establish the actual input/result trace or installed-formal membership at the selected contract, owned by the original source/primitive interpretation and recursive introduction lanes. The computation action transports such membership once established.

First remaining native Effect hygiene bridge: authenticate actual Rust constructors/readout against `Decoded` and connect those decoded history/current/owner/call fields to the original Native.World/Control execution and return semantics. Primary source/native owners retain that obligation. Equality of decoded projections alone supplies no semantic membership or permission interpretation. Full raw-admissions conservativity, whole effect hygiene, original A/B, principality, termination, implementation and production gates remain OPEN.

Next in-scope action: primary freezes these bytes and assigns fresh independent review. Mutual TODO: reviewer checks exact original quantifiers and same-witness cut composition; primary adjudicates/integrates and retains native/source parent gates. This leaf has no reviewer/Git/scheduling authority.

## Changed/scratch paths and cessation

Only new leased module, this new handoff, and `proof/` scratch were written. Scratch includes the isolated project/cache, two audit source versions, unmodified material failure logs, accepted logs and resource receipts, plus frozen inventory. Every file was created exclusively; existing tracked `.lake`, toolchain/configuration, source dependencies, root imports and compiler files were untouched. All writes stop after the frozen inventory is created; exact cessation UTC and hashes are delivered in STOP ACK. No further artifact changes are authorized after that ACK.
