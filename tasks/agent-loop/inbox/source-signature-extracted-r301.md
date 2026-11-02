# Source signature extracted R301 — finite HIR → Lean instance

Author: `/root/source_signature_lean_bridge` (bounded leaf, no children).
Status: constructed and checker-accepted finite instance; independent review PENDING.
Baseline observed: `d8753fd29d019785424b28b880fefb64a6a3862d`.
Exact packet: primary's source-signature R301 assignment, <=900s; no semantics,
production/compiler, shared status, root imports, dependency or Git writes.
The current-state R286 contract was read as required; it does not authorize or
specify this separate R301 packet. The primary's exact R301 lease controls it.

## Outcome and original parent

The fixture is parsed and lowered through the real `yu-syntax`/`yu-hir` APIs by
the frozen reviewed extractor. Its exact `--lean` stdout is the generated module;
no edits, namespace changes, expected values or proof text are inserted there.
It contains three `Signature Nat Nat` values and its **same-execution** JSON
identity table, operation field/port inventory, operation uses and HIR diagnostics.
A fresh offline isolated native build was used, so executable provenance does
not rely on an unverified preexisting binary. Re-extraction is byte-identical.

`SourceSignatureExtractedChecksR301.lean` is handwritten. Its expected signature,
row values, paths and signs come from source lines 2–4, not a Rust-generated
expected-value function. All seven nested paths are explicit. The separate
handwritten `/tmp/.../check_metadata.py` compares the generated module's embedded
JSON against source slices, row identities, all nested fields/ports, resolutions
and diagnostics. It never derives expected paths/values from producer output.
The script is an executable finite check, not independent review or a theorem
about the extractor. The Python script is reproduced below for review.

Governing sources: native-signature-formation definition §§1–4 selects the
reviewed signature-incidence construction §§2–6. The original Theorem SIG §7
preserves complete dependent source-port schemas, original introductions/routes,
independent semantic witnesses, scopes and registered sharing. Theorem IF in
call-source-interface construction §6 assumes actual finite resolved source,
authentic complete original operation, independently typed primitive interfaces
and lawful whole-map actions, and constructs its full diagram before challenges.
Opening correction/selection notices were read; research drafts grant no further
authority. This packet instantiates retained HIR syntax only, not SIG/IF semantics.

The unchanged whole parent in `Contracts.lean`,
`YulangClosure.SourceProblem.InferenceSoundness p`, remains:

```lean
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

All source, scope, solution quantifiers and the shared witness `e` remain intact.
No concrete `SourceProblem` instance is supplied here. No A/B or whole-parent
closure is claimed. Source/native and production gates remain OPEN.

## Represented source and identity boundary

- Line 2: nested function arguments/results; primitive Unit/Int, variable `'a`;
  tail-only negative row `['arg]`; positive `[F, E, F, 'out]` retaining order,
  duplicate F and symbolic tail; result `[E]`; omission at all other fields.
- Line 3: explicit empty `[]` differs from omitted rows.
- Line 4: ordered tuple with variable and hole, plus callable result. HIR
  retention includes both; R300 `operationValues signature2 = false` retains
  their unsupported operation-value status. Signatures 0/1 pass **value shape**
  only; actual solver preflight is not executed or asserted.
- Actual `E::nested` use resolves to the exact operation-table Arc; `E::missing`
  remains unresolved. All four original HIR diagnostics are retained, including
  UnsupportedItem effect placeholders and UnsupportedExpression uses.
- This fixture omits Bool/Str, imports/external modules, catches/pattern-use
  inventories, multiple-row-tail malformed rejection, aliases and recursive
  registrations. Those omitted cases are not removed from the language or
  asserted covered by this finite extraction.

Within the embedded JSON, families 0/1 identify actual E/F `SourceEffectId`
Eq classes. Source keys 5/6/7 identify bracket rows at byte ranges [29,36),
[43,59), [65,69); empty-row key 11 is [94,97), hole key 15 is [124,125).
The complete Eq identities are interned during the **same selected parse/run**.
Nat numbers, spelling, byte ranges and ordinal positions do not authenticate
native identity across executions. A separate JSON run compares equal serialized
data; this is reproducibility, never cross-run identity. The generated artifact
also embeds its canonical absolute source path, so byte-exact regeneration
assumes the same path/environment and fixture bytes.

## Parent application and remaining premises

`callable_field_readback` applies R300 `fieldRead_exact` to the actual extracted
nested callable with arbitrary independent initial signs. `argument_result_field`
applies R300 `lookup_iff_field` at the actual path. `positive_callable_plan` and
`negative_argument_tail` apply R300's pure operation-effect branch lemmas,
retaining full rows and root Self contribution; nested owners clear Self.
These are syntax/branch-policy theorems, not mutable allocation/cache or typing.

`original_app_requires_computation_check` applies R159 `app_source_iff` and
`app_continuation_iff`, then R300 `actual_union_consumer`, to an arbitrary
**assumed original App derivation**. It recovers one admitted candidate and
the original computation checking Local at that exact candidate's environment
extension. It preserves arbitrary Kernel, Environment, Context, Mark and both
source children. It does not infer an App proof from extracted syntax.

First remaining source bridge: prove the frozen Rust extractor's general
source/HIR→Lean representation correspondence (or an authenticated production
certificate), including original typed port/primitive semantic interfaces and
whole-map actions. Owner: primary's source/native correspondence lane.
At R159 `app_admission_iff`, the first original admission conjunct remains
`decode readout environment = some state` with
`admissions.logical state ⟨mark.site, .viewLogic, 0⟩ .viewLogic data`, for one
shared occurrence/data/state and candidate. All original annotation locals,
App locals (descriptor formation, whole argument compatibility, complete call
certificate, source-call incidence, callable image and conditional origin),
both checks and both children still require proof at that same environment.
Owner: original semantic admission/IF/GR5 proof lanes, assigned by primary.
This packet supplies none of these independent semantic premises.

## Actual verification and failures

Pinned native Lake: `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`.
Read-only `elan which lake` resolved that installed path; it emitted a latest-release
query warning while using the existing pin, and did not install anything.
Versions: Lake `5.0.0-src+eb6cafb` / Lean `4.35.0`, x86_64 Linux,
commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
Rust `1.95.0 (59807616e 2026-04-14)`; Cargo
`1.95.0 (f2d3ce0bd 2026-03-21)`.

Commands and actual exits:

```sh
CARGO_TARGET_DIR=/tmp/yulang-source-signature-r301/cargo cargo build --offline --locked --manifest-path tools/inline-authentic-extraction/Cargo.toml --bin source_signature_r300 -j1
# exit 0, 24.89s, existing yu-hir dead-code warnings (8); no authorized repair lease
/tmp/yulang-source-signature-r301/cargo/debug/source_signature_r300 --lean tools/inline-authentic-extraction/fixtures/source-signature-r301.yu > notes/theory/lean/YulangClosure/SourceSignatureExtractedR301.lean
# exit 0; repeated to /tmp/.../regenerated.lean; cmp exit 0
/tmp/yulang-source-signature-r301/cargo/debug/source_signature_r300 tools/inline-authentic-extraction/fixtures/source-signature-r301.yu > /tmp/yulang-source-signature-r301/extraction.json
# exit 0
python3 /tmp/yulang-source-signature-r301/check_metadata.py
# exit 0, explicit expected slices/paths/rows/ports/resolution/diagnostics PASS
# isolated project cwd: /tmp/yulang-source-signature-r301/lean
LEAN_NUM_THREADS=1 /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake build +YulangClosure.SourceSignatureRealizationR300
# exit 0, 56 jobs
LEAN_NUM_THREADS=1 /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake build +YulangClosure.SourceSignatureExtractedChecksR301
# final exit 0, 58-job dependency closure
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake env lean -j1 -M1024 YulangClosure/SourceSignatureExtractedChecksR301.lean
# exit 0
```

Bundled checker command: `python3 .agents/skills/yulang-lean-proofs/scripts/check_lean.py`
with `--project /tmp/yulang-source-signature-r301/lean`, the exact `--lake` above,
`--timeout 120`, `--module YulangClosure.SourceSignatureExtractedR301`,
`--module YulangClosure.SourceSignatureExtractedChecksR301`, and one `--theorem`
for **every one of the 14 fully qualified declarations printed below**.
Checker exit 0, all four internal commands exit 0 (versions, module build, audit).
No `--full` default-root claim: root imports were outside the lease.

Material failures preserved: first Lake invocation from repository root exited 1
(no lakefile). First isolated module build exited 1: unqualified Step resolved to
machine Step, constructor parameters are Effect/Hole rather than E/H, and Kernel,
Environment, SourceJudgment, Local live in OriginalSource. The handwritten file
was repaired to these actual definitions; no theorem hypothesis or conclusion
was weakened. Original failed logs remain in scratch with hashes below.
An earlier version lookup used relative read paths from the project cwd and
reported missing files; corrected root-relative reads established all inputs.
Existing imported R104 unused-simp warning and yu-hir dead-code warnings were
observed; their files are outside this leaf's lease and return to primary.

Complete dependency search found no sorry/admit/project-axiom/checker-bypass/
native_decide matches in 57 local Lean input files. Their copied checked sources
are byte-identical to working inputs, recorded in `/tmp/.../lean-inputs.json`.
All theorem kind checks passed. Axiom groups: 5 empty; 8 `[propext]`; original
App necessary consequence `[propext, Classical.choice, Quot.sound]`. Exact types
and complete per-theorem outputs follow below.

## Frozen files, resources and handoff

Only the three artifact paths below and this handoff were written in the repo.
All cache/generated binary/audit output ownership is isolated under
`/tmp/yulang-source-signature-r301` (~580 MiB at check); the skill also used a
unique temporary audit directory and cleaned it. No shared `.lake` writes,
compiler edits, toolchain/manifest/lock changes, root imports or Git mutations.
One Cargo build and one isolated Lean build at a time; all Lean work uses
one thread and project `-j1 -M1024`; helper timeout 120s; no background jobs.
No precise aggregate CPU/RSS measurement was made. Native build time is the
actual Cargo 24.89s receipt, not an estimate. All subprocesses finished.

Writes stopped after finalizing this handoff; files are frozen for fresh review.
Primary owns independent review, shared status/intake, warning-owner disposition,
Git and any next packet. This producer has not self-certified source semantics.

Artifact/direct dependency SHA-256:

- `notes/theory/lean/YulangClosure/SourceSignatureExtractedR301.lean`: `f88acdeeca2d083c0408c488b05c8d0f8d91b8604f754a5b59cf067a30a9bad6`
- `notes/theory/lean/YulangClosure/SourceSignatureExtractedChecksR301.lean`: `279e8771297dad208af6fce199f8163b8a0e0508b11a748a9c22b5a8c2aaddbe`
- `tools/inline-authentic-extraction/fixtures/source-signature-r301.yu`: `65f88c17fbc256ea31f2fe4859308a479455f1d04ff771c5042b85faabc7b5fd`
- `tools/inline-authentic-extraction/src/bin/source_signature_r300.rs`: `e72138e1982bebe2ca6fe1e867b4cc8d70126524b1946875e05deb8a7cc35c18`
- `notes/theory/lean/YulangClosure/SourceSignatureRealizationR300.lean`: `384ac75df5fe6269b76faf06971cca345a6029f4f6a173296042fcfdceae8449`
- `notes/theory/lean/YulangClosure/SourceAppAdmissionR159.lean`: `5e948a1f8a3aab66028f885ebf16b6ffeed81999039e8a5a4e9c3caf84464408`
- `notes/theory/lean/YulangClosure/AuthenticSourceGraphR299.lean`: `58107dcecfeae237696dab71d9f99196403a96c0145ec5443ba55ee90a2bf217`
- `notes/theory/lean/YulangClosure/OriginalUnionOwnerR292.lean`: `c353bd68c7bb32b2031cbc7af0e5144a57be9944027accd503e26d2efb442d66`
- `crates/yu-hir/src/module/source_annotation.rs`: `409ce491bc216c6963bf76d20810790aa2756edf260ecc35e76d5cfc05d24b3f`
- `crates/yu-solver/src/candidate_effect.rs`: `4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15`
- `tools/inline-authentic-extraction/Cargo.lock`: `35495bd146b24e7b27f5556676440556156a994b93b5ab43e2a3cab3c1dd2d7f`
- `notes/design/2026-10-08-native-signature-formation-definition.md`: `e6c6cf995a3618172e45b4f8cdf4578313c057c6ec1e3e118c4dc11b6f162ab9`
- `notes/theory/2026-10-08-source-signature-incidence-construction.md`: `7367ce8eb69376583386c6d675d067712ec6fa173e96f458ee34ce390dc8901a`
- `notes/theory/2026-10-08-call-source-interface-construction.md`: `278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98`

Scratch evidence SHA-256:

- `/tmp/yulang-source-signature-r301/checker.log`: `a898a1665006a0d2992da46be415857e631a417048acd446c00efad225b7c362`
- `/tmp/yulang-source-signature-r301/check_metadata.py`: `b3ba4647c491a2c001826d1d17ca597bd405b65dc00f9430c6328e22ebc47e39`
- `/tmp/yulang-source-signature-r301/metadata.log`: `a670924fed56afeb228c6ca4e7056ca7a742d117a8c46d5d22d060e1bf3eb2a8`
- `/tmp/yulang-source-signature-r301/lean-inputs.json`: `adc2df2c6fb1908aa773412543ade83cdecaefd3e0544ec7f958176038f403c3`
- `/tmp/yulang-source-signature-r301/cargo-build.log`: `4b8eea607dad7aab12e7391af0521099a4352d0937d19dedb6a3eb0440874826`
- `/tmp/yulang-source-signature-r301/lean-first.log`: `ec23038f8eea027fb8a682d2a427c6a2bfe8a8b5ca60cd9d87c62f74fbf81537`
- `/tmp/yulang-source-signature-r301/lean-first-isolated.log`: `cfae6aeba786a9eafd1ceaa8c7eff7499b06d31512bb6c83af01718f72cf8a53`
- `/tmp/yulang-source-signature-r301/lean-repaired.log`: `e2a6585cb6fbfb76646de22f38bb633ff9e2b9171020be1cc2eec05b644aa15b`
- `/tmp/yulang-source-signature-r301/direct-lean.log`: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`
- `/tmp/yulang-source-signature-r301/extraction.json`: `a3898c6edb49eabad657d71851b1d3fa318ae0b1ee96135f5991370fc3efa9ab`
- `/tmp/yulang-source-signature-r301/dependency-search.log`: `01ba4719c80b6fe911b091a7c05124b64eeece964e09c058ef8f9805daca546b`

## Handwritten metadata check (exact script)

```python
import json
from pathlib import Path
root=Path('/home/momota1029/rust/yulang')
gen=root/'notes/theory/lean/YulangClosure/SourceSignatureExtractedR301.lean'
fixture=root/'tools/inline-authentic-extraction/fixtures/source-signature-r301.yu'
line=next(x for x in gen.read_text().splitlines() if x.startswith('def extractionJson : String := '))
j=json.loads(json.loads(line.removeprefix('def extractionJson : String := ')))
assert j['source']==fixture.read_text()
assert j['source_path']==str(fixture)
# Expected slices and paths are handwritten; never computed from producer output.
expected_keys={0:(0,141,'ActDeclaration'),1:(142,148,'ActDeclaration'),
 5:(29,36,'BracketRow'),6:(43,59,'BracketRow'),7:(65,69,'BracketRow'),
 11:(94,97,'BracketRow'),15:(124,125,'TypeExpression'),
 16:(164,172,'PathTail'),18:(190,199,'PathTail')}
for key,(a,b,kind) in expected_keys.items():
 k=j['keys'][key]; assert (k['id'],k['byte_range'],k['syntax_kind'])==(key,[a,b],kind)
for key,spelling in {5:" ['arg]",6:" [F, E, F, 'out]",7:' [E]',11:' []',15:'_',16:'::nested',18:'::missing'}.items():
 a,b=j['keys'][key]['byte_range']; assert j['source'][a:b]==spelling
assert [(f['id'],f['declaration_key']) for f in j['families']]==[(0,0),(1,1)]
assert [(o['spelling'],o['family_id']) for o in j['operations']]==[('nested',0),('empty',0),('retained',0)]
row=lambda p,cs,vs: dict(position_key=p,concrete_family_ids=cs,variables=vs)
expected=[([], 'function',True,None),(['argument'],'function',False,None),
 (['argument','argument'],'unit',True,None),(['argument','result'],'int',False,row(5,[],["'arg"])),
 (['result'],'function',True,row(6,[1,0,1],["'out"])),
 (['result','argument'],'variable',False,None),(['result','result'],'int',True,row(7,[0],[]))]
assert j['operations'][0]['fields']==[dict(path=p,kind=k,positive=s,variance_positive=s,effects=r) for p,k,s,r in expected]
assert [(p['function_owner_path'],p['argument_effect_path'],p['result_effect_path'],p['argument_positive'],p['argument_variance_positive'],p['result_positive'],p['result_variance_positive'],p['result_family']) for p in j['operations'][0]['function_ports']]==[
 ([],['argument'],['result'],False,False,True,True,0),
 (['argument'],['argument','argument'],['argument','result'],True,True,False,False,None),
 (['result'],['result','argument'],['result','result'],False,False,True,True,None)]
assert j['operations'][1]['fields'][2]['effects']==row(11,[],[])
assert j['operations'][2]['signature']['argument']['elements'][1]==dict(kind='hole',effects=None,position_key=15)
assert [(u['source_key'],u['resolution'],u['operation_index']) for u in j['operation_uses']]==[(16,'resolved_same_arc_as_table',0),(18,'unresolved',None)]
assert [(d['kind'],d['byte_range'],d['retained_effect_placeholder']) for d in j['hir_diagnostics']]==[
 ('UnsupportedItem',[0,141],True),('UnsupportedItem',[142,148],True),
 ('UnsupportedExpression',[163,172],False),('UnsupportedExpression',[189,199],False)]
# Separate JSON run has equal serialized data, which is reproducibility only.
assert j==json.loads(Path('/tmp/yulang-source-signature-r301/extraction.json').read_text())
print('PASS: handwritten source slices, same-artifact labels, all nested fields/ports, retained empty/hole, use resolution, unchanged diagnostics; separate-run JSON data equal (no cross-run identity claim)')
```

## Complete printed theorem types and axiom audits

```text
YULANG_AUDIT_BEGIN YulangClosure.SourceSignatureExtractedChecksR301.nested_exact
YulangClosure.SourceSignatureExtractedChecksR301.nested_exact : YulangClosure.SourceSignatureExtractionR300.signature0 =
  YulangClosure.SourceSignatureExtractedChecksR301.expectedNested
'YulangClosure.SourceSignatureExtractedChecksR301.nested_exact' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.SourceSignatureExtractedChecksR301.nested_exact
YULANG_AUDIT_BEGIN YulangClosure.SourceSignatureExtractedChecksR301.empty_exact
YulangClosure.SourceSignatureExtractedChecksR301.empty_exact : YulangClosure.SourceSignatureExtractionR300.signature1 =
  YulangClosure.PrimitiveOperation.Annotation.function Option.none
    (YulangClosure.PrimitiveOperation.Annotation.primitive Option.none YulangClosure.PrimitiveOperation.Primitive.unit)
    (YulangClosure.PrimitiveOperation.Annotation.primitive
      (Option.some YulangClosure.SourceSignatureExtractedChecksR301.emptyRow)
      YulangClosure.PrimitiveOperation.Primitive.int)
'YulangClosure.SourceSignatureExtractedChecksR301.empty_exact' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.SourceSignatureExtractedChecksR301.empty_exact
YULANG_AUDIT_BEGIN YulangClosure.SourceSignatureExtractedChecksR301.retained_exact
YulangClosure.SourceSignatureExtractedChecksR301.retained_exact : YulangClosure.SourceSignatureExtractionR300.signature2 =
  YulangClosure.PrimitiveOperation.Annotation.function Option.none
    (YulangClosure.PrimitiveOperation.Annotation.tuple Option.none
      [YulangClosure.PrimitiveOperation.Annotation.variable Option.none "'a",
        YulangClosure.PrimitiveOperation.Annotation.hole Option.none 15])
    (YulangClosure.PrimitiveOperation.Annotation.function Option.none
      (YulangClosure.PrimitiveOperation.Annotation.primitive Option.none
        YulangClosure.PrimitiveOperation.Primitive.unit)
      (YulangClosure.PrimitiveOperation.Annotation.primitive Option.none
        YulangClosure.PrimitiveOperation.Primitive.int))
'YulangClosure.SourceSignatureExtractedChecksR301.retained_exact' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.SourceSignatureExtractedChecksR301.retained_exact
YULANG_AUDIT_BEGIN YulangClosure.SourceSignatureExtractedChecksR301.nested_fields
YulangClosure.SourceSignatureExtractedChecksR301.nested_fields : List.map
    (YulangClosure.SourceSignatureRealizationR300.fieldRead YulangClosure.SourceSignatureExtractionR300.signature0
      Bool.true Bool.true)
    [[], [YulangClosure.SourceSignatureRealizationR300.Step.argument],
      [YulangClosure.SourceSignatureRealizationR300.Step.argument,
        YulangClosure.SourceSignatureRealizationR300.Step.argument],
      [YulangClosure.SourceSignatureRealizationR300.Step.argument,
        YulangClosure.SourceSignatureRealizationR300.Step.result],
      [YulangClosure.SourceSignatureRealizationR300.Step.result],
      [YulangClosure.SourceSignatureRealizationR300.Step.result,
        YulangClosure.SourceSignatureRealizationR300.Step.argument],
      [YulangClosure.SourceSignatureRealizationR300.Step.result,
        YulangClosure.SourceSignatureRealizationR300.Step.result]] =
  [Option.some (YulangClosure.SourceSignatureExtractedChecksR301.expectedNested, Option.none, Bool.true, Bool.true),
    Option.some
      (YulangClosure.SourceSignatureExtractedChecksR301.expectedArgument, Option.none, Bool.false, Bool.false),
    Option.some
      (YulangClosure.PrimitiveOperation.Annotation.primitive Option.none
          YulangClosure.PrimitiveOperation.Primitive.unit,
        Option.none, Bool.true, Bool.true),
    Option.some
      (YulangClosure.PrimitiveOperation.Annotation.primitive
          (Option.some YulangClosure.SourceSignatureExtractedChecksR301.argumentRow)
          YulangClosure.PrimitiveOperation.Primitive.int,
        Option.some YulangClosure.SourceSignatureExtractedChecksR301.argumentRow, Bool.false, Bool.false),
    Option.some
      (YulangClosure.SourceSignatureExtractedChecksR301.expectedResult,
        Option.some YulangClosure.SourceSignatureExtractedChecksR301.callableRow, Bool.true, Bool.true),
    Option.some
      (YulangClosure.PrimitiveOperation.Annotation.variable Option.none "'a", Option.none, Bool.false, Bool.false),
    Option.some
      (YulangClosure.PrimitiveOperation.Annotation.primitive
          (Option.some YulangClosure.SourceSignatureExtractedChecksR301.resultRow)
          YulangClosure.PrimitiveOperation.Primitive.int,
        Option.some YulangClosure.SourceSignatureExtractedChecksR301.resultRow, Bool.true, Bool.true)]
'YulangClosure.SourceSignatureExtractedChecksR301.nested_fields' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.SourceSignatureExtractedChecksR301.nested_fields
YULANG_AUDIT_BEGIN YulangClosure.SourceSignatureExtractedChecksR301.retained_tuple_fields
YulangClosure.SourceSignatureExtractedChecksR301.retained_tuple_fields : YulangClosure.SourceSignatureRealizationR300.fieldRead
      YulangClosure.SourceSignatureExtractionR300.signature2 Bool.true Bool.true
      [YulangClosure.SourceSignatureRealizationR300.Step.argument,
        YulangClosure.SourceSignatureRealizationR300.Step.element 0] =
    Option.some
      (YulangClosure.PrimitiveOperation.Annotation.variable Option.none "'a", Option.none, Bool.false, Bool.false) ∧
  YulangClosure.SourceSignatureRealizationR300.fieldRead YulangClosure.SourceSignatureExtractionR300.signature2
        Bool.true Bool.true
        [YulangClosure.SourceSignatureRealizationR300.Step.argument,
          YulangClosure.SourceSignatureRealizationR300.Step.element 1] =
      Option.some
        (YulangClosure.PrimitiveOperation.Annotation.hole Option.none 15, Option.none, Bool.false, Bool.false) ∧
    YulangClosure.SourceSignatureRealizationR300.lookup YulangClosure.SourceSignatureExtractionR300.signature2
        [YulangClosure.SourceSignatureRealizationR300.Step.argument,
          YulangClosure.SourceSignatureRealizationR300.Step.element 2] =
      Option.none
'YulangClosure.SourceSignatureExtractedChecksR301.retained_tuple_fields' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.SourceSignatureExtractedChecksR301.retained_tuple_fields
YULANG_AUDIT_BEGIN YulangClosure.SourceSignatureExtractedChecksR301.independent_signs
YulangClosure.SourceSignatureExtractedChecksR301.independent_signs : YulangClosure.SourceSignatureRealizationR300.fieldRead
    YulangClosure.SourceSignatureExtractionR300.signature0 Bool.true Bool.false
    [YulangClosure.SourceSignatureRealizationR300.Step.argument,
      YulangClosure.SourceSignatureRealizationR300.Step.argument] =
  Option.some
    (YulangClosure.PrimitiveOperation.Annotation.primitive Option.none YulangClosure.PrimitiveOperation.Primitive.unit,
      Option.none, Bool.true, Bool.false)
'YulangClosure.SourceSignatureExtractedChecksR301.independent_signs' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.SourceSignatureExtractedChecksR301.independent_signs
YULANG_AUDIT_BEGIN YulangClosure.SourceSignatureExtractedChecksR301.callable_field_readback
YulangClosure.SourceSignatureExtractedChecksR301.callable_field_readback : ∀ (p v : Bool),
  YulangClosure.SourceSignatureRealizationR300.fieldRead YulangClosure.SourceSignatureExtractionR300.signature0 p v
      [YulangClosure.SourceSignatureRealizationR300.Step.result] =
    Option.some
      (YulangClosure.SourceSignatureExtractedChecksR301.expectedResult,
        Option.some YulangClosure.SourceSignatureExtractedChecksR301.callableRow, p, v)
'YulangClosure.SourceSignatureExtractedChecksR301.callable_field_readback' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.SourceSignatureExtractedChecksR301.callable_field_readback
YULANG_AUDIT_BEGIN YulangClosure.SourceSignatureExtractedChecksR301.argument_result_field
YulangClosure.SourceSignatureExtractedChecksR301.argument_result_field : Nonempty
  (YulangClosure.SourceSignatureRealizationR300.Field YulangClosure.SourceSignatureExtractionR300.signature0
    [YulangClosure.SourceSignatureRealizationR300.Step.argument,
      YulangClosure.SourceSignatureRealizationR300.Step.result]
    (YulangClosure.PrimitiveOperation.Annotation.primitive
      (Option.some YulangClosure.SourceSignatureExtractedChecksR301.argumentRow)
      YulangClosure.PrimitiveOperation.Primitive.int))
'YulangClosure.SourceSignatureExtractedChecksR301.argument_result_field' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.SourceSignatureExtractedChecksR301.argument_result_field
YULANG_AUDIT_BEGIN YulangClosure.SourceSignatureExtractedChecksR301.operation_value_shapes
YulangClosure.SourceSignatureExtractedChecksR301.operation_value_shapes : YulangClosure.SourceSignatureRealizationR300.operationValues
      YulangClosure.SourceSignatureExtractionR300.signature0 =
    Bool.true ∧
  YulangClosure.SourceSignatureRealizationR300.operationValues YulangClosure.SourceSignatureExtractionR300.signature1 =
      Bool.true ∧
    YulangClosure.SourceSignatureRealizationR300.operationValues
        YulangClosure.SourceSignatureExtractionR300.signature2 =
      Bool.false
'YulangClosure.SourceSignatureExtractedChecksR301.operation_value_shapes' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.SourceSignatureExtractedChecksR301.operation_value_shapes
YULANG_AUDIT_BEGIN YulangClosure.SourceSignatureExtractedChecksR301.positive_callable_plan
YulangClosure.SourceSignatureExtractedChecksR301.positive_callable_plan : YulangClosure.SourceSignatureRealizationR300.operationEffectPlan
    4 (Option.some YulangClosure.SourceSignatureExtractedChecksR301.callableRow) (Option.some 0) Bool.true Bool.true =
  Option.some
    (YulangClosure.SourceSignatureRealizationR300.EffectPlan.view Bool.true 6 [0, 1, 0, 1] (Option.some "'out"))
'YulangClosure.SourceSignatureExtractedChecksR301.positive_callable_plan' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.SourceSignatureExtractedChecksR301.positive_callable_plan
YULANG_AUDIT_BEGIN YulangClosure.SourceSignatureExtractedChecksR301.negative_argument_tail
YulangClosure.SourceSignatureExtractedChecksR301.negative_argument_tail : YulangClosure.SourceSignatureRealizationR300.operationEffectPlan
    4 (Option.some YulangClosure.SourceSignatureExtractedChecksR301.argumentRow) Option.none Bool.false Bool.false =
  Option.some (YulangClosure.SourceSignatureRealizationR300.EffectPlan.tail Bool.false "'arg")
'YulangClosure.SourceSignatureExtractedChecksR301.negative_argument_tail' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.SourceSignatureExtractedChecksR301.negative_argument_tail
YULANG_AUDIT_BEGIN YulangClosure.SourceSignatureExtractedChecksR301.omitted_empty_distinct
YulangClosure.SourceSignatureExtractedChecksR301.omitted_empty_distinct : YulangClosure.SourceSignatureRealizationR300.effects
    (YulangClosure.PrimitiveOperation.Annotation.primitive Option.none YulangClosure.PrimitiveOperation.Primitive.int) ≠
  YulangClosure.SourceSignatureRealizationR300.effects
    (YulangClosure.PrimitiveOperation.Annotation.primitive
      (Option.some YulangClosure.SourceSignatureExtractedChecksR301.emptyRow)
      YulangClosure.PrimitiveOperation.Primitive.int)
'YulangClosure.SourceSignatureExtractedChecksR301.omitted_empty_distinct' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.SourceSignatureExtractedChecksR301.omitted_empty_distinct
YULANG_AUDIT_BEGIN YulangClosure.SourceSignatureExtractedChecksR301.family_only_outer
YulangClosure.SourceSignatureExtractedChecksR301.family_only_outer : YulangClosure.SourceSignatureRealizationR300.selfFamily
      0 [] =
    Option.some 0 ∧
  YulangClosure.SourceSignatureRealizationR300.selfFamily 0
        [YulangClosure.SourceSignatureRealizationR300.Step.argument] =
      Option.none ∧
    YulangClosure.SourceSignatureRealizationR300.selfFamily 0
        [YulangClosure.SourceSignatureRealizationR300.Step.result] =
      Option.none
'YulangClosure.SourceSignatureExtractedChecksR301.family_only_outer' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.SourceSignatureExtractedChecksR301.family_only_outer
YULANG_AUDIT_BEGIN YulangClosure.SourceSignatureExtractedChecksR301.original_app_requires_computation_check
@YulangClosure.SourceSignatureExtractedChecksR301.original_app_requires_computation_check : ∀ {Value : Type}
  (kernel : YulangClosure.OriginalSource.Kernel Value) (environment : YulangClosure.OriginalSource.Environment Value)
  (context : YulangClosure.OriginalSource.Context) (mark : YulangClosure.OriginalSource.Mark)
  (callee argument : YulangClosure.OriginalSource.Source YulangClosure.OriginalSource.Category.expression),
  YulangClosure.OriginalSource.SourceJudgment kernel environment context
      (YulangClosure.OriginalSource.Source.app mark callee argument) →
    ∃ candidate,
      kernel.admitted environment { site := mark.site, kind := YulangClosure.OriginalSource.BinderKind.viewLogic }
          candidate ∧
        YulangClosure.OriginalSource.Local kernel
          (environment.extend { site := mark.site, kind := YulangClosure.OriginalSource.BinderKind.viewLogic }
            candidate)
          (YulangClosure.OriginalSource.Premise.checking
            { mode := YulangClosure.OriginalSource.CheckMode.computation, site := mark.site, context := context,
              lower := { site := mark.site, port := YulangClosure.OriginalSource.Port.callableImage },
              upper := { site := mark.site, port := YulangClosure.OriginalSource.Port.synthesis } })
'YulangClosure.SourceSignatureExtractedChecksR301.original_app_requires_computation_check' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.SourceSignatureExtractedChecksR301.original_app_requires_computation_check
```
