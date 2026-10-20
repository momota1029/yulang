# R167 — source-authenticated whole-module execution

Status: proposed contract revision 2, no R167 lease or code change yet. Revision 1 was preserved in commit `148666e52`; its independent prospective review found that proof and implementation shared one writable evidence path. Revision 2 assigns distinct evidence paths. Fixed parent goal remains the user's complete request: proof-backed Yulang type inference/evaluator implementation, frequent primary-owned commits/pushes, and broad execution of unchanged Yulang2 Web samples in this repository. Do not redefine success around this one runtime entrypoint. No Yulang2 binary/sample execution is authorized.

## Outcome and authority

Advance R149's already adopted whole-module behavior on the actual checked-out Yulang3 evaluator: consume a source-authenticated mixed schedule of required computation initializers and direct expression roots in source order, preserve lazy values/caches/forward demands/continuations, and terminate with an honest module-level completion when the schedule is exhausted without selecting or fabricating a definition/source occurrence.

The R149 authority and finite Types/Console goal do not cap the parent goal. They provisionally authorize whole-module execution while preserving the existing selected-definition entry. R167 does not claim Types/Console sample compatibility: authenticated imported module resolution, tuple support, roles, primitives, host writes and atomic output publication remain separate required work.

## Baseline and governing pins

- Branch baseline: `fa5fd3a0fb055226875534754646e81e921fa557`.
- R149 authority contract: `tasks/agent-loop/sprints/yulang2-types-console-20261020-r149-rev10.md`, SHA-256 `31214917352b673c7467873b60d5db8e470e4d16c8370d882c266a7fcef5b3e9`.
- R149 adopted design: `notes/design/2026-10-20-r149-types-console.md`, SHA-256 `1644743185363d3c258c606a2e65245b3db8206dddeb666d2994e2471d74f7fa`.
- R166 reviewed closeout: `notes/progress/2026-10-20-r166-closeout.md`, SHA-256 `429139155dc96541eff6f4272d2b1684f5b6d095b71eb92db9df78af5b43ce63`.
- Runtime schedule owner `tools/inference-playground/src/runtime/program.rs`: `28748da0458da92b9d1190b250bbb84bdecc6643718eacbca95a04f5d6c9aa0d`.
- Runtime machine owner `tools/inference-playground/src/runtime/machine.rs`: `875213902660c06ffa393c8fef001c4e67d229486fed6ef8773c6abd9a3b23f1`.
- Runtime public/internal outcome owner `tools/inference-playground/src/runtime/mod.rs`: `64d208743793a03501a76f56bc2b511c50ed40cff3f789757a00b7d608fc846b`.
- Playground source/runtime consumer `tools/inference-playground/src/lib.rs`: `a0769f77feac552304f0516b0742637f51660c0bb8bf9391d18ae0f9de5e2473`.
- Source-local form owner `crates/yu-hir/src/module/local_source.rs`: `d9f516993c579ae8f4dd905abb8400ffc0769072a904a4b4c8d4ffbefcde6442`.
- HIR binding/source-class owner `crates/yu-hir/src/module.rs`: `153a23ecaa68fd150d8bd0cc0316f3723e1cb5d98a6e3026aadef2bfd08fd907`.

Before activation, Luna rechecks all pins and exact current leases. R166 ordinary-provider incidence and replay residual correspondence remain separately OPEN and are not silently closed by runtime work.

## Proof lane — R167-SOURCE-INITIALIZER-COMPLETENESS

Producer: `/root/r165_native_admission_proof`, after fresh launch and exact lease. Outputs:

- `notes/theory/2026-10-20-r167-module-schedule-proof.md`
- `tasks/agent-loop/inbox/20261020-r167-module-proof.md`

Establish the source-owned classification law for each actually admitted top-level binding form, then prove the runtime schedule includes every source-required computation definition and every direct expression root exactly once in source order. Preserve lazy value materialization. Inspect `Case` explicitly and distinguish retained syntax from a source-authorized computation classification. A runtime instruction shape or `HirBinding::evaluation_class` for generalization is not automatically the schedule law. Follow original source occurrence identity through `HirItem`/`LocalSource` to `ExecutionRoot`.

Success is a source-constructor classification and order correspondence for the admitted Y3 source domain, plus an exhaustive branch table including unsupported/error/recovery paths. If the current source owner does not provide a classification law for a constructor, record the precise missing authority/premise and **NO_SAFE_CODE_SLICE** for that constructor; do not infer computation status from shape or effects. No inference theorem, imported-module census or sample-wide claim follows.

No source/solver edits, tests, builds, runtime/sample/compiler execution, temporary Y2 activity, instrumentation, or semantic rule changes.

## Implementation lane — R167-WHOLE-MODULE-RUN

Owner: Luna primary. Proposed exact code leases:

- `tools/inference-playground/src/runtime/program.rs`
- `tools/inference-playground/src/runtime/machine.rs`
- `tools/inference-playground/src/runtime/mod.rs`
- `tools/inference-playground/src/lib.rs`

Evidence outputs:

- `notes/theory/2026-10-20-r167-module-runtime-simulation.md`
- `tasks/agent-loop/inbox/20261020-r167-module-implementation.md`

Implementation is conditional on proof-lane support and fresh independent prospective review. Construct the whole-module entrypoint against the reviewed complete schedule; do not require or synthesize a selected `DefId`. Preserve the selected-definition API and its execution/continuation-owner behavior. At schedule exhaustion return a module-level completion representation distinct from a source-bearing `RuntimeValue`; never fabricate a `SourceSite`, Lambda, binding or DefId. Keep value definitions lazy and cached; keep computation roots and direct expressions in their authenticated source order.

If the proof lane finds a missing source classification law for any entry that the implementation would need to execute, stop before enabling the public whole-module entrypoint. A private plumbing change is not a substitute for the scheduled whole-module outcome. R167 can implement only the fully source-authorized admitted subset and must name every omitted constructor precisely.

No imported module loader, tuple language support, standard library, roles/methods, primitive bindings, host-write resolver, CLI/Web integration, expected-output changes, test additions/runs, or Yulang2/Yulang3 sample execution in this contract. No claim of Types/Console compatibility.

## Verification and review

Prospective reviewer: `/root/r157_contract_review` on this exact contract and all proposed handoffs before grant. Final result review covers proof constructor exhaustiveness, source/HIR identity joins, lazy-value preservation, schedule order and module completion provenance; inspect code/source diff against direct pins. Primary cannot self-certify. No tests or execution are authorized in this packet; source correspondence and code review are the evidence boundary.

## Resources and stop conditions

Total cap 3600 seconds, fully charged on grant, Astra 0, no carryover: contract/preparation and prospective review 360 + proof 1200 + Luna implementation 1200 + independent review 600 + closeout/integration 240. Three UNKNOWN legacy reservations remain; maintain two review/integration slots. One proof worker may run beside Luna; no descendants.

Stop on any pin mismatch, source constructor without an applicable classification law, order/caching/owner divergence, requirement for fabricated provenance, output outside exact leases, unknown writer overlap or cap. Preserve all unrelated work. Luna alone updates current state, stages exact paths, reviews outbound commits and pushes.

## Parent limits

R167 cannot close the original inference/evaluator A/B theorem, R166 ordinary-provider incidence, R70/R71, replay residual correspondence, imported module resolution or production. The whole goal remains active beyond this sprint.
