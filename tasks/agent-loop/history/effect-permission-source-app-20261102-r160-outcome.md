# R160 outcome: selected native formation to original App bridge

Sprint: `EFFECT-PERMISSION-ORIGINAL-APP-PA/20261102-R160`, correction contract
`tasks/agent-loop/sprints/effect-permission-original-app-pa-20261102-r160-r2.md`,
SHA-256 `5bf51cba95e5c33fe1961b631af556359b479ec9154e572892ee5afcc6f082ab`.
Parent contract r1: SHA-256
`c2a81e706d633687bd8f1332f0d6bea8a7eb32a012a1bcbf4ed06094e218cc95`.
Baseline: `38619375c` on `yulang3`.

## Fixed parent and accepted bounded result

The exact original source App scope and R159 `app_admission_iff` quantifiers
were retained. Both annotations, all Local premises, both finite Checking
judgments, arbitrary callee and argument, conditional singleton-formal origin,
and one shared occurrence/payload/environment extension remain unchanged.

R160 r1's Lean consumer reductions were checked and source-reviewed. The first
source review found the r1 note had omitted selected Authoritative native
signature formation. That finding and the r1 artifact hashes were pushed in
`38619375c`. R160 r2 then applied the selected native construction and
accurately separated:

- **Already selected:** native support/Slots, complete licensing/incidence,
  witness-bearing profile projections, and the bounded source-owned
  unannotated policy, under the scope of
  `notes/design/2026-10-08-native-signature-formation-definition.md` §§2–5
  (SHA-256 `e6c6cf995a3618172e45b4f8cdf4578313c057c6ec1e3e118c4dc11b6f162ab9`)
  and `notes/theory/2026-10-08-source-signature-incidence-construction.md`
  §§2–8 (SHA-256
  `7367ce8eb69376583386c6d675d067712ec6fa173e96f458ee34ce390dc8901a`).
- **P remains OPEN:** no reviewed witness-preserving bridge yet maps that
  selected native evidence into the original App `Kernel.atom` at
  `.descriptorFormation`, `FunctionGuards.formation/profile`, actual
  annotation/governed-port/permission realization, and the `Logical` payload
  at the same binder, occurrence, and extension.
- **A remains independently OPEN:** no original initial source-context/import
  constructor and encoding into `LocalAdmissions.logical` is established.

This is a source-constructor/interpretation boundary, not a source-qualified
counterexample, full P/A closure, language change, or production approval.
No conflicting authoritative semantic alternatives were found; no user
semantic decision is currently needed.

## Lean evidence and independent review

Lean artifact:
`notes/theory/lean/YulangClosure/OriginalAppConstructionR160.lean`, current
SHA-256 `a7a766ef1d733719bfc4145bdcc9051e2e9e64521feb3fa400877a60bf9cb793`.
Proof note:
`notes/theory/2026-11-02-original-app-pa-r160.md`, SHA-256
`e5343412b792cf825c2a3436ae3f6535b996c94f2bf2a65af7e6c0ca4837e28d`.
Handoff revision 2:
`tasks/agent-loop/inbox/effect-permission-source-app-r160-proof.md`, SHA-256
`5b462a690ba96da973b9f3cb5736238cec3e7a54e6f3382c13c2ed80594ca970`.

Pinned Lean 4.35.0 built the two consumer reductions and exact R159 parent
audit. Full types and axiom reports remain in handoff revision 1/2; complete
audits were independently checked:

| Declaration | Complete transitive axioms |
|---|---|
| `OriginalAppConstructionR160.formation_consumer_iff` | `propext` |
| `OriginalAppConstructionR160.logical_admission_consumer_iff` | none |
| `SourceAppAdmissionR159.app_admission_iff` | `propext`, `Classical.choice`, `Quot.sound` |

Fresh review r1 returned **CHANGES REQUIRED** for omission of selected native
formation. Fresh delta review r2 returned substantive **PASS** after the
correction. Its minor handoff provenance/evidence clarity point was resolved
by `tasks/agent-loop/history/effect-permission-source-app-r160-proof-review-r2.md`
(SHA-256 to be recorded in current state). The reviewer confirmed every
non-comment Lean byte, theorem statement, proof term, and retained audit block
matches the authenticated r1 version; Lean did not need a second build. R159's
Lean result and axiom list are unchanged.

## Rust source/native lane

`tasks/agent-loop/inbox/effect-permission-source-app-r160-rust.md` was
independently reviewed PASS with no findings. It traces clean source Apply
identity through candidate operands/provenance to native Function and separate
callee-evaluation, invocation, argument-evaluation, and application effect
ports. The consumers still leave original formation/Gen-Call-0/source
typing/admission suppliers pending. Result: bounded `NO_SAFE_CODE_SLICE` for
constructing original P/A. The trace does not prove distinct solved effect
rows, complete effect retention, permission, or soundness.

No Rust source, Cargo, Rust build, test, scratch output, or new environment,
target, cache or worktree. Dirty/quarantined solver and runtime paths and
unreviewed unrelated artifacts remain outside the staged/pushed R160 set.
Existing Lean project/build only; R160 did not add another build directory.

## Remaining owner and next step

Owner: Luna source/Checking interpretation. Required next evidence is a
constructor-directed bridge from selected native port/license/profile witnesses
to the exact original App consumer/payload, followed by the independent A
initial-context constructor. Do not reopen native formation or use a solved
shape/observer as source admission. The next-action selector's bounded
continuation recommendation is recorded in the current state/checkpoint.
Whole effect hygiene, source/native soundness, inference, principality,
termination, and production remain OPEN.
