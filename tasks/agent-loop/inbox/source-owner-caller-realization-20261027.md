# SOURCE-OWNER-CALLER-REALIZATION-20261027/r1 — proof handoff

Assignment `/root/source_owner_caller_proof`, handoff revision **1**. Contract
SHA-256 `9c6bb17280250a83c68f42cc17dc32ccc331e60a7f5290af1d942b5e139432e6`. Code baseline
`90d6332ffc30fdb9f005e1f788bfdb3eaf82bc8c`; initial admission metadata commit
`c1af78936`. Registered `lean_prover`; sole author, no descendants. Requested
model/effort: registered defaults; observed execution model/effort and session
UUID: **UNKNOWN**. This handoff is source analysis plus a constructed, unchecked
schema; it delivers **no checked theorem**.

## Result and source authority

The implementation leaf reported a Cargo compile failure and cessation before
an executed trace existed. Luna supplied no frozen-trace hash ACK. This leaf
therefore consumed no generated trace and ran **0 Lean/Lake/checker calls,
0 checker seconds**. No printed theorem type or axiom result is claimed.
The project configuration was read and pins Lean **4.35.0**, but no actual
version command was executed in this packet.

The original parent remains the complete Yulang inference/executor objective,
including all original supported forms/quantifiers, soundness, Effect hygiene,
principality, termination and source/native obligations. Governing source:
`notes/design/2026-10-08-source-generalize-definition.md` §§2–5 selecting
`notes/theory/2026-10-08-source-generalize-definition-and-proof.md` §§3–5,
particularly §3.1 Name and §3.3 external Mono, Published/Family, and installed
Shared evidence. Original whole-language target:
`docs/yulang-whole-proof-closure-ja.md` §§1,4. Original Simple-sub preservation:
`notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1,3,5, with
`notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6. None closes here.

The schema is frozen at
`notes/theory/lean/YulangClosure/OriginalSourceCallerSchema.lean`, SHA-256
`9bb15c7f383a997c4e7d63efd521704c925e62c95072f81ad18ad2aec9ba30b9`. Namespace
`YulangClosure.OriginalSourceCallerSchema` defines raw `ModuleRow`, `RootRow`,
`ImportLeafRow`, `ExportRow`, `LookupRow`, `ImportedUseRow`, `CallerTable`,
`lookupExport` and `ImportedUseAgrees`. No `OriginalSource.Context`, semantic
Binding, root RuleTree, guard or runtime Frame is constructed. The data-only
interface was sent to implementation and Luna; both acknowledged its exact
hash. It remains **constructed but unchecked**.

## Exact first missing interpretation equation

`OriginalSourceSyntax.lean:188–198` defines `OriginalSource.Binding` with
`name`, `owner`, `kind`, `component`, `annotation`, `entry`, and `singleUse`,
then `Context := List Binding`. The original source §3.3 distinguishes an
external immutable Mono/Established certificate from a Published/Family
contract and its actual instantiation. Those classifications are constructor
outputs from the actual owning source rule.

`crates/yu-hir/src/module/source_exports.rs:1–4,151–179` explicitly retains
syntax and source identity without assigning type-level meaning;
`SourceExportId` carries module/name/source key/range/kind. The real
`SemanticImports::with_source_imports` / `SourceImportEnvironment` authenticate
consumer parse/module identity, exposed alias and exact public provider route.
`with_caller_evidence` (`module.rs:902–931`) explicitly does not validate opaque
payload meaning. These inspected owners do not supply the original semantic
`Binding.kind` or the installed certificate and dependent fields.

The first missing equation is the actual provider/source owner's interpretation
of that authenticated export/resolution into the adopted original Binding,
starting with its kind and retaining every installed semantic field, with
`lookupBinding` preserving the same resolved provider/alias. Assigning
`.external`, `.published`, `.family`, or empty/default fields merely because
import lookup succeeds would invent this equation.

A second, dependent missing equation is import elaboration at the whole source
root. `OriginalSource.Source` includes `letS`, `expressionS`, and `moduleS` but
no raw `use` constructor. The complete ordered CST/HIR root inventory can retain
the import item; it cannot erase or reinterpret that item by convention to
claim a complete original `sourceRules` tree. Consequently an actual whole-root
route and ambient scope cannot yet be specialized from that inventory. This is
an exact boundary in the inspected construction, not a universal nonexistence
theorem or source-language counterexample.

## Prepared finite application and represented cases

Implementation and proof agreed to preserve the prior nested fixture
`my value = \x -> { (\x -> x) x; x }` structurally unchanged, retaining
its actual outer-parameter argument and inner shadow/restored sibling. Named
alias `identity` and prelude `id` use separate original fixture declarations.
Changing the selected argument to an Imported resolution would invalidate reuse
of the unchanged accepted `argumentTerm`; that change was not adopted.

A consumer template reuses the exact accepted coordinate map and prepares the
complete nested finite-key, `CoordinateLaws`, selected Name/Lambda/Group/App/
Block/declaration relations, and the two Identity/application relations with
arbitrary caller Context/route/ambient parameters still explicit. It has
16 theorem candidates and **none is checked or delivered as a
proof**. After the missing trace it was preserved at
`/tmp/yulang-source-owner-caller-realization-20261027/proof/OriginalSourceCallerReification.unchecked.lean`, SHA-256 `0ce19f64dcb98918b2170407b5ee24b66c4f824240e1ad8a3e2508e8b8326836`;
the unbuildable repository consumer candidate was removed from this leaf's own
lease. No audit module was created. No root import was edited.

The intended source path is parsed consumer/providers → authenticated resolver
lookup and HIR/LocalSource ownership → frozen data table → finite Lean lookup
and selected-subtree checks. It does not establish source semantic constructor
laws, propagation, operational execution, native refinement, semantic Context,
whole-module RuleTree or runtime OwnedFrame payloads. All original parent gates
remain **OPEN**.

## Pins, resources and cessation

Independently rehashed all **56 inherited entries** (22 governing plus 34 local
import/configuration entries), with no mismatch. Manifest:
`/tmp/yulang-source-owner-caller-realization-20261027/proof/inherited-pins.json`, SHA-256 `5b54c394c12346b6464c0d46861d1295a33eb2f5cad4decb6e6940beeafa4e25`.
Ten exact governing source/interface hashes are retained at
`/tmp/yulang-source-owner-caller-realization-20261027/proof/source-map-pins.json`, SHA-256 `30bda7b7fafc44a90e00a8dddf36fc5fa134ba4fe7e8df25fd51172591ddc459`.
Private prior project/cache was copied into this lane's isolated scratch project;
that copy is no new checker evidence.

Scratch root: `/tmp/yulang-source-owner-caller-realization-20261027/proof/`. Prepared, unexecuted resource scripts:
`run_check.py`, `limited.sh`, `capture_envelope.py`. They would use explicit
`taskset`, `prlimit` (1 GiB / 120 CPU seconds) and `timeout` (120 seconds),
recording environment, inherited limits, affinity and child/wrapper status.
Since no checker was invoked, no enforcement or runtime receipt is claimed.
Observed preparation interval: `436.542`
seconds; earlier startup was uninstrumented and is not reported as zero. Checker
budget remains **0/6 calls, 0/360 seconds**. No Cargo, tests, dependency/config,
compiler, Git, shared state, or other-worker writes occurred.

Stable TODO `SOURCE-OWNER-CALLER-INTERPRETATION-1`: primary/source owner must
supply the actual provider-certificate → original Binding interpretation and
its lookup preservation, followed by complete import-root elaboration. Required
inputs are the real resolver identity and installed semantic certificate;
proposed output is the adopted owner equation, not a successful-Q predicate.
Falsifier: mismatched provider/alias, fabricated Binding field, or omitted import
root. Runtime frames remain a separate subsequent owner.

All authored repository/scratch writes cease after the final receipt. No
verification process, descendant or further construction remains pending.
Worker **STOPPED**; independent review/integration remain Luna's responsibility.
