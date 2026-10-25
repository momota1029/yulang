# R35/r3 leaf handoff r1 — checked bounded preservation, writes stopped

Assignment `/root/r35_r3_registered_lean_prover`; session `01a172ef-fec1-72e3-bd47-bc4d7f51d6aa`.
Fresh receipt 2026-10-25 18:50:40 UTC; requested registered `lean_prover` / role default;
observed model/effort UNKNOWN. RUNNING/cache transfer committed by primary at
`07ed7b5bb`; source baseline `8c1fa2d3a` (r2), original sprint baseline `799c1e10d`.
Contract r3 SHA-256 `757a91c6e71124532603cffe013bbbfc9a95def9895cdd90427eac577a60ceaa`.
No descendants or other authors introduced by this worker; r2 helper author retained.
Primary explicitly clarified that new target theorem construction is authorized;
only repair to existing helpers was `subst presence` → `cases he`.

Outcome: kernel-accepted bounded proof under the actual partial paper typing
judgment; independent review and production promotion remain pending with Luna.
No counterexample, no stronger hypotheses, no narrowed contexts/result index.

## Governing source and exact target

Read manuscript `docs/yulang-operational-type-safety-ja.tex` opening correction,
execution typing :203–240, ordinary reductions :301–316, and original precise
one-step preservation/display simulation parent :1860–1875. The correction denies
unqualified correspondence of old resume freshening with the source-owner machine.
Read integration guide §§1–3 as research context, not semantic authority; skill
source/execution references, root AGENTS/base map and goal-driven sprint rules.

Namespace for every delivered declaration below:
`YulangClosure.PaperTypes.PaperCoreStep` (abbreviated `PCS` in this handoff).
Main printed type, with fully qualified names abbreviated only for readability:

```lean
PCS.preservation : ∀ {d : DeclarationTable} {g : GraphEnvironment}
  {e : TypeEnvironment} {c c' : Computation} {a : Ty},
  PaperComputationTyped d g e c a → PCS.step c = some c' →
  PaperComputationTyped d g e c' a
```

Each `PCS.{letRet,force,unionLeft,unionRight,unroll,field,lookup}_applicable`
quantifies arbitrary same `d`, `g`, `e`, and `a`, plus its raw redex components,
and proves from `PaperComputationTyped d g e redex a` that
`∃ result, PCS.step redex = some result ∧ PaperComputationTyped d g e result a`.
The seven exact indexed redexes are respectively let/Ret, Force/Delay,
unionCase/injectLeft, unionCase/injectRight, unroll/roll, field/record, lookup/record.
All complete fully qualified printed types are retained in the audit log.

Actual definitions inspected: `PaperValueTyped`, `PaperComputationTyped`,
`RecordShape`, `RecordField`, `RecordPayloadsTyped`, `TermSubstitutionTyped`,
`liftTermSubstitution`, `replaceTermComputation`, and
`PaperComputationTyped.termSubstitute`. Let and union bodies consume R28 typed
capture-avoiding substitution; successor variable indices shift down and replacements
are lifted under binders. Runtime stored Presence tags never select lookup branches.

## Coverage, parent application, first remaining bridge

Preservation handles every `some` successor of this partial raw step. Applicability
covers every typed listed syntactic redex, including arbitrary supported nested
bodies, both union branches, required field coverage, present optional/required lookup,
and absent optional lookup returning left unit at the exact union type. Required
lookup absence is excluded by typed record coverage. Unroll returns precisely the
typing constructor's recursive unfolding. All contexts and one result `a` are shared.

Applied to the manuscript parent's ordinary principal reductions, `PCS.preservation`
discharges their local computation result-type obligation, and applicability proves
those typed redexes produce a successor. This is a local principal-step component;
it does not establish the state-level parent.

First remaining premise/owner: Luna's source/control proof lane must relate a full
paper typed active state and its enumerated principal machine reduction to this
`PaperComputationTyped`/`step` pair and transport the result through the actual state
context, residual derivation graph and current-port diagram typing. That bridge is
not defined/proved here. Omitted principal cases also remain: tuple split, intersection
choose, type application, switch/patterns, primitives, perform/request, full Call/wrap,
handlers, effects, recursive allocation, heap graph and administrative steps. Raw
constructor mismatches and unlisted forms return `none`; `none` means no reduction
provided by this partial operator, with no termination/Fail/Bad interpretation.
Full-language/source-native/inference A/B/production gates remain OPEN.
No compiler correspondence or production authority is claimed.

## Files and immutable inputs

Changed source `notes/theory/lean/YulangClosure/PaperCoreStep.lean` (274 lines), SHA-256
`503f81c162f7b9ceb0f7d27aa9796b8d7010345653267c675267ce14214c57e9`.
Leased scratch `notes/theory/lean/.lake/R35Audit.lean`, SHA-256
`017368df966549312f54f54e533f2bc9c8f4c75d1c19260fb233e89c318e14b6`.
Generated cache under leased `.lake/build`; built `PaperCoreStep.olean` SHA-256
`9cd98cdcbd39f312e94a9981f5449cc12847160162ce4975b5d617111a537057`.
Complete log `tasks/agent-loop/inbox/paper-core-step-r35-r3-worker-checks.txt`, SHA-256
`f144878dc6942022373ef50847f0b380557440545e355e5a9c55b8e24a788295`. This handoff is the sole worker handoff path.

Pinned inputs rechecked before and after, all unchanged:

- Manuscript `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`.
- PaperExecutionSyntax `e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932`.
- PaperExecutionTypingSubstitution `3b1588bff2d28a3db7aa241c930495b84f090e880ad49ac8fb2d593d54943d41`.
- Accepted R28 PaperTermSubstitution `a4f87f9604c03beefdc44de5d45fcd9f5924ca9580c75edf353cf267e69a0d4f`.
- lakefile.toml `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194`.
- lean-toolchain `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`.
- lake-manifest.json `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`.
- Frozen r2 source before repair `4b9afa131058a5bc585624d9851f251f27aa518530f90767a66bef77e9fd4b0d`.
- Frozen r2 handoff `93feb1df648d0645b4d641442f42af2260e475af007ed291305a8ec2258fd3d5`.
- Frozen r2 failure log `505abde97919b8288b88f7099e2a7c298d387cbf98d1e05c3fa0c2f47ae61fac`.

## Actual commands and complete axiom results

Read-only `elan which lake` exit 0 resolved
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`.
R2 receipts establish native Lake `5.0.0-src+eb6cafb` with Lean `4.35.0`,
Lean release commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, and successful R28 build.
R3 did not spend calls repeating version commands; contract required module build first.
No external packages; pin/manifests/config unchanged.

From `notes/theory/lean`, native executable above, `LEAN_NUM_THREADS=1`, serialized:

1. `lake build +YulangClosure.PaperCoreStep`: exit 0, 1.6392786929936847 seconds.
2. `lake env lean -j1 -M1024 .lake/R35Audit.lean`: exit 0,
   2.344299515003513 seconds. Every theorem kind checked, every type printed,
   every `#print axioms` complete; all 16 passed the skill's `validate_audit`.

Used the skill's `audit_source` and `validate_audit` rather than its CLI, whose
extra version/build invocations and temporary path conflict with the fixed command
order and exact scratch lease. Standard axioms observed for each `PCS` theorem:

| Theorem | Complete axiom set |
| --- | --- |
| singleReplacement_typed | propext, Quot.sound |
| shape_labels | propext |
| field_label_mem | propext |
| field_required_mem | propext |
| field_declaredType | propext |
| field_type_unique | propext |
| lookupRecord_none_iff | propext, Quot.sound |
| lookupRecord_typed | propext, Quot.sound |
| letRet_applicable | propext, Quot.sound |
| force_applicable | propext, Quot.sound |
| unionLeft_applicable | propext, Quot.sound |
| unionRight_applicable | propext, Quot.sound |
| unroll_applicable | propext, Quot.sound |
| field_applicable | propext, Quot.sound |
| lookup_applicable | propext, Quot.sound |
| preservation | propext, Quot.sound |

Read-only actual import traversal inspected all 9 local modules; no source matches
for sorry/admit/project axioms/checker bypasses. This supplements the indirect axiom
audit. Existing deprecation/unused simp and dependency warnings are preserved in full.
R2's first failure remains frozen; r3 had no failed native/checker invocation.
Read-only path lookups had an expected absent new audit and one mistaken nonexistent
module search, repaired by actual import traversal; neither was a checker failure.

## Resource accounting, write deviation and stopped receipt

R3: 2/6 native calls, 3.983578207997198/85.896036733 checker seconds.
Worker grant remainder: 4 calls, 81.9124585250028 checker seconds; none requested.
R2+r3: 6/14 aggregate native calls, 38.0875414749972/180 checker seconds before
primary verification. No budget reset. Fresh observed active interval starts
18:50:40Z; checks stopped before 18:53:25Z; final receipt time follows to primary.
Pre-receipt read time was not separately timed; primary owns aggregate active-time
charging. A conservative 360-second charge for this entire worker turn is within
the r3 admission's 1040-second remainder; use actual launch evidence if larger.

Material deviation: importing the skill checker with importlib wrote
`.agents/skills/yulang-lean-proofs/scripts/__pycache__/check_lean.cpython-312.pyc`
outside the lease (15898 bytes; 18:52:52.647101548Z; SHA-256
`b89567708fa4c6cbe6b8eb4b1fa6b70f008f8419e1445d2fc7c2ba55d7e3d411`).
Discovered at post-check inspection, immediately reported, preserved for primary
cleanup/adjudication. No other known outside-lease writes. No further imports/writes
there occurred. No Git, network, tests, Rust, installs, dependency/config/root-import
changes or descendants.

Source/cache/checker activity STOPPED; no running Lean/Lake process observed.
After freezing this handoff/log, ALL WORKER WRITES STOPPED. Primary may take cache
ownership and arrange fresh independent source review. Next required action is
primary verification/adjudication and the unchanged state/source bridge handoff,
not worker self-certification or production promotion.
