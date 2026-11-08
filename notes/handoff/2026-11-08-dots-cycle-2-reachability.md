# Cycle 2 — T7b declaration reachability (read-only, provisional)

Date: 2026-11-08. Snapshot: local merge `4c25d90d9`, integrated base `5fd6ffa2c`.
No declaration or module was deleted. This is an analysis, **not deletion approval**.
`lean/Main.lean` and `lean/MainStatements.lean` were absent at this snapshot.

## Tool and methodology

`tools/Reach.lean` imports the actual compiled `Yulang`, `SpecExamples`, and
historical `Yulang.EOFRoleInference` (also explicitly imported by Audit).
It computes the transitive constant-reference closure of every root's type and
value, including opaque proof values (`ConstantInfo.value? (allowOpaque := true)`).
Every non-system loaded declaration is written to a TSV with its actual defining
module and a reachability bit. Unknown or empty roots fail, rather than silently
being skipped. The tool does not decide which claims should be retained.

The import closure below was separately computed from the snapshot's `import`
lines. A module with no reachable declaration can still be necessary because a
retained module imports it. Registration/environment-extension/runtime needs are
not captured solely by a theorem's expression dependencies. In particular,
“unreachable” does not mean “false”, “obsolete”, or “safe to delete”.

## Two root profiles

### A. Exploratory current-entry roots (not approved as a complete retention set)

```text
Yulang.CommonRoleSettledResolver.resolve_exact
Yulang.CommonRoleSettledResolver.accessible
Yulang.CommonRoleOpenRecursivePass.run_exact
Yulang.CommonRoleOpenRecursivePass.run_recollects
Yulang.CommonDeclarationVarianceRegistry.registry_exact
Yulang.CommonSourceOptionalX22.x22_proved
Yulang.CommonRoleIntervalCandidateFrontier.solutions_exact
```

Actual output: `REACH: 7 roots; 5029/82374 non-system declarations reachable`.
Of 1130 declaration-owning non-system modules, 945 have no reached declaration.
750 of those are also outside the import closure of the declaration-reached
modules **when operational aggregators are deliberately excluded**. This is not
an acceptable deletion set: these seven statements do not cover all language
features, old counterexamples, examples, or future bridge requirements.

Examples in that exploratory set:

| Module | Lines | Reason to retain / inspect, not delete |
|---|---:|---|
| `CommonRoleAssociatedExactness` | 89 | E2 documents a real semantic mismatch; historical evidence remains valuable. |
| `CommonRoleClosedIntervalInspection` | 101 | Local closed-interval component; being absent from these seven roots does not establish supersession. |
| `CommonRoleIntervalCandidates` | 202 | Candidate semantics may still be needed by future open-interval integration. |
| `CommonRoleIntervalDictionaries` | 210 | Dictionary correctness is not represented by all selected roots. |
| `CommonRoleOpenNormalization` | 98 | Currently unconnected bridge, not an obsolete result; T1c may require it. |
| `CommonRoleOpenPropagationOrigin` | 82 | Source provenance is explicitly unfinished, so an unused provenance lemma is not a deletion reason. |

### B. All existing Audit roots (conservative existing proof commitments)

Extracted 6251 distinct literal `#print axioms` names from `lean/Audit.lean`.
Actual output: `REACH: 6251 roots; 39732/82374 non-system declarations reachable`.
Thus 42642 loaded declarations are not referenced from these roots.
19 declaration-owning modules have no reachable declaration and are outside
imports of modules with reachable declarations (excluding operational aggregators).

| Module | Declarations | Lines | Retention rationale |
|---|---:|---:|---|
| `Yulang.CommonFiniteParameters` | 9 | 71 | Finite parameter helper; inspect whether intended future bridge or unused support. No deletion approved. |
| `Yulang.ErrorEffectExamples` | 162 | 163 | Example/check coverage can be valuable without theorem-to-theorem dependency. No deletion approved. |
| `Yulang.HornExamples` | 17 | 63 | Example/check coverage can be valuable without theorem-to-theorem dependency. No deletion approved. |
| `Yulang.JointConstraintInferenceExamples` | 46 | 109 | Example/check coverage can be valuable without theorem-to-theorem dependency. No deletion approved. |
| `Yulang.JunctionEffectExamples` | 24 | 83 | Example/check coverage can be valuable without theorem-to-theorem dependency. No deletion approved. |
| `Yulang.LoopEffectExamples` | 122 | 150 | Example/check coverage can be valuable without theorem-to-theorem dependency. No deletion approved. |
| `Yulang.OpenRecordConstraintGraphExamples` | 26 | 93 | Example/check coverage can be valuable without theorem-to-theorem dependency. No deletion approved. |
| `Yulang.PresenceDataExamples` | 47 | 102 | Example/check coverage can be valuable without theorem-to-theorem dependency. No deletion approved. |
| `Yulang.RigidRecordValueInferenceExamples` | 28 | 98 | Example/check coverage can be valuable without theorem-to-theorem dependency. No deletion approved. |
| `Yulang.SemanticRecordCheckerExamples` | 55 | 99 | Example/check coverage can be valuable without theorem-to-theorem dependency. No deletion approved. |
| `Yulang.SemilinearDecisionExamples` | 17 | 65 | Example/check coverage can be valuable without theorem-to-theorem dependency. No deletion approved. |
| `Yulang.SemilinearNormalizationExamples` | 22 | 71 | Example/check coverage can be valuable without theorem-to-theorem dependency. No deletion approved. |
| `Yulang.SemilinearRowAlgebraExamples` | 13 | 83 | Example/check coverage can be valuable without theorem-to-theorem dependency. No deletion approved. |
| `Yulang.ShadowRecordLatticeCheck` | 76 | 160 | Example/check coverage can be valuable without theorem-to-theorem dependency. No deletion approved. |
| `Yulang.SourceDataOrderExamples` | 31 | 95 | Example/check coverage can be valuable without theorem-to-theorem dependency. No deletion approved. |
| `Yulang.StrictApplicationExamples` | 12 | 66 | Example/check coverage can be valuable without theorem-to-theorem dependency. No deletion approved. |
| `Yulang.StructuralDecisionExamples` | 49 | 116 | Example/check coverage can be valuable without theorem-to-theorem dependency. No deletion approved. |
| `Yulang.TypeConstraintGraphExamples` | 59 | 139 | Example/check coverage can be valuable without theorem-to-theorem dependency. No deletion approved. |
| `Yulang.TypeConstraintInferenceExamples` | 43 | 123 | Example/check coverage can be valuable without theorem-to-theorem dependency. No deletion approved. |

**Operational import result: zero removal candidates in either profile.**
When `Yulang`, `Audit`, and `SpecExamples` are retained as operational roots,
all 1130 declaration-owning modules are in their import closure. In particular,
`Yulang.lean` explicitly imports the 19 modules above. Removing them would require
separate approval to edit imports and a justification that their test/semantic
coverage is dispensable. No such approval is inferred here.

## Reproduction

From the repository root, generate the conservative roots (no repository writes):

```sh
python3 - <<'PYROOTS'
import re
from pathlib import Path
text = Path('lean/Audit.lean').read_text()
roots = list(dict.fromkeys(re.findall(r'^#print axioms (\S+)', text, re.M)))
Path('/tmp/yulang-reach-audit-roots.txt').write_text('\n'.join(roots) + '\n')
PYROOTS
cd lean
YULANG_REACH_ROOTS=/tmp/yulang-reach-audit-roots.txt \
YULANG_REACH_OUTPUT=/tmp/yulang-reach-audit.tsv \
lake env lean ../tools/Reach.lean
```

The generated TSV includes every loaded project declaration and its bit; it was
inspected locally rather than committing a large snapshot-derived declaration
listing. The roots, method, counts and complete conservative module list are
preserved here. Rerun after imports or root statements change.

## Validation and limits

- Both root profiles executed successfully with Lean 4.35.0 (exit 0).
- An Audit-root attempt initially failed on `EOFRoleInference.fragmentCheck_exact`;
  the tool initially omitted Audit's explicit EOF import. Added that same import,
  reran, and checked all 6251 names. No roots were dropped to make the run pass.
- Initial elaboration errors (mutable-name shadowing and a numeric type annotation)
  were fixed before successful runs.
- No `Main*.lean` root statements existed to add; later drafts must be imported and
  selected explicitly. Whether the exploratory root list captures the user's
  intended main theorem is **not established**.
- Expression dependency is syntactic, not semantic relevance. Generated constants,
  mutual inductive blocks, environment extensions, examples and imports require
  retention analysis beyond the declaration bit.
- T7b is a useful provisional analysis; a justified deletion list and owner approval
  remain absent. T7c is not performed.
