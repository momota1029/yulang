# Cycle 3 — T7b expanded-root read-only reachability

2026-11-08 UTC. Snapshot `23b9113cf`, integration base `b6012d387`.
**No declaration/module deleted. These results are not deletion approval.**

## Scope and method

Ran the existing `tools/Reach.lean`, unchanged. It imports `Yulang`, `MainStatementsDraft`, `SpecExamples`, and `EOFRoleInference`. `Yulang` now transitively imports the promoted `Main`. It follows references in declaration types and values, including opaque proof bodies. Loaded environment has 83,076 non-system declarations in 1,151 declaration-owning modules. This count differs from the verification gate's 82,854 because Reach imports a different root environment; neither is a count of newly proved statements.

Profile A roots: every distinct literal `#print axioms` name in current `lean/Audit.lean`, not just the 8 Main statements.
Profile B roots: A plus every explicit `#check` target in `SpecConformanceIndex.lean`, and every declaration owned by `Main` (including statement definitions and compiler-generated helpers). This conservatively includes X evidence, actual entries, and Main's unproved target definitions without claiming those definitions have been proved.

Exact output (both exit 0):
```text
REACH: 6440 roots; 40189/83076 non-system declarations reachable
REACH: 6456 roots; 40191/83076 non-system declarations reachable
```

Thus profile B has 42,885 loaded declarations not reached by expression dependencies. The extra 16 roots add only two reached declarations: `Yulang.Main.passStates._sunfold`, `Yulang.Main.passStates._unsafe_rec`. Most named conformance evidence was already rooted by Audit. The small difference is a measured overlap, not a reason to select the smaller root set for deletion.

## Modules with no expression-reached declaration

The following 19 declaration-owning modules have zero reached declarations under B. Almost all are examples, and their checks/regressions can be valuable without appearing in theorem expression dependencies.

| Module | Loaded declarations |
|---|---:|
| `Yulang.CommonFiniteParameters` | 9 |
| `Yulang.ErrorEffectExamples` | 162 |
| `Yulang.HornExamples` | 17 |
| `Yulang.JointConstraintInferenceExamples` | 46 |
| `Yulang.JunctionEffectExamples` | 24 |
| `Yulang.LoopEffectExamples` | 122 |
| `Yulang.OpenRecordConstraintGraphExamples` | 26 |
| `Yulang.PresenceDataExamples` | 47 |
| `Yulang.RigidRecordValueInferenceExamples` | 28 |
| `Yulang.SemanticRecordCheckerExamples` | 55 |
| `Yulang.SemilinearDecisionExamples` | 17 |
| `Yulang.SemilinearNormalizationExamples` | 22 |
| `Yulang.SemilinearRowAlgebraExamples` | 13 |
| `Yulang.ShadowRecordLatticeCheck` | 76 |
| `Yulang.SourceDataOrderExamples` | 31 |
| `Yulang.StrictApplicationExamples` | 12 |
| `Yulang.StructuralDecisionExamples` | 49 |
| `Yulang.TypeConstraintGraphExamples` | 59 |
| `Yulang.TypeConstraintInferenceExamples` | 43 |

This is not an import-closure analysis: a module may still be imported, and environment registration, `#eval`/`#check`, runtime code generation, documentation, counterexample preservation, and future bridge requirements are not captured by the expression graph. No file is recommended for deletion. Prior cycle's 8-root result should not be used as a global retention criterion.

## Reproduction

```sh
# Run from repository root; use Lean 4.35.0 via elan.
python - <<'ROOTS'
from pathlib import Path
import re
roots=sorted(set(re.findall(r'^#print axioms (\S+)', Path('lean/Audit.lean').read_text(), re.M)))
Path('/tmp/restart-audit-roots.txt').write_text('\n'.join(roots)+'\n')
ROOTS
cd lean
YULANG_REACH_ROOTS=/tmp/restart-audit-roots.txt YULANG_REACH_OUTPUT=/tmp/restart-audit-reach.tsv lake env lean ../tools/Reach.lean
cd ..
python - <<'ROOTS'
from pathlib import Path
import re,csv
roots=set(Path('/tmp/restart-audit-roots.txt').read_text().splitlines())
extra=set(re.findall(r'^#check (\S+)',Path('lean/Yulang/SpecConformanceIndex.lean').read_text(),re.M))
extra|={r['declaration'] for r in csv.DictReader(open('/tmp/restart-audit-reach.tsv'),delimiter='\t') if r['module']=='Main'}
Path('/tmp/restart-expanded-roots.txt').write_text('\n'.join(sorted(roots|extra))+'\n')
ROOTS
cd lean
YULANG_REACH_ROOTS=/tmp/restart-expanded-roots.txt YULANG_REACH_OUTPUT=/tmp/restart-expanded-reach.tsv lake env lean ../tools/Reach.lean
```

Raw TSV files remain in the cloud workspace's `/tmp`; they are reproducible, not promised to persist across environment replacement. No repository tool changed. Hashes:
- `/tmp/restart-audit-reach.tsv`: SHA256 `40dbca38984eba396369878542729d3f3eadf8d809b57612d7a8f9e08f1229c8`
- `/tmp/restart-expanded-reach.tsv`: SHA256 `7f1c91578019428ca97b5073c2dc518522e0fe8c15b24ebcef9cc333df17d232`

## Second code snapshot follow-up (before PathOrder)

After adding the fixed dependency-order module (verified code commit `7432df4ab`; documentation-only commit `6c0cfc15a`), the same analysis was rerun. Both exit 0:

```text
REACH: 6447 roots; 40202/83102 non-system declarations reachable
REACH: 6463 roots; 40204/83102 non-system declarations reachable
```

Profile B leaves 42,898 expression-unreached declarations; the same 19 modules above still have zero reached declarations. This is again not a deletion recommendation. Final raw outputs:
- `/tmp/restart-final-audit-reach.tsv` SHA256 `00cf66096ee150d289cba59e207082ce37f59c2c356178a978c88291534e699c`
- `/tmp/restart-final-expanded-reach.tsv` SHA256 `f19e1c0ec22330719156b395961a06bbd875093cb667fb8cf7a0d09d3c8be82f`

## Final PathOrder snapshot

Verified code `514c65248`, expanded profile B rerun after the last 5 order-independence theorems. Exact output (exit 0):

```text
REACH: 6468 roots; 40211/83109 non-system declarations reachable
```

There are 42,898 expression-unreached declarations and the same 19 zero-reached modules. The count is still not a deletion recommendation. No declaration or module was removed.

Raw TSV `/tmp/restart-last-expanded-reach.tsv`, SHA256 `c69443a947e228b1b56dc6e975b91f7707e15d7fc0e448daa168d6fe43fca781`.
