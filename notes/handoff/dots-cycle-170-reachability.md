# Cycle170 T7b read-only dependency check

Snapshot: production `8d893bdc440a3e0255cd0bb8f742ac171ed3eb42`.
No declarations, files or modules are recommended for deletion.

Used new `tools/ReachCycle170.lean`, derived from existing `Reach.lean` with
narrow imports. It traverses constant types and values, including opaque proof
bodies, but reports only declarations owned by the11cycle170modules. This is
not a whole-repository coverage or retention analysis. Roots include a Prop
statement definition explicitly as a definition, not as a proof of that target.

All three runs used Lean4.35.0 `-j1 --trust=0` with120second caps and exited0.

- Abstract target roots: `B4SkeletonV5.b4_of_bridges` and `B4TargetV5.Statement`.
  **0/295** cycle170 declarations reached.
- Concrete inherited conditional root:
  `GeneralNominalDownstreamObligations.b4_of_remaining`. **0/295** reached.
- Six cycle entry roots: `build_dictionary`, `ordinary_build`, `build_bound`,
  new `coverage_gap`, `actual_no_old_coverage`, and `stable_coverage_gap`.
  **147/295** declarations reached (private/generated declarations included).

| Module | Reached / owned declarations from six entries |
|---|---:|
| `GeneralDictionary170AssemblyPersistence` | 7 / 8 |
| `GeneralDictionary170AssemblySize` | 17 / 40 |
| `GeneralDictionary170BoundedAssembly` | 17 / 38 |
| `GeneralDictionary170NamedAccessible` | 9 / 20 |
| `GeneralDictionary170NamedCoverage` | 17 / 60 |
| `GeneralDictionary170NamedCoveragePersistence` | 8 / 12 |
| `GeneralDictionary170NamedSelection` | 0 / 5 |
| `GeneralDictionary170NamedSpine` | 19 / 32 |
| `GeneralDictionary170NamedSpineExample` | 33 / 36 |
| `GeneralDictionary170NamedSpineStable` | 20 / 20 |
| `GeneralDictionary170PathBound` | 0 / 24 |

The zero target counts are expected: those older generic/conditional entries
accept bridge obligations rather than invoking this new structural assembler.
They are a syntactic connection check, not a theorem that no semantic bridge
can exist or an alternative justification for V5 incompleteness. The eight
Remaining fields were also inspected directly: progress,execution,halted,
whereAccessible,treeExecution,canonicalLocalOrder,evidenceNode,generatedChildren.
The six inherited laws remain separate from those eight assumptions.

NamedSelection and PathBound may be absent from this chosen endpoint closure
while still providing independent coherence/depth results and regression checks.
Other root sets can reach them. Do not remove them or any old module based on
these counts. Runtime registration, documentation, test usage and future bridge
relevance are outside this expression-dependency analysis.

The first attempt at the concrete root found its cached olean absent. A focused
`lake build Yulang.GeneralNominalDownstreamObligations --wfail` then passed682jobs;
the read-only probe was rerun successfully. No existing source was changed.

Reproduce from `lean/`, with the repository's Lean executable on PATH:

```
LEAN_PATH=.lake/build/lib/lean \
YULANG_REACH_ROOTS=../notes/verification/cycle170-reach-entry-roots.txt \
YULANG_REACH_OUTPUT=/a/new/output.tsv \
lean -j1 --trust=0 ../tools/ReachCycle170.lean
```

Use target/concrete roots files for the other profiles. Exact rows, roots and
logs are preserved in notes/verification/cycle170-reach-*.
