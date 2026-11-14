# Cycle176 verification commands and boundaries

Compiler: Lean4.35.0, all direct proof checks use `-j1 --trust=0`.
The focused cache was copied by symlinks from the prior verified cache, then a
second clean cache omitted every new176 object. Dependency traversal rebuilt
changed imported source and every new module in topological order. Each source
command had a180-second limit; the complete focused script had a900-second cap.
No root `lake build` or `tools/verify-lean.sh` was executed.

```sh
LEAN_PATH=<clean-focused-cache> lean -j1 --trust=0 -o <cache>/<module>.olean <source>.lean
LEAN_PATH=<clean-focused-cache> lean -j1 --trust=0 lean/Audit/Cycle176PublicDeclarations.lean
LEAN_PATH=<clean-focused-cache> lean -j1 --trust=0 lean/Audit/Cycle176FinalGate.lean
LEAN_PATH=<clean-focused-cache> lean -j1 --trust=0 tools/TypesCycle176Final.lean
YULANG_REACH_ROOTS=<roots.txt> YULANG_REACH_OUTPUT=<declarations.tsv> \
  LEAN_PATH=<clean-focused-cache> lean -j1 --trust=0 tools/ReachCycle176Final.lean
```

Focused new source roots:
- `Yulang.GeneralDictionaryCenteredCandidate176`
- `Yulang.GeneralDictionaryCenteredFlexible176`
- `Yulang.GeneralDictionaryCenteredFootprint176`
- `Yulang.GeneralDictionaryCenteredInhabited176`
- `Yulang.GeneralDictionaryCenteredLeafRegression176`
- `Yulang.GeneralDictionaryCenteredLedger176`
- `Yulang.GeneralDictionaryCenteredNonvacuous176`
- `Yulang.GeneralDictionaryCenteredReady176`
- `Yulang.GeneralDictionaryCenteredRecorded176`
- `Yulang.GeneralDictionaryCenteredRegression176`
- `Yulang.GeneralDictionaryCenteredRevision176`
- `Yulang.GeneralDictionaryCenteredSharedMerge176`
- `Yulang.GeneralDictionaryCenteredTree176`
- `Yulang.GeneralDictionaryHeadFootprintRegression176`
- `Yulang.GeneralDictionaryViewFootprint176`

Full stdout/stderr and separate exit-code text files are adjacent. The
clean-build-order lists the actual34 rebuilt modules. Standard axioms allowed:
propext, Classical.choice, Quot.sound. The gate traverses every new declaration's
axiom dependencies including opaque proof bodies, private/generated declarations.

Other checks: git diff --check; exact hashes of27 protected paths; all new
module root imports present; no removed/replaced old Lean lines; source hashes
of the published checkpoint match unchanged local sources. Broad substring
search matched English 'admitted', but the actual forbidden-token word-boundary
regex passed. The full verifier remains the supervisor's responsibility.

Final publication: compile GroundLeaf176 into cleanlib; run Audit/Cycle176PublicationGate.lean and Audit/Cycle176GroundLeaf.lean with lean -j1 --trust=0. All exit0. PublicationGate audits all16module319declarations; the earlier14module247 gate and112public-type record are retained unchanged.
