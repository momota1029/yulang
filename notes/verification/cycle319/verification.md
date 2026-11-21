# C319 verification

Lean 4.35.0 (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`).
The exact scoped targets are in `modules.txt`. These use the warmed project
cache, with every newly added source also rechecked as a source file with
`lake env lean --trust=0 -DwarningAsError=true`. The old fixture inputs were
imports, not a claim of a full clean build. The current verification does not
compile Rust, run Sat, or establish the mixed boundary's general EvidenceNode.

- Focused Lake: `cd lean; lake build $(cat …/modules.txt) --wfail`.
- Exact source: `cd lean; lake env lean --trust=0 -DwarningAsError=true Yulang/<name>.lean` for each listed target.
- Independent I-51 audits: `cd lean; lake env lean --trust=0 -DwarningAsError=true Audit/Cycle319*.lean` one file at a time. They import only `Yulang.*`.
- Scoped transitive axiom gate: unchanged body of `tools/AxiomGate.lean`, imported roots `Yulang.GeneralWherePhysicalEvidence319` and `Yulang.GeneralDeclarativeBounds319`, invoked as a standalone source at trust 0. This covers dependencies of those roots only. The scoped audit is not the unrestricted gate over the entire barrel.
- I-52 diff: `bash tools/verify-lean.sh . 85197e90c --no-build`; complete output split into numbered chunks. No full build.
- I-53: every new `lean/Yulang/*.lean` has an append-only import in the same publication. No prior files under `lean/` were removed or amended, except the authorized barrel additions.
- Partial selection experiment (before discovering I-56): an unpublished child-selection compile exited 137, was not treated as evidence, and was not added to the project. The published child proof separately has a current frame and a same-model semantic certificate, not a claim that the existing mixed resolver selected it.

Results: focused Lake exit 0 (3103 jobs, includes transitive dependencies);
30/30 new source files exit 0; 9/9 standalone audits exit 0; 273 audit entries,
including repeats; scoped gate PASS over 95,208 non-system declarations.
Diff-only verification PASS, exit 0. No nonstandard axioms.
