# Reproduction and boundary checks

Run commands from repository root with Lean4.35.0 toolchain at ../toolchain244/bin.
- `python notes/verification/cycle259/check-sources.py`: validates inherited source hashes, new import closure, freeze and forbidden tokens. Requires baseline git objects and prior verification records.
- `python notes/verification/cycle259/rebuild-final-critical.py`: builds63 non-prior-closure mathematical modules into cycle259-final-critical, reusing source-hash-verified existing artifacts for all other imports.
- `python notes/verification/cycle259/run-final-audits.py`: after successful fresh-build marker, exposes focused artifacts to lake and executes six standalone audits, then both independent probe files. The closure hash includes both probes' imports, but the probes are standalone proofs rather than imported Yulang mathematical modules.
- `python notes/verification/cycle259/make-japanese-guide.py`:185 mathematical declarations with module-level Japanese quantifiers/assumptions, plus separately maintained probe guide.

Output logs with failed intermediate proof elaborations are not used as success evidence. The final proof files contain neither sorry nor custom axioms, and their strict exit0 outputs print only standard axioms. Whole repository verification remains out of scope.

The main Full audit covers291 definitions, theorems, structures and generated/private declarations under the28 new namespaces. Probe proof axioms are audited explicitly (three proofs per file); their three helper definitions are ordinary executable constructions with no custom assumptions.

Final selected roots include actual certificates/public projections, both finite run regressions, generic completion/step-budget/quiescence, unsupported checking and fixed-batch results.151 of185 explicit main declarations are transitively used by28 selected roots. This is dependency reachability for these selected statements, not a claim that all project theorems depend on them or that every separate regression must lie on a single final proof path.
