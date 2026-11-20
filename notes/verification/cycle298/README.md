# Cycle 298 verification

`theorem-index.md` gives the exact names and signatures indexed from the added modules. The eleven independent files in `lean/Audit/Cycle298*.lean` print their names and axioms; the corresponding checked outputs live here. `verify-focused.sh` compiles the new import tail against a prior Lean 4.35.0 cache in an isolated scratch directory, checks the audits with trust 0, reruns selected old audits, and compares four executable Lean fixture outputs byte-for-byte. This is not a clean full-repository Lake/CI run. No Rust code was modified or executed.

The symbolic duplicate is synthetic. The C252/C271 refresh/install and C277 generated install child are actual existing Lean-model executions. The row-sensitive C287 example is a symbolic-source/typing fixture in its own scope, not a reachable B4-ground-initialization claim. The finite windows are not raw path enumeration algorithms; finiteness concerns the available targets, not raw path lengths or type/row carriers.

- `focused-verification.txt`: isolated Lean build and audits; source SHA-256s identify the inputs directly, regardless of later documentation commits.
- `direct-verification.txt`: normal Lake-environment replay of all eleven new audits and four tests, with all 52 source digests checked.
- `static/diff-00.txt` through `diff-04.txt`: concatenate in order for the byte-complete `verify-lean.sh --no-build` output. The comparison to integration uses a disposable, check-only commit over the exact upstream tree.
