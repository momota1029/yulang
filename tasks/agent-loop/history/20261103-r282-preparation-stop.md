# R282 preparation STOP — cfg(test) source bytes rendered

R282 Luna preparation stopped immediately after a source-boundary incident.
The exact command

```sh
sed -n '1,110p' crates/yu-solver/src/candidate_intrusion.rs
sed -n '1,95p' crates/yu-solver/src/candidate_scheme.rs
sed -n '440,475p' crates/yu-solver/src/candidate_source.rs
sed -n '8350,8515p' crates/yu-solver/src/lib.rs
```

rendered `#[cfg(test)]` declarations and test-only field/branch bodies from the
first two files and the `reserve_instantiation` test-only branch in `lib.rs`.
No test assertion or test output was used as evidence. No R282 view artifacts
were frozen and no boundary reviewer, Sol owner gate, or Sol proof assignment was
launched. The pre-existing R281 view remains unchanged and its own receipt is
unaffected.

This invalidates R282 preparation admission as a source-view input. Keep R282
INCOMPLETE/STOPPED; do not proceed to a boundary or proof gate using these reads.
Conservatively charge the full 600s Luna preparation allocation. No tests,
builds, probes, Cargo, Lean, compiler edits, Git operations, descendants or
background processes occurred. Parent/A/B remains 0->0 and implementation
remains NO_SAFE_CODE_SLICE.
