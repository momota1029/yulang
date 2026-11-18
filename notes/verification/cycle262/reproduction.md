# cycle262 focused reproduction

Lean4.35.0. From repository root:

```sh
python3 notes/verification/cycle262/make-audits.py
python3 notes/verification/cycle262/rebuild-focused.py
python3 notes/verification/cycle262/run-audits.py
```

Toolchain path is ../toolchain244/bin. Fresh layer selected by comparing every
transitive Yulang source SHA256 to cycle261 dependency-source-sha256.json; changed
frozen dependencies are rejected. New/previously unverified dependency modules are
recompiled topologically. Other unchanged dependency artifacts are reused. This is
not a full clean repository build. Each Audit file is invoked separately via
lake env lean --trust=0 -DwarningAsError=true; no Audit imports another Audit.

Independent frontier review rebuilt five selected modules in a separate cache; its
exact hashes/logs are stored alongside rebuild-frontier-review.py. Kernel regression
probes use ordinary Lean proofs, not native computation. Yulang2 runtime not invoked.

Final pass includes eleven standalone Audit files, including OwnerProbe and NormalizedProbe. The seven
OwnerProbe theorems are experimental local owner-address separation, not part of
the 28 production modules or their 205 explicit /412 full declaration count.
`make-reach.py` regenerates the selected-root reachability audit. Its 37 roots
reach174/205 explicit declarations; the remaining31 are not asserted to be dead code.
The first ten-audit run was19:15:52–19:16:15 UTC, exit0.
OwnerProbe was extended with table-size and combined-interpretation results,
then NormalizedProbe added two support-scoped cross-Plan body results.
All eleven audits were rerun; exact times are in final-audit-run.txt.

Independent rebuilds cover22 distinct production modules: frontier5, dynamic3,
observed/planned2, selected5, failure/unused2, semantic/safety5. The source-pool
modules received independent source review but not a second fresh rebuild; other
modules are covered by the primary45-module rebuild and all-declaration audits.
The final dependency-source manifest covers1728 Yulang source files; all hashes
were checked unchanged after the final audit. No assertion of full repository
clean-build, global compiler completion, runtime performance or satisfiability
is justified by these checks.
