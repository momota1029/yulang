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
