# cycle260 focused reproduction

All commands run in the repository root unless `cd lean` is shown. Lean 4.35.0.

1. Build the 27 modules in `modules.txt` dependency order with the compatible
   focused cache, `lean --trust=0 -DwarningAsError=true -o <cache>/Yulang/<M>.olean lean/Yulang/<M>.lean`.
2. `python3 notes/verification/cycle260/make-audit.py`
3. `python3 notes/verification/cycle260/prepare-final.py`
4. `python3 notes/verification/cycle260/check-sources.py`
5. `python3 notes/verification/cycle260/rebuild-final-critical.py`
   Fresh-builds all Yulang modules in this import closure not present in the
   cycle259 closure. It reuses the older cache only after source hash checks.
6. `python3 notes/verification/cycle260/run-final-audits.py`
   Exposes fresh focused artifacts and runs Complete, Full, Usage, Types,
   AllTypes, Reach separately with `cd lean && lake env lean --trust=0
   -DwarningAsError=true Audit/Cycle260<Name>.lean`. No Audit imports Audit.
   Then strictly checks the standalone RequestAddressProbe.
7. `python3 notes/verification/cycle260/make-japanese-guide.py`

These scripts refer to the existing local toolchain and compatible cache paths.
They are not a clean-checkout or whole-repository build claim. Missing caches
must be supplied or the actual dependency closure rebuilt first. The initial
inherited focused cache was from cycle259 and old source hashes were checked.
The final critical layer is rebuilt afresh; exact modules and all command
results are listed alongside this document. `verify-lean.sh`, whole `lake build`,
and Yulang2 runtime were not run.

Only propext, Classical.choice and Quot.sound are allowed by Full. The main
library modules contain no sorry/admit/new axiom/native_decide. Reach reports
unreached helpers honestly; it is not a claim that every declaration is used by
one end-to-end language theorem.
