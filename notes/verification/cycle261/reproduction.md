# cycle261 focused verification

Lean 4.35.0. From repository root, with the prior cycle260 focused cache retained:

```sh
python3 notes/verification/cycle261/build-dependencies.py
python3 notes/verification/cycle261/build-pool-dependencies.py
python3 notes/verification/cycle261/make-audit.py
python3 notes/verification/cycle261/prepare-final.py
python3 notes/verification/cycle261/check-sources.py
python3 notes/verification/cycle261/rebuild-final-critical.py
python3 notes/verification/cycle261/run-final-audits.py
python3 notes/verification/cycle261/make-japanese-guide.py
python3 notes/verification/cycle261/alias-closure-prototype.py
```

The scripts use `../toolchain244/bin/lean`; adapt only that toolchain location when reproducing.
`rebuild-final-critical.py` rebuilds every Yulang module in the current dependency closure absent
from cycle260's verified source-hash manifest, topologically, in a separate critical cache.
Other dependencies reuse artifacts with unchanged source hashes. This is not a clean build of
the entire repository. `final-critical-modules.txt` identifies the exact fresh layer.

`run-final-audits.py` exposes that fresh layer in the local lake library path and invokes each
of Complete, Full, Usage, Types, AllTypes and Reach separately using
`lake env lean --trust=0 -DwarningAsError=true Audit/Cycle261<Name>.lean`.
None of these Audit files import another Audit file. The independent CandidateBoundaryProbe
is then compiled against the same fresh cache. The Python alias experiment is not Lean proof.

Full checks generated/private declarations as well as explicitly named functions/theorems.
Complete and AllTypes enumerate the explicitly written theorem/def/abbrev declarations.
The Trace/Failure inductive types and generated recursors are included by Full.
Reach is a selected-final-interface dependency analysis, not a claim that all declarations
are used by one completed language theorem. Remaining helpers are printed, not deleted.

No whole-repository `lake build`, `verify-lean.sh`, or Yulang2 runtime invocation was performed.
