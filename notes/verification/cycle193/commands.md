# Cycle193 commands and exits

All commands from lean/ unless otherwise indicated; Lean4.35.0 cached toolchain.
- `timeout 180 lake build --wfail Yulang.GeneralNominalNonleafInstallation193`: exit124; checkpoint.log.
- Direct Installation193 `lake env lean --trust=0 -DwarningAsError=true ...`: exit0; installation-strict.log (empty).
- Plan193/Local193 same command: both exit0; plan-local-strict.log.
- `lake env lean --trust=0 -DwarningAsError=true Audit/Cycle193Checkpoint.lean`: exit0; public-types.log.
- `lake env lean --trust=0 -DwarningAsError=true Audit/Cycle193Gate.lean`: exit0; gate.log,69 declarations.
- `timeout 150 lake build --wfail Yulang.GeneralNominalNonleafReuse193`: exit0; final-focused.log.
- Each of7 `GeneralNominalNonleaf*193.lean`, `timeout 90 lake env lean --trust=0 -DwarningAsError=true <path>`: exit0 each; final-strict.log.
- `timeout 90 lake env lean --trust=0 -DwarningAsError=true Audit/Cycle193FinalTypes.lean`: exit0; final-public-types.log.
- `timeout 90 lake env lean --trust=0 -DwarningAsError=true Audit/Cycle193FinalGate.lean`: exit0; final-gate.log,148 declarations.
- From repo root `bash tools/verify-lean.sh . e7003de4cf4735c7211047ec38ba016455c11a8e --no-build`: exit0; diff-only.log(full stdout).

The source worker also strict-checked all7. Coordinator reran all7 independently.
This is one shared cache, not an independent clean-machine build. Focused1114jobs
counts include cached dependency jobs, not a full repository build. No full verification.
