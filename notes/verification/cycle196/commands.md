# Cycle196 verification commands

Toolchain Lean4.35.0, cached local183 package. All commands from lean/ with cached toolchain PATH.

- `timeout 180 lake build Yulang.GeneralNominalViewExample196 Yulang.GeneralNominalViewRefresh196 --wfail`: exit0,1131jobs.
- `timeout 180 lake env lean --trust=0 -DwarningAsError=true Audit/Cycle196Transport.lean`: exit0.
- Same strict command for Cycle196PublicTypes and Cycle196KernelGate: exit0, gate66declarations.
- `timeout 180 lake build Yulang.GeneralNominalExecutableView196 --wfail`: exit0,1139jobs.
- Strict Audit/Cycle196Executable.lean: exit0.
- Final `timeout 180 lake build Yulang.GeneralNominalExecutableView196 Yulang.GeneralNominalRootedViewExample196 --wfail`: exit0,1142jobs.
- Strict Cycle196Rooted, Cycle196RootedExample, Cycle196FinalGate: exit0, final110declarations.
- Each of all7 new source modules directly checked with `timeout 120 lake env lean --trust=0 -DwarningAsError=true Yulang/<module>.lean`; results in strict-sources.log.
- `bash tools/verify-lean.sh . origin/integration/m1-final --no-build`: exit0, PASS (diff checks only),6 REVIEW items for audit run_cmd; see final-diff-only.log and report. No full build.

Worker exploratory elaboration failed before the verified final sources: dependent slot numerals, definition transparency and example projections were corrected. One initial coordinator diff check found fresh integration no longer an ancestor after concurrent owner commits; new integration was merged preserving its files, then the final diff check rerun. No prior Lean declaration was weakened.
Full repository build, all historical audits, full build verifier, hostedCI, and Yulang2 runtime were not run. These focused passes are not a whole-system certificate.
