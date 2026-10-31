# R87 amendment 01 — correct frozen contract hash and baseline

Sprint: `NATIVE-DRAIN-READER-CORRESPONDENCE/20261031-R87`

The committed contract is unchanged at `tasks/agent-loop/sprints/native-drain-reader-correspondence-20261031-r87.md` and its exact SHA-256 is
`2ec7f33760b4ef8cdb3ac434dcf415f473a2019f4acf87c25786f77e0fc81261`. Amendment 01 corrects the earlier manifest's stale contract
hash, which had been calculated before trailing-whitespace cleanup. No semantic
contract content changed.

- Superseded manifest: `tasks/agent-loop/sprints/native-drain-reader-correspondence-20261031-r87-inputs.json` SHA-256
  `c96e2ada0461e0ed5527af4c4d96e697034aa9428420f56c10b6d489825409f4`.
- Corrected manifest: `tasks/agent-loop/sprints/native-drain-reader-correspondence-20261031-r87-inputs-r2.json` SHA-256 `e3d1b0590ea1fb179cc89039665b04d0d4d9bd2ec6a63290df4f90011fe2be96`.
- Exact baseline/admission commit: `9931800b1aed04402049a0e7685630f24b9e5e56`.
- Contract SHA-256: `2ec7f33760b4ef8cdb3ac434dcf415f473a2019f4acf87c25786f77e0fc81261`.

The source lane read only the two pinned source files for hash/symbol inventory
and stopped at the mismatch; it wrote no report. The proof lane read only the
contract and manifest and paused before creating a candidate. No Lean call,
source edit, build, test, cache, target, scratch, or environment was created.
Both lanes acknowledged WRITES STOPPED before this correction. Amendment 01
supersedes the prior manifest pin and re-admits the same exact leases and
budgets.
