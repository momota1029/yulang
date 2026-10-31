# R87 corrected admission — amendment 01

Sprint: `NATIVE-DRAIN-READER-CORRESPONDENCE/20261031-R87`
Contract SHA-256: `2ec7f33760b4ef8cdb3ac434dcf415f473a2019f4acf87c25786f77e0fc81261`
Corrected input manifest: `tasks/agent-loop/sprints/native-drain-reader-correspondence-20261031-r87-inputs-r2.json`
Corrected manifest SHA-256: `e3d1b0590ea1fb179cc89039665b04d0d4d9bd2ec6a63290df4f90011fe2be96`
Baseline: `9931800b1aed04402049a0e7685630f24b9e5e56`.
Amendment: `tasks/agent-loop/history/native-drain-reader-correspondence-20261031-r87-amendment-01.md` SHA-256 `d6d4718bedc3b66f0f728afe7eb12e129b01d1fe2a2c1f687ea2cec23983ef20`.

The earlier manifest/admission pin is superseded due solely to a stale hash
computed before whitespace cleanup. Proof and source lanes stopped before
writing any artifact or executing Lean; the source lane's initial hash/symbol
inventory stayed within its two exact source inputs. The original R87 scope,
leases, budget, execution gate, and no-environment constraint are unchanged.

Re-admitted envelope: 3,600 seconds total; proof 1,400; source proposal 1,000;
independent review 700; primary 500; Astra 0. Candidate preparation remains
separate from execution. No Lean execution is authorized until the exact frozen
candidate/input receives fresh independent review and a separately
committed-and-pushed authorization. Luna retains all state and Git duties.
