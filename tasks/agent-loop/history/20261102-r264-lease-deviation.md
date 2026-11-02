# R264 source-read lease deviation — 2026-11-02

Producer `/root/sol_r264_required_lineage_288aae38a`, contract
`tasks/agent-loop/sprints/required-lineage-coverage-r264.md` SHA-256
`c8fa42e8721ec357922b081c660261defe60f52fc83791c8a141e775a8934ee7`, reported
that one `rg` search used the broad pattern
`crates/yu-solver/src/candidate_*.rs`. Its result included two matching lines
from unpinned `crates/yu-solver/src/candidate_context_tests.rs` (reported at
lines 4163 and 4169). The worker said it did not open the file or use those
matches as evidence and narrowed later searches to exact permitted paths. This
is still a source-read scope deviation under the fixed 36-path manifest.

Luna sent STOP and interrupted the active worker. The interruption tool
reported its prior status as RUNNING; the live roster now reports interrupted.
No cessation acknowledgement was available at reconciliation. Therefore the
worker is **UNKNOWN**, not STOPPED. Whether it wrote any bytes to either exact
R264 output after its last progress receipt is also UNKNOWN. No output file was
opened or hashed during this reconciliation. Keep both exact R264 output paths
QUARANTINED under their existing owner, retain the full 2,400-second
reservation, and do not read, write, transfer or reclaim them without an
actual stop receipt and fresh adjudication of the deviation.

The admission receipt retains the contract, baseline, source gate and
unmodified goal. No result from this trial is admitted; no source
counterexample, compiler defect or production authorization is claimed. R263's
separate UNKNOWN/quarantined paths remain unchanged. No capacity override or
path release occurred.
