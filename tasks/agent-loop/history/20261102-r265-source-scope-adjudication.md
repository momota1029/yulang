# R265 source-scope stop and Luna adjudication — 2026-11-02

R265 worker `/root/sol_r265_consumer_lineage_51dd6af` reported that an exact
read of the pinned `crates/yu-solver/src/candidate_context.rs` range
4640–4795 showed literal `#[path]` declarations naming the unpinned test files
`candidate_context_tests.rs` and `candidate_native_inventory_tests.rs`. The
worker reports that neither file was opened/read, no broad search was used,
and no unpinned source body was read or used. Its pre-read R255 gate matched
36/36 pins. The only source observation is from the authorized pinned file.

Luna adjudicates that seeing literal path strings inside an authorized pinned
file is not exposure or reading of the referenced unpinned files and does not
violate R265's exact-path source authority. No theorem or source/native result
follows from this observation. The worker had already stopped source reads and
was interrupted while Luna reconciled the interpretation. The interruption
tool returned prior status RUNNING; no cessation or output-write receipt is
yet available. Therefore the worker is UNKNOWN and both exact output leases
remain QUARANTINED until a fresh explicit receipt establishes the prior
session's cessation and output status. No output path has been opened or
hashed by Luna.

Any same-contract resumption must revalidate exact authority/dependency hashes
and the 36/36 source pins, use a fresh actual session receipt, continue within
the original 1,200-second grant (no reset/extension), and read only exact
manifest paths. Literal path declarations in pinned files do not authorize
opening or searching the referenced files.
