# R272 pin-count erratum

R272 rev1 bytes remain frozen. Its handoff's statement that 307 distinct
inherited/direct path-hash pins matched is withdrawn as unsupported by the
retained path enumeration. The independent R272 review authenticated 303
distinct explicit paths after deduplication; the four further paths needed to
substantiate 307 were not identified. No source-byte mismatch was found in the
303-path set, and this count gap establishes no compiler defect. The exact
review finding and limitations remain in
`tasks/agent-loop/history/20261102-r272-source-actual-pair-review.md`.

For R273, Luna independently extracted the exact source rows from three
previously authenticated manifest tables: the 139-row R271-r2 local manifest,
the 68-row R271-r3 cached external manifest, and the 36-row R255 source
manifest. These comprise 243 rows and 229 distinct paths after deduplication;
all hashes matched at extraction. The complete path/hash/origin list is
`tasks/agent-loop/sprints/source-successful-consumer-r273-inputs.json`, SHA-256
`42040552635bb7c2652eb0bad68cb46295078d03ae70620b7edd555d3883fa5f`. This is
the exact technical source scope for the next packet. The unsupported 307 count
does not authorize extra dependencies or paths.

No R272 producer output, semantics, source scope or parent claim is rewritten.
R272 remains INCOMPLETE, with conditional local native evidence only, parent
delta 0→0, `Need_D` and R71 open, and `NO_SAFE_CODE_SLICE`.
