# Preparation envelope — MODULE-SUPPLIER-NATIVE-SLICES-PAGEPACK/r3

Authorized by selector disposition at sprint end of r2. Luna is the sole primary publisher and holds the only publication lease. This envelope authorizes primary-owned transport preparation and fresh independent read-only review only. No semantic/source/proof producer grant is issued.

Preserve all r1/r2 contracts, page packages, receipts and outcomes unchanged. Read only the four exact owners already pinned by r1/r2. Keep emitted pages <=4,096 bytes including headers and unique source body <=100 KiB. Preserve the accepted consumer validation behavior; the r3 copy may change only its fixed package directory.

Required repairs:

1. Trim the complete `route_internal` plus `route_internal_inner` unit to `lib.rs:18207–18230`, excluding `decode_positive_scheme`.
2. Authenticate the r1 governing contract against SHA-256 `6ab211856d460e4c31fdcadd0f4c0576444444630eb9bcd380a53e4aec7f7435` before source owner reads or staging. Authenticate all four pinned owners before staging.
3. Serialize every permitted r3 publisher with one persistent fixed lock inode `tasks/agent-loop/sprints/module-supplier-native-slices-r3-publish.lock`. Use nonblocking exclusive OS locking; hold it from destination/stage existence checks through atomic rename. Never unlink or replace the lock inode. Lock contention or existing output/stage means STOP. Only Luna may publish; any future permitted publisher must use this same inode and protocol.

Precompute and validate the complete package before private staging. Validate staged hashes/sizes/manifest before atomic rename into a fresh destination. Failed staging is not a frozen package. Use fresh versioned generator, page directory, manifest and preparation receipt.

Fresh independent nonauthor `compiler_referee` review: 150 seconds. Primary adjudication/record: 25 seconds. Total packet charge is fixed at 250 seconds: preparation 75 + review 150 + primary 25. Current cumulative charge 5,450/7,200 seconds; on completion 5,700/7,200, 1,500 remain. No contingency. No tests/builds/Cargo/Lean/Git, no source edits, no descendants except the assigned independent reviewer. Keep all semantic gates OPEN and `DELTA_AUTH_UNRESOLVED / NO_SAFE_CODE_SLICE` binding.
