Review receipt — MODULE-SUPPLIER-NATIVE-SLICES-PAGEPACK-REVIEW/r2

Disposition: REJECT; read-only review STOPPED. No supplier/source/native/production conclusion.

Findings:

- major — unit boundary mislabeling: `module-supplier-native-slices-r2-pagegen.py:28`, manifest range `route_internal and route_internal_inner`, and `page-010.txt`. Both named functions close at `lib.rs:18210` and `18230`; the range continues through `18236`, including the incomplete declaration of unrelated `decode_positive_scheme` at `18232–18236`, while claiming `kind=unit`, `complete_unit=true`. This violates the complete exact named-unit boundary requirement. Close by trimming the range to `18230` and regenerating/re-pinning, or explicitly authorizing and labeling the added fragment.
- major — governing contract pin is asserted, never authenticated: generator lines `12–13`, `46–52`, `81–83`. Only four owner hashes are checked before staging; the contract path/hash are copied into the manifest without reading/verifying the contract. A missing or changed contract would still permit publication bearing its stale claimed digest. Close with an actual contract hash check before owner/body processing and staging.
- major — publication does not atomically enforce freshness: generator lines `99–100`. `OUT.exists()` followed by `os.rename(STAGE, OUT)` leaves a race: an empty destination directory appearing between these operations can be replaced on Linux. This violates fresh-destination preservation. Close with an atomic no-replace publication primitive, or an enforced exclusive publication protocol.

Authenticated independently: review contract SHA `b001533ccf8264ed16020a6124437264e2720e1d9aa72705d9d8f84dc0652b62`; all five contract-listed artifact pins; all four full-owner SHA pins. Preparation explanation was not used as evidence.

All 18 page hashes, emitted/body sizes, exact headers, owner pins, byte offsets and line spans passed. All 14 declared ranges reconstructed byte-for-byte, with correct continuation, no overlaps/gaps/substitution within each range, and aggregate body coverage 32,185 bytes. Three designated `lib.rs` context ranges are explicitly `context_fragment`, with `complete_unit=false`. Other named units have matching closing boundaries; Name arm closes at `1807`; `instantiate_candidate_graph` includes closing brace at `4800`; `definition_use` includes its documentation and full declaration beginning at `3232`.

Generator owner/range/overlap/page/aggregate checks precede staging; staged page bytes/hashes/sizes and manifest are validated before publication. Consumer checks basename, unique manifest membership, regular page file, size/cap, hash, exact header and body length before writing stdout.

Largest page was executed using the prescribed consumer, `page-014.txt`, with 8,192 output tokens, exit 0, untruncated. Exact stdout 3,779 bytes, SHA-256 `40ab089138446edbada37f87e8e609f8e6eea65b80f82a1162276391544ca502`, ending `b'            retained: retained_maps,\n        });\n'`; stderr empty.

Deviation: initial verification invocation used unavailable `python` (exit 127); reran successfully with `python3`. No writes, tests/builds, Cargo/Lean/Git, descendants or background work. Only admitted slices were inspected; full owners were read for hashes/byte indexing without tail interpretation. Measured elapsed lower bound 95 seconds (`04:44:09–04:45:44 UTC`), startup unmeasured/unknown; full 150-second grant remains charged.
