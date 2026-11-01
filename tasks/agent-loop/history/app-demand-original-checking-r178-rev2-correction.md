# R178 activation receipt correction

The original R178 admission receipt is byte-preserved at SHA-256 `78f547d07b4eaea77c8da996170aeb76aa0928bb4a92056fe268e79cb616cd41`. Its line reporting “strict 31-path validation” is stale: the final rev2 contract contained 32 direct paths after the R177 pin-correction input was added. Revision 2 strictly checked all 32 full-length digests with zero malformed rows or mismatches before its two lane acknowledgements.

The earlier rev1 count is withdrawn: it had 31 path entries, 30 valid matching digests and one malformed `candidate_scheme.rs` hash. Revision 3 supersedes rev2 and must validate all its direct paths before either lane resumes. This correction preserves the original admission receipt and its historical hash.
