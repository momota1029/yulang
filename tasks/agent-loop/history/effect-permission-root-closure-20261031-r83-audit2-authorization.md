# R83 Lean audit 2 authorization — repaired dependency prefix

Primary authorization after adoption of amendment 01 at commit `8e9133129` (pushed) and independent amendment review PASS.

- Invocation 2 of the unchanged maximum 3; audit 1 is consumed and failed. Total execution ceiling remains 360 seconds, each invocation <=120 seconds.
- Exact input: repaired dependency prefix only, 92,550 bytes; SHA-256 `65d6e1c9ccd282bd905203da157135bd9eccf8f0cb1a22a55672c34b52caa302`. Its 78,116-byte body SHA-256 is `886990606fbe866e1e8682664883820d08cffbba2646797f63abc8a3399652d3`.
- The only assembly repair is the three namespace-local `unique` notations and deletion of the diagnosed `set_option pp.width 160` line, exactly as specified in adopted amendment 01. All 215 prefix `#check` queries remain. No R83 candidate body is included.
- Executable `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean`, SHA-256 `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`. Command `lean -j1 -M1024 --stdin`; cwd `notes/theory/lean`; `LEAN_NUM_THREADS=1`; hard timeout 120 seconds.
- Pass exact stdin directly from memory. Capture full stdout/stderr in memory and append their bytes, hashes, exit and elapsed time to the proof handoff. Create no scratch, cache, target, `.olean`, Lake output, build, test or environment.

A nonzero exit, timeout, missing declaration or error-recovered prefix closes R83 incomplete. Only prefix exit 0 allows a separately committed/pushed audit 3 authorization for the full candidate. Audit 3 is the last invocation; no further repair/retry is permitted. This authorization accepts no theorem.
