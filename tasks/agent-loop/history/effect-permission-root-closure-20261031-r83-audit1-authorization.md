# R83 Lean audit 1 authorization

Primary authorization under the admitted R83 contract, after independent frozen-artifact review PASS and exact in-memory reconstruction. This authorizes one invocation of the dependency-prefix input only.

- Input: 92,456 bytes; SHA-256 `c42cc473b7a1629cedb796b30dae79bfcc41a597e5ca8e5afce4136183bd4146`.
- Prefix body: 77,998 bytes; SHA-256 `dafe89f3daf16a96122d0c840ece5a18fa9837dac85f9d40db8261bb7795186a`.
- Construction: exact 220 source declarations from the ten pinned modules, `import Std`, original namespaces/opens/contexts, then the 215-name prefix query list. Source slices and module hashes were independently verified.
- Executable: `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean`; SHA-256 `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`.
- Command: `lean -j1 -M1024 --stdin`; cwd `notes/theory/lean`; environment `LEAN_NUM_THREADS=1`; hard timeout 120 seconds.
- Input is passed directly from memory; stdout/stderr are captured in memory and their complete byte streams, hashes, exit status and elapsed time will be recorded. No scratch, cache, target, `.olean`, Lake, compiler build, or environment.

Invocation budget: audit 1 of at most 3; per-invocation limit 120 seconds, total limit 360 seconds. A nonzero exit or missing required declaration stops this packet incomplete; no theorem is accepted from error recovery. This record authorizes no candidate audit: audit 2 requires a separately pushed authorization and only follows prefix exit 0.
