# R80 exact Lean audit 1 authorization

Primary authorization committed and pushed before execution. Sprint: `EFFECT-PERMISSION-SOURCE-INCIDENCE/20261031-R80`. Candidate revision 1 is frozen; only the primary may run this one direct stdin audit. It will not write source, build, cache, target, scratch or project artifacts.

Exact input: 100,504 bytes, SHA-256 `d67576cf54949582d25432adac6fc01df67c4455c931f79d4b925c1909b0ba2d`. Luna reconstructed the input from the proof handoff's explicit ordered slices and strings, verified every complete-source and slice hash, then matched this complete input size/hash. The eight queries are the exact theorem names listed in that manifest. Candidate module SHA-256 `2346aee86469d1ba4ffb6ca79837cafc78ba5159a79f32a03d1b6e02cfcd3379`; proof handoff SHA-256 before execution `1357135d4b470cd6aa981e6beb27b4e79df777831123fd30a1b3d177f54bf0b0`.

Pinned command and boundary: `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean -j1 -M1024 --stdin`, cwd `notes/theory/lean`, `LEAN_NUM_THREADS=1`, wall limit 120 seconds. The toolchain file says Lean 4.35.0 and the executable SHA-256 is `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`. Input and output remain in process memory; the exact input, complete stdout/stderr, exit and elapsed time will be recorded in the assigned proof handoff. No retry is authorized by this record.

This audit can establish only the exact flattened declarations and printed type/axiom results. It does not establish Lake import closure, Rust compilation/runtime, authenticated Rust-to-Lean extraction, R66 Root, original A/B, whole-language soundness, principality, termination or production.
