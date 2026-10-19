# R97 independent compiler/source review

Reviewer: fresh `compiler_referee`, independent/read-only; primary-preserved report.

**CLEAN for the finite R97 compiler/source correspondence. No BLOCKING or major finding.**

The change adds evidence rather than repairing compiler behavior. It exercises the existing owning branches without masking preparation failures:

- `module.rs:2100–2138,3005–3068` and `local_source.rs:596–628` retain definition-owned formal IDs and authentic annotations. Loop’s `x` and ignore’s `x` remain distinct.
- `source_annotation.rs:359–440` preserves `None` versus `Some(empty_row)`. `candidate_source.rs:868–883,973–1044` and independent `runtime/program.rs:414–507` derive Value/Computation from that outer presence, without using body demand or solved effect support.
- `machine.rs:648–658,879–902` retains the whole argument label/environment and allocates inert Delay. `new_invocation:1248–1267` precedes both role branches. Value installs `ValueEntry` and executes Delay; Computation binds Delay directly (`969–1009`). `ValueEntry:1081–1099` rebinds the returned value without recursively forcing it.
- Ping’s Value payload and outward request path agree with the proof (`1011–1069,1762–1778,1935–1956`). The recursive Value cases support finite fuel exhaustion only. Closure definition classification (`program.rs:570–600`) does not execute loop merely because it exists.

All six fixtures remain present. Removing the single added test reproduces baseline SHA `8fae651ed7d14f4ed25c2aaa7d1d5fd3ba40940414a1995a42ddfcb5fe6d4815`. Existing helpers/assertions/names are byte-preserved.

Provenance is nonblocking with explicit primary adjudication. The earlier implementation handoff hash is a historical snapshot, and the final disclosure changes no test or compiler dependency. The proof also pins the pre-delta spec receipt, whose later appended review naturally changes its hash. Preserve these snapshot transitions in intake. A minor factual inconsistency remains at implementation handoff line 25 (“No … Git command”) against its explicit deviation at line 27; the closeout should treat line 27 as the correction. The disclosed read-only pre-edit status violated the assignment, but supplies no evidence of semantic corruption or Git mutation.

Verified actual SHA-256:

```text
2a9e65fd973e4d9c7f0916440fe8438eb6e9a8b8cd7969dc8f89025d9cf1b1ce contract
2619e4c8bb006e2d98cf81887091ae372cb1ae3731de76e7b707a97db577009c test
77b4ea777a2fd413b356b5128cc55362f1126e6298bcb7c310f776cfd53b4b98 proof
6a84958c082f6ec9575cb13962ad395c4246a5e7636df6921429399503eabdfb proof handoff
b6d9b8206ca433839ab48b9822f8546bf89d40099a2e8e763da1cb6d210ec39d final implementation handoff
e52fbcd82b8eb83e071ee64fc38411838229180c2ef7b9a46f889247960bbaf1 spec report
```

Every compiler/parser/runtime dependency hash in the proof table matches. Only the two disclosed evolving receipt hashes differ.

I performed read-only source/hash inspection; no files written, Git, builds, tests, compiler CLI, or descendants. Luna’s single successful run is supplied execution evidence, not a reviewer rerun. This review establishes neither method typing/dispatch nor general §21, divergence, effect soundness, original A/B, semantic adoption, production authority, or parent gate closure.
