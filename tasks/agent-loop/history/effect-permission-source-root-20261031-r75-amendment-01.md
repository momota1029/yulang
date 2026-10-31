# R75 amendment 01 — pin transitive Lean source and authorize one repair audit

Sprint: `EFFECT-PERMISSION-SOURCE-ROOT/20261031-R75`.

- Contract remains frozen at revision 1, SHA-256 `bbeb3cc4bf26a8fe29b2144dc086e6e0efa6bd7c0f9d2ec5ab8aeab8401db3fb`.
- Replaces the incomplete input manifest r1 with r2:
  `tasks/agent-loop/sprints/effect-permission-source-root-20261031-r75-inputs-r2.json`
- Manifest r2 SHA-256: `518ff1313ecc5c837c5fd97bd958ad879ddf585b18e3783c915b695cef916db6`.
- R39 transitive source SHA-256: `748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e`.

## First audit disposition

The proof worker invoked the single audit allowed by the original contract
before Luna's message to pause arrived. It flattened R39/R45/R47 and R75. The
R39 bytes had been measured before invocation, but R39 was not in manifest r1.
This is a recorded pinning deviation; no later document retroactively changes
the order. First stdin SHA-256 was
`dff3f4dd94d00e90ca2bdc6658ca423fb3d14f635d5c9c4cb762181b7d98d3a0`; the run
exited 1 after 6.625 seconds. Six general theorems checked with only `propext`
and `Quot.sound`. The finite fixture failed typeclass synthesis; Lean recovery
introduced `sorryAx` for those failed declarations. The fixture is rejected,
and the first run does not pass the packet. The proof handoff must retain the
full command, diagnostics, declaration inventory and axiom report.

## One amended audit authorization

Luna authorizes exactly one repair audit, after this amendment is committed and
the proof writer confirms the candidate bytes still match all pins below:

- Exact stdin SHA-256: `8b3b30ed3a8333573aa5a78b923819491be56456f7d0e958085a4f0ec119d91c`
- Exact stdin size: `64305` bytes.
- Command: `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean -j1 -M1024 --stdin`
- Executable SHA-256: `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`.
- Flattened inputs in order: R39 `748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e`; R45 `9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f`; R47 `d64c54f7c977e110305a76e6437fc87c8ff14201a4d69eb0bbcb5ee0e1cd8b9c`; R75 module `e868eb6bc6cba74af4f3096cc7fb2e48503c8183e064071b84022923c2bc6821`.
- Resource cap: 120 seconds, Lean memory flag M1024, one process, no retry.
- Output: stdout/stderr retained in the handoff; record their hashes, exit and
  full theorem types/axiom reports. Emit no `.olean`, `.ilean`, cache, or other
  file.

No third audit is authorized. If the exact candidate or executable differs,
stop without invoking Lean. The source/native and genuine R66 Root gaps remain
open regardless of this finite theorem's result.
