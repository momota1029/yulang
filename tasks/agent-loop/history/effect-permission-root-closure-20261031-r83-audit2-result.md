# R83 audit 2 result — repaired dependency prefix rejected

The separately committed authorization was pushed before invocation as
`677e77ab7`. Audit 2 was invocation 2 of the unchanged maximum of three.

- Exact stdin: 92,550 bytes, SHA-256
  `65d6e1c9ccd282bd905203da157135bd9eccf8f0cb1a22a55672c34b52caa302`.
- Pinned Lean executable SHA-256:
  `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`.
  Command: `lean -j1 -M1024 --stdin`; cwd `notes/theory/lean`;
  `LEAN_NUM_THREADS=1`; timeout 120 seconds.
- Exit 1, no timeout, elapsed 10.2 seconds. Stdout: 83,756 bytes, SHA-256
  `39b395b0a68dae8af921d6e2f93e652dfc48efe465283f88d5229177352bb3ae`.
  Stderr: 0 bytes, SHA-256
  `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- Complete stdin, stdout and stderr are retained as base64 in the proof handoff,
  whose post-receipt SHA-256 is
  `c623f7a999572cc32cadf2e48a0b7b2f7640178319973a70f64379084ebd26b7`.

The first diagnostic is at flattened stdin line 1246, column 24, corresponding
to R77's `simp [internalInputs, unique, c.plans]`. Lean reports that the
notation-expanded `unique` is a function type rather than a proposition, so it
cannot be used as a simp theorem. The associated goal remains unsolved. The
same invalid simp argument occurs in R81's three `simp [unique, ...]` calls at
source lines 146, 150 and 154. The reviewer response initially attributed these
to lines 151, 155 and 159; primary inspection of the pinned source corrected
that attribution. The independent reviewer counted eight errors overall. The
recorded output and hashes were independently checked against the retained
base64 receipt.

No R83 theorem type or axiom report appears in this prefix-only audit. No
theorem is accepted. Audit 3 is blocked because the adopted amendment and
authorization require audit 2 to exit 0 before a full-candidate invocation.
The remaining numerical invocation allowance does not authorize a retry.
