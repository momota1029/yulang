# Call request/failure unwind r1 outcome

**Status: STOPPED; composition failed; no independent review or promotion.**

Contract: `call-unwind-20261025-r1.md`, SHA-256
`efeaabb27416bd9cb51066c37f8a36d13b3a4ced3eeba7f1f9488ac4ada38a2a`.
Baseline: `64d39df59`; branch `research/simple-sub-intrusion`.

## Results

- P `call_request_unwind_exists` compiled from the frozen source with exit 0,
  no timeout, and empty stderr. Candidate source SHA-256:
  `e4835bd2c2487b14d658b02373e0507ea6c201b81a1fb81d396b0f05a1850fc9`.
- Q `call_failure_unwind_exists` compiled from the frozen source with exit 0,
  no timeout, and empty stderr. Candidate source SHA-256:
  `2d7422bc4c83310a1a1d0a2bcaa5528bb6a8801520c42db2f2ada6b12224b89c`.
- The combined initial-trace module failed on invocation 3. The proof did not
  transport `resultType` and `literalSuffix` equalities from the supplied prefix
  endpoint through the destructed state. Lean reported four related type
  mismatches at lines 69–70 and 115–116. Exit code 1, no timeout, empty stderr.
- The frozen contract requires stopping on the first elaboration failure. No
  repair, fourth signature/axiom query, or independent review was run. P/Q
  remain compiled candidates pending review; the composition is not verified.

Full invocation records, command lines, source and dependency hashes, outputs,
and streams are in `inbox/20261025-call-unwind-r1-verification.jsonl`, SHA-256
`daa39582fc9455d444e6acb9daa61665b4bebfb65e53fc168d438b1b46ba273f`.
P/Q handoff hashes are respectively `4aacb47b569a1bba3df4519e1540dbedd07cc3d42f0ce255641f5cd3119a710b`
and `880f530091fce6f2994c0b69a4b6f22a91a9fd6fbba9f1ee559c14d952d37437`.
All 50 frozen contract pins were recomputed and matched before verification;
all six assigned output paths were absent at the pre-verification check.

The third invocation's source candidate is retained at
`notes/theory/lean/YulangClosure/CallUnwindTyping.lean`, SHA-256
`57afc331d735c7b9680c8b1391ced1f86b72a0ab10ca37e9f620cf0388af1cc1`.
It is an explicitly failed candidate and must not be treated as proof evidence.

## Scope boundary

No independent review occurred. This sprint establishes neither the composed
initial-trace corollaries nor acceptance of P/Q. No global progress or
reachability, source/native correspondence, cleanup correctness, original Call
A/B, inference A/B, or production conclusion follows. The viewed-delay gap and
r9 remain OPEN/UNACCEPTED. No Rust/runtime implementation was performed.

The failure is handed to the dispatcher for a fresh, separately frozen next
action. Any follow-up must use a new revision and its own exact lease, budget,
verification plan, and review; r1 has no repair authority.
