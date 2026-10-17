# Observed-Apply run provenance correction

Sprint `npair-observed-apply-function-ingress-20261018`, rev2 contract SHA-256
`6792708386e9d977d8905716a2f79cc831fd5e37ad8f5e1d1b683919ddf8d0c8`.
This correction supersedes any wording in the frozen source-evidence note or
handoff that treats the reported run as independently reconstructed execution
evidence.

## Review finding and primary disposition

The rev2 contract required a frozen hash of the strict endpoint/scope/Replay
query and a clean independent review **before** the single Cargo command. The
command was run before that gate. The stricter query edits were made afterward,
and the run-time harness snapshot/hash was not captured. The implementation
review therefore could not compare the historical output to exact executed
source bytes. This is a major contract-order deviation.

The single run is retained as a **provisional, author-reported observation**:
the worker reports exit 0, a 1.60-second Cargo dev build, `received` LocalSource
with Apply occurrence 18, a matching source_call occurrence with `receive` and
`f0` operands, native call endpoints, and no candidate conflicts. These facts
are useful leads but are not independently authenticated against an executed
source snapshot. They do not establish exact typed-endpoint/scope correlation,
Replay, `s1 -> D`, the original contribution premise or parent closure.

The current research example hash
`5525939261a25548f5694c06cef330dcf4e53079b6d5377b0a3cd87d4e2b8d12` identifies
later, unexecuted query edits. Independent compiler review found those current
query checks consistent with the pinned APIs and found no additional source
selection overclaim; that review does not convert the later code or the
historical run into executed evidence. The fixture is restored to its exact
baseline SHA-256
`969e20e0f38a2c341a96ff4fe07028bf567ca134e0fb24602fadf6e4c723d9c0`.

The primary accepts the run only at this provisional, author-reported scope and
rejects promotion of the unexecuted query as a verified implementation.
No second invocation is authorized in this sprint: implementation packet
elapsed time and remaining cap are UNKNOWN, and the exact contract condition
for a rev3 run is therefore unmet. No additional tests, builds, probes or
semantic changes are made here.

## Parent and next evidence

Original parent conditions closed: **0**. The separately reviewed proof
artifact establishes source constructor laws and the successful-path port map
`q_D^r = phi_r(rep(q_D))`, but original same-`w` `eta`, dependent
Permission/use transport `T_rho`, observed Replay records, N-Transport, H0,
F1/FK1, soundness, principality, termination and parent closure remain OPEN.

The next source experiment requires a new exact contract, a frozen query hash,
independent pre-run review, verified runtime allocation, and an explicit
single-run budget. It must query the exact `received` source occurrence,
operands, typed endpoints and definition scope; any Replay must be tied to that
same call with both ordered BoundKeys and relation fibers. A future run may not
be inferred from this provisional receipt.
