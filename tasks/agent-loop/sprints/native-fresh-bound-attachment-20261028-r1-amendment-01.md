# Amendment 01 — correct the Lean README pin

Parent packet: `NATIVE-FRESH-BOUND-ATTACHMENT/r1`.
Base contract SHA-256: `fd040b8a5a1702b54c06c44fa88a8316433dc950a62d453de48db3f73e2e6e2c`.

This amendment corrects one malformed SHA-256 in the `Lean 4.35.0 and theorem/authority pins` list. The admitted `notes/theory/lean/README.md` pin is:

```text
8d27e0b90fc04eb8a0a30606a857e564e5269e8e33e72fddbf1190cb6a7072e3
```

The base contract accidentally omitted the `0` after `fc`, yielding a 63-hex-character value. This amendment changes no path, owner, source domain, theorem, semantic authority, output lease, resource cap, verification gate, or success predicate. All other pins remain unchanged.

The proof producer reported the malformed pin after its original ACK. It then corrected its initial account: the startup included reading the README body and a later line range before the pin discrepancy was noticed. It reports that no theorem construction relied on README content. This is a non-waivable ACK/pin-order deviation under the base contract. Therefore the proof output may continue only as provisional research under the same exact lease and grant; this sprint's fixed outcome cannot be accepted or promoted. The deviation must remain in the handoff and independent review. No checks are authorized. The producer paused further reads/construction; it may resume only after this amendment and its hash are recorded in `current.json` and the producer ACKs the exact amendment. Existing output leases and grants remain unchanged.
