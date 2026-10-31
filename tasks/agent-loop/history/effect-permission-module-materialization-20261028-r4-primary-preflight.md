# R4 primary preflight receipt

At the repository root, the primary ran the exact bootstrap command pinned in
the r4 grant. `/usr/bin/sha256sum -c` authenticated the r4 contract, the
21-entry manifest and preflight script, and the r3 outcome plus both frozen r3
STOP receipts. It exited 0. `/usr/bin/python3` then ran the pinned preflight
against the manifest and exited 0 with `PREFLIGHT_21_ENTRIES_ALL_MATCH`.

Contract SHA-256:
`12d99e885af99a669007921e3ebc782b990c443781a9b6549962c12abd2f490f`.
No semantic source body was inspected as part of this authentication receipt.
