# R20 amendment 01 — admit selected Call source dependencies

Base contract revision 1 SHA-256 `0b19ec601ee40765fdd1f74235d0b6f35e0c6e195a4a032672f40c7358c410f1`; base 25-file manifest SHA-256 `ebd5164460314d7b6a940e9a9caf2bbbe385c105bc8f4ff15f13e7daa9eec57d`. Both remain unchanged. This amendment adds a separately versioned dependency supplement, `call-owner-constructor-20261028-r20-dependencies-01.json`, SHA-256 `e4d8d9315e54b613f9ba03fc051cc4656e04c5419edd16458b8ebcfcb92f8102`.

The proof lane authenticated the original 25 pins and found that the exact C-Call/J-Owned labels and definitions were not in that source set. The already-pinned source-construction note points to the following primary sources. Admit these exact bytes together:

- `notes/progress/2026-10-06-source-call-generation-construction.md`, SHA-256 `6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073`;
- `notes/design/2026-10-07-complete-call-contribution-definition.md`, SHA-256 `4c83a095dce3636ada842bfc32c18cf0ef598db0e361861fb8e659745b74411e`;
- `notes/design/2026-10-08-call-source-interface-definition.md`, SHA-256 `20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c`.

This is a dependency-closure correction, not a semantic change or source-scope narrowing. Preserve all original quantifiers, the same shared source/provider/world/event tuple, independent premises, and the R20 success/falsifier criteria. The proof lane may read these three files only in addition to its original 25 pins. Do not open linked proof sources or current theory files unless a later exact amendment admits and authenticates them. If these selected source definitions leave a construction step dependent on such a source, stop there and report the exact dependency; do not use a stale or hash-mismatched theory file.

The same proof worker retains the existing two output leases and the original single 450-second total assignment budget. No elapsed or unused time is reset. Continue only within the remaining time evidenced by the R20 session; report elapsed/remaining time or UNKNOWN. No Lean, code, build, test, Cargo, formatter, Git, descendant or new output authority is added. Implementation audit, independent review, aggregate 1,500-second envelope, and all parent/production gates remain unchanged.
