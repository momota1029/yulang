# R3 primary preflight receipt

Contract: `tasks/agent-loop/sprints/effect-permission-module-materialization-20261028-r3.md`
SHA-256: `7b608b5640caf26f076c8e5e9befeb297c5a9552f913bbb4d074a3025406b727`
Manifest: `tasks/agent-loop/sprints/effect-permission-module-materialization-r3-manifest.json`
SHA-256: `aee1a5e3c06e9c72348e45676157bdb56b57f0dc5673ddcffe58b30a8fb16f11`
Preflight script SHA-256: `7ef05dc938c7f44cbbcd08004cc5fc9b306677b58415cc4276c21330a832d133`

Runtime: `/usr/bin/python3` version `Python 3.12.3`; checksum tool `/usr/bin/sha256sum`.
Working directory: `/home/momota1029/rust/yulang`.

Executed the exact bootstrap plus manifest command in the r3 contract, replacing
only `<CONTRACT_SHA256_FROM_DISPATCH>` with the authenticated contract SHA.
Bootstrap hashes passed for the contract, manifest and script. The preflight
script validated all digest syntax, confirmed all 21 paths existed, hashed all
21 and returned `PREFLIGHT_21_ENTRIES_ALL_MATCH`. No source bodies were printed.
No tests, builds, Cargo, Lean/Lake or Git command was run.
