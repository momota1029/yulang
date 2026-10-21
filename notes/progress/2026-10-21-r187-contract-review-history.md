# R187 implementation-contract review history

Frozen primary-owned receipt for the successive prospective review gates. Source current-state SHA-256 before this archive: `a5443812f8064fe30ff7474c9af3a3759e7314bd409b77a183903fdae0ba6315`. This archive records resolved review outcomes; it changes no source lease or semantic authority.

- Rev1 design review: NOT CLEAN; new CLI test path lacked candidate lease; blanket preservation of prior parser expectations conflicted with adopted braced syntax.
- Rev2 bundle review: NOT CLEAN; candidate budget references and handoff/design pins disagreed.
- Rev3 bundle review: NOT CLEAN; candidate still described 2400/2160 code, omitted the new review cost, and handoff design pin was stale.
- Rev4 bundle review: NOT CLEAN; candidate full-budget sum double-counted the already charged review, handoff still granted 2160, and current lane status/next action were stale.
- Pre-write spec ruling: CLEAN for the exact delta only: remove `if x { body }` from `if_c6_keeps_non_companion_and_shallow_newline_outward`'s unconsumed cases; preserve both colon cases; add it to accepted braced `IfArm` parsing with consumed/no-error expectations. No test edit occurred.

Previously reviewed candidate/design/handoff hashes:
- Rev1: design `f94fab4f573f097dc020cd9e77612799bb376519875738f8a3a99d428e5d3f84`, handoff `1df610e5a22496d028cc555f57d33cfa9bf9e8a137a62ca10c2ec59f61e4e608`.
- Rev2: candidate `a7ce2462a78e90ea986561dae8f80fa806ea3a8d4605d42878e32869a02d6d27`, design `18e1e95677b3efc188a2af425a9c55b14a2188bfae3d042c56b3fd11eeaa54e8`.
- Rev3: candidate `3c122ffa5840cbb00f02f70ce9eda0905caaced17473bd39373f5e7456a44f51`, design `8d26548e91edcd6ee886b0c7cb2d368311e6b54b3cf68c1ac32bf8e949c0f0ad`.
- Rev4: candidate `ba1cb4334c07d3fe794b4fe64144019669428bacd9b4333c9ba49e598b822da8`, design `542fb0425f82adb247811c7c2163e34410f8c0e19d0b7d91391351f4e30b4ac9`, handoff `c9c8150deabbf25a48597a06cbcd513ccd7c3fbe2a0b1c1d6ba5e3d09ab6412d`.

All review workers stopped. No compiler/test/build/execution or external worktree access occurred.
- Rev6 worker receipt (`/root/r187_contract_review_rev6`): CLEAN for activation; 240s charged; record-only minor corrections resolved. No writes/descendants.
