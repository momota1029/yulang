# R76 closeout — rejected, source choice remains open

Sprint: `EFFECT-PERMISSION-SOURCE-CHOICE/20261031-R76`
Disposition: **REJECTED; fixed outcome not achieved.**

The bounded task attempted to construct the exact Internal-use plan and global formal-owner choice from complete source inventories. The Rust candidate constructor is uncompiled and cannot match the admitted source use: it equates a `DefinitionUse` Name occurrence with an `ApplySourceInput` outer Apply occurrence and returns `None` before owner selection.

Both permitted Lean stdin audits failed. Audit 1 exhausted the 1024 MiB limit in upstream R60 before R76 declarations. Audit 2 ran once on the exact 35,050-byte R3 slice and failed with source elaboration/type/syntax errors. Its axiom reports contain `sorryAx` for 10 of 14 declarations, including the key global-selection and construction-certification results. No R76 theorem is accepted, and no third audit is permitted under this packet. Full outputs remain in the proof handoff.

Independent review: **REJECT, 2 BLOCKING**. Rust occurrence mismatch and Lean proof failures are recorded in `tasks/agent-loop/inbox/effect-permission-source-choice-r76-review.md` (SHA-256 `e30bf21454cf4957f39e06d253680beafcc09442a87338c386fe828de653f70a`). The reviewed Rust origin loop itself preserves native selection order and does not prefilter Function/row; this partial positive result does not establish the fixed outcome.

No tests, Cargo, Rust compiler, Lake, build, formatter or other Lean invocation ran. No production inference path is wired to the private method. This closeout is a failed research checkpoint, not semantic approval. The worktree retains the unreviewed Rust and Lean source artifacts for a separately admitted repair sprint; they are not staged as accepted code.

Still OPEN: source/native extraction, genuine R66 `Root`, original A/B, whole-language proof obligations and production. Pending question count remains 32; unrelated UNKNOWN workers and quarantined paths are unchanged.

Frozen evidence: R76 contract SHA `87325ab223af0e98a6ca8c78162ead6ba1d72403b318342d155ee5dd55069936`; R3 manifest SHA `376de3ca8609a437853e6502ff77f386386b62d90b29f440f471eb626c1f8575`; Lean module SHA `28f5c2fc3679e3af4ef2f14bb984307fe036b4c979a3cb91f39ba0c9ebf565c3`; Rust source SHA `a5e9f3cd641f40415a6f2aa1f92fdd2cff9c031c5e64c066f8fde1f792770968`; proof handoff SHA `26a0f7ce400c18a3ee1c31046d76738f9edecaa437a35b7f3f39bb174aa9f1b1`.
