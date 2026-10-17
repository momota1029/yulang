# NPAIR parser row-key separation sprint closeout

Sprint `npair-parser-row-key-separation-20261018`, contract revision 3,
SHA-256 `88f1136f82ae525bd0797f534062f8aaa04685c6bffbb9c0f835310e59c55c10`.
Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`.

## Outcome

- Original parent conditions resolved: **0**. The original theorem, source
  domain and quantifiers remain OPEN.
- Rev1 identified that the proof needs key separation between any earlier
  cache-seeding row and the root result row. It correctly stopped at
  `cursor::recovery::emit::emit_token_item`; no key collision or theorem was
  claimed.
- Rev2 inspected the exact recovery emitter and `Item` payload. It established
  one-time payload consumption and byte preservation, but `Token.kind` and
  `Token.text` are independent and `Item::plain`/`finish` allow empty text.
  Actual nonempty `LBracket` production remains an upstream lexical premise.
- Fresh independent compiler/source review found no BLOCKING, major or minor
  findings in the composite artifacts. It confirmed the distinction between
  synthetic empty payloads and authentic lexer reachability. Historical rev1/
  rev2 contract byte authentication remains UNVERIFIED to the reviewer; Luna's
  committed-blob comparison is primary evidence, recorded in rev3.
- The unconditional SourceNodeKey proof from the previous sprint remains
  rejected. Reusable facts are exact Eq/Hash identity, HIR key transport, and
  conditional cache-miss reasoning. The local address conclusion remains
  conditional on actual lexical row-token identity/position. No semantic `At`
  or source-qualified collision exists.
- No code or tests changed. No tests, builds, probes or compiler execution ran.
  `NO_SAFE_CODE_SLICE` remains. Full 480s envelope charged; Astra 0. All
  workers/reviewers STOPPED.

## Frozen evidence

- Rev1 parser audit: `notes/theory/2026-10-18-npair-parser-row-key-separation.md`, SHA-256 `51e756e4ae4cea61688553ee89bd1e7ec10a178d33e127c13946cf1a8189f222`; handoff `tasks/agent-loop/inbox/20261018-npair-parser-row-key-separation.md`, SHA-256 `e28f3a4f37754e285f2b0a2aa00d0ec216db2df883baf46aba8e4687f1a5fafc`.
- Rev2 recovery-token delta: `notes/theory/2026-10-18-npair-parser-recovery-token-width.md`, SHA-256 `13646ef1dcfd203dedf5fef86db796bf5a6ded9cbea148b0a42b6512ed65292b`; handoff `tasks/agent-loop/inbox/20261018-npair-parser-recovery-token-width.md`, SHA-256 `7e6d7c377faac8df8366779e74374bfc42ce3c19ffc0fa2b698d8befe31115b9`.
- Contract rev1's recorded hash was corrected from a mistaken pre-finalization value to the committed blob hash `f9e0c7476e2cd03d0d83ef7c608807b01f2cdc9e9bb1677440692556f7d24b96` in rev3. Rev2 hash: `4de607f76986b6f97e11e1fcaebca8a32cc8e46c8d2d758458ba7333301e3798`.
- Reviewer report verified rev3 `88f1136f82ae525bd0797f534062f8aaa04685c6bffbb9c0f835310e59c55c10`, both artifacts/inboxes, and direct emitter/item/parser pins. Reviewer model/effort UNKNOWN. No Git or tests by reviewer.

Relevant pushes: `c6843e694`, `4ffe60795`, `fe9e0bb76`, `b3a9b1739`, all on
`research/simple-sub-intrusion`.

## Next exact boundary

The next local address prerequisite is the authentic lexer path that forms
`current_item` and classifies the opening token as nonempty `LBracket`. The next
semantic proof work is separate and primary: draft a concrete Operation
latent-self-effect contract candidate that preserves whole alternatives and
all reference classes, then review it against the existing adopted contract.
No candidate will be silently adopted. See the next sprint contract.
