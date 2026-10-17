# Lexer bracket identity: frozen rev1 handoff

Worker: /root/npair_lexer_bracket_identity. State: STOPPED; writes ended at this
submission before frozen review. Sprint npair-operation-contract-and-lexer-identity-20261018
rev1; baseline b3a9b1739b59d8c7991b5f798e98f71f96904b19.

Objective/method: bounded static source trace of authentic LBracket production,
current_item transport and canonical/Error emission. Claim class: source facts
plus conditional lexical lemma, not authentic-parser closure or key injectivity.

Result: scan_punctuation chooses LBracket only after next() returns '[';
assuming real-source next/with_str and transaction semantics, the payload is
exactly one byte "[". current_item and Item wrappers retain it. Canonical
emission retains LBracket kind; raw Error recovery retains bytes and emits
Error kind. Generic crate-visible Token fields permit empty text without
establishing parser reachability. No actual counterexample or execution claim.

Parent application: closure0. Positive bracket width alone does not establish
distinct BracketRow starts/keys for earlier cache-seeding rows versus the root
result row. Missing owner evidence is LexIn::next/with_str/transactions and the
BracketRow/Type parser callback wiring, node-start placement and unique opening
bracket ownership, composed with the primary's reviewed key transport. Primary
explicitly confirmed this boundary and prohibited further owner reads in rev1.

Frozen artifact:
`notes/theory/2026-10-18-npair-lexer-bracket-identity.md`
SHA-256 `7e6b99f764ffc32f1bab3935a1035be1b4861a84a9fd69cd6a43093891bf98b9`.
The note contains the exact six-entry dependency manifest; all contract-pinned
hashes matched. Changed dependency hashes: none. Contract SHA-256:
`67ff7aefe2b696db00433305f42774aca02c53253d877ac1ffc6035c81dbc631`.

Checks: cat, rg -n, sed -n, sha256sum; initial broad output truncated and decisive
branches reread with targeted output. No tests, builds, probes, Cargo, compiler
changes, Git, network, children or reviewer appointments. No executable oracle;
H1–H3 share runtime assumptions and are explicitly unverified. Seeds/ranges and
executed mutations: none. Requested Sol/researcher/high cap180s, Astra0,
children0; effective model/effort UNKNOWN. CPU/RSS/exact wall usage unmeasured;
charge the full 180s reservation. No heavy process.

Recommended next action: primary obtains fresh source review of this frozen
conditional result, then leases the exact cursor/parser producer seam if useful.
No additional synthetic-token or transition-model probe is recommended.

Commit packet:
- Exact leased paths: `notes/theory/2026-10-18-npair-lexer-bracket-identity.md`;
  `tasks/agent-loop/inbox/20261018-npair-lexer-bracket-identity.md`.
- Baseline SHA: `b3a9b1739b59d8c7991b5f798e98f71f96904b19`.
- Dependency hashes changed: none.
- Review: NOT_RUN; author provides no independent certification.
- Checks already run: source reads and SHA-256 comparisons above.
- Proposed message: `research: bound authentic lexer bracket identity and remaining row-start gate`.
- Shared-record deltas left to primary/curator: STOPPED receipt, conditional
  source result, exact cursor/parser remaining gate and unchanged parent closure0.
