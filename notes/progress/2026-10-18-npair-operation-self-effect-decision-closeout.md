# NPAIR Operation self-effect decision sprint closeout

Sprint `npair-operation-self-effect-decision-20261018`, contract revision 3,
SHA-256 `0ab0e6a7353810204825ffd05815b2a42195a0915c5380c72831061b7355cd94`.
Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`.

## Outcome

- Original parent conditions resolved: **0**. The parent and its quantifiers,
  source domain, F1/FK1, N-Transport, complete Call and downstream obligations
  remain OPEN.
- The reviewed semantic classification establishes only that the cited
  IF/Operation inputs do not expose the original Operation-specific projection
  from contribution cases to its latent root result-effect field. It does not
  demonstrate that two compatible semantics exist; no new rule or meaning was
  selected. The spec reviewer found one minor rev1 dependency-hash typo; rev2
  corrected it without semantic changes, and an independent recheck closed the
  finding.
- The explicit-row cache result is **conditional** on distinct parsed rows
  having distinct `SourceNodeKey`s. The compiler review of the primary's
  injectivity artifact found a major gap: the pinned sources do not prove
  distinct `BracketRow` starts in parser recovery/empty-node cases, and
  `cursor::parse_root` was outside that packet. No authentic collision was
  found. Reuse only the exact Eq/Hash characterization and HIR key transport;
  do not treat the injectivity claim as proved.
- No code or tests changed; no tests, builds, probes or compiler execution ran.
  `NO_SAFE_CODE_SLICE` remains. All 900 seconds in this sprint are charged;
  Astra 0. All authors and reviewers stopped.

## Frozen evidence and adjudication

- Semantic classification: `notes/design/2026-10-18-npair-operation-self-effect-decision.md`, SHA-256 `fe258f9f5d3d40f80814fe478e9cde7019dc2436462b77a3ad6b9f6fe847f1e5`; handoff SHA-256 `3fd708f4d7a9c3e2df1fdec922ea87f0d58a05ad385f544b487c72e9825df3d7`. Spec review: no major/blocking findings; minor rev1 pin typo closed by contract rev2 and independent exact-hash recheck.
- Address/cache lemma: `notes/theory/2026-10-18-npair-explicit-row-address-invariant.md`, SHA-256 `2796562ac2e359933ff5ac8ec58352a5b61b83264b5b88baa7ef8ce0065382ac`; handoff SHA-256 `677fc2df20b5508403ffcff5e6d95b60b47555c15ff657cfc9376702a855f43c`. Compiler review supports its conditional cache-miss argument; the hypothesized key alias is not a source-qualified counterexample.
- Primary injectivity candidate: `notes/theory/2026-10-18-npair-source-node-key-injectivity.md`, SHA-256 `8ab47830c985e13a4823a8a707ad6ee0b3ff9bb970f68da752d517052f59eeb6`; handoff SHA-256 `0b0e7643899561d5cf6ddd761d5488ce7593f49cd8ccbb64d02fd8fec7aef270`. **Rejected as an unconditional key-separation proof.** Its Eq/Hash characterization and HIR transport remain useful; its distinct-start premise is unproved for parser/recovery nodes. Fresh compiler review found one major; the candidate is not promoted.
- Contract rev1 contained the incorrect prior-lift hash `…d88aee8d…`; contract rev2 `5b5891f850fa5f1475d7762630c515b0923d334088fb8494a11ce6c94d2adbeb` corrected it to the exact `…d88eaa8d…` artifact hash. Contract rev3 `0ab0e6a7353810204825ffd05815b2a42195a0915c5380c72831061b7355cd94` authorized only the final reserved source-identity audit. No source/semantic authority changed.

Relevant pushes: `db6d915df`, `77097aa70`, `9ef00d05e`, `faefd179f`, `ca6bc33ee`, `515b705f6`, all on `research/simple-sub-intrusion`.

## Next exact boundary

The compiler review identifies the actual next owner: parser construction and
recovery for `BracketRow` via `cursor::parse_root`, the type-expression parser,
and delimited parser. The next bounded packet is
`npair-parser-row-key-separation-20261018`, contract revision 1. It targets only
key separation for rows that can precede and seed the Operation root cache,
including recovery paths; it may not narrow to syntax-clean inputs or claim a
collision without authentic evidence.
