# R37 revision 1–2 review receipt

Parent conditions remain `0 -> 0`; no source counterexample or semantic decision
was established. R37’s proof report passed fresh review **as a bounded
owner-specific obstruction only**. The actual ordinary Call result-description
introduction, logical scope, complete ordered telescope, and typed connection to
`NativeInterface.result` remain missing. C/D scopes and typed publication remain
open. Exact proof and independent-review hashes are in the R37 inbox/contract
and current snapshot.

## Native review findings

Revision 1 candidate `candidate_scheme.rs` SHA-256
`dab6a99c660c709ba85b7128e9c1b8f7a22827700552354038180dc92a9d437b` was
BLOCKED by both independent reviewers. The integration regression was additive
to the pinned baseline; no prior approved expectation, golden, diagnostic or
language output changed. The production prefix was byte-identical to baseline:
119639 bytes, SHA-256
`bc809becb6dc89149e2d00057f1d65b879121668f5485fef9d6a493d64f08a18`.

1. Supplied `Parent` was not authenticated against `parents[parent_index]`;
   changing `copy` to `parent` could pass kind/capture lookup and invent a link.
2. Capture-time representatives were required to equal current representatives,
   rejecting lawful merges before canonical-map handling.
3. A canonical-map hit may reuse a previous fresh image `F != S` with
   `allocated_fresh_image=false`; the image assertion incorrectly required `F=S`.
4. The missing-event negative could reject at the wrong earlier edge or skip
   without asserting.

Revision 2 fixed indexed Parent authentication and the nonvacuous negative, but
both independent delta reviews remained BLOCKED: downstream checks at
`candidate_scheme.rs:2348/2351`, `2689`, `2709` still imposed capture-time root
equality after merges; `:2719` still rejected a canonical hit that reuses a prior
fresh image. These are existing-owner correspondence defects, not semantic
changes. No target executed; Cargo remains gated.

## Immutable candidate preservation

The exact R37 revision 2 source/test delta against pinned launch commit
`887eed4370278cd9e789fb2b9b10ff58369da540` is
`notes/progress/2026-10-18-r37-rev2-native-candidate.patch`, SHA-256 recorded
with that file. Rev2 candidate SHA-256 was
`c2b629f43c08fb991741571ce9574ef7cb7abc4aac45078266bd9fe47aa8948d`; test
hash `47ced76fe8f0f136c42802b2376ca09f7cadec0fc8e5b1b3d4c6acc7bc613e55`;
progress `2e3f0baad01b11d6eb217a811e11446680ce290975fcd371f4d114313e74a1f5`;
handoff `63ea394c80868c8dd928066aa5e054fa9bc691ad96f1dd091e5d1c104ac58e45`.

Rev2 compiler/spec authors and reviewers are terminal. Revision 3 may alter only
the exact leased test surfaces under its versioned contract. No production
prefix, expected output, theorem scope or source rule changes are authorized.
