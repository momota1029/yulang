# Receipt: initialization order and global effect handling

Date: 2026-10-16
Question: `2026-10-16-forward-definition-initialization-context`, revision 1
Approved draft: `forward-definition-initialization-context-a1`, revision 2
Integrated bundle: `885012b42`
Outcome: validated and consumed; the offered alternatives are replaced by the
user's ordering and global-effect rules, not selected as proposed

## Validation

Validated SHA-256 values:

- Question: `900cd3b5c946593a3738ddc97c3010cb4279f33ce4f8e7118d77a6ea30c90b07`.
- Draft: `5169884bbcbc5fff5b4a6633c69983fdd7bf2f775780645532bb578673069b57`.
- Approved answer: `8e238cdbd185c9f3bdd6042d7bc536bb827e869def34e363b3e79f29d8c77c12`.

The embedded approved draft is byte-identical to the complete saved revision 2.
The wrapper records the final approval quote `OK` after that complete display;
the earlier wording correction and revision-1 discussion do not replace this
approval. Stable message URLs and exact timestamps are unavailable, as disclosed.
Question/draft identities, revisions, absolute worktree and branch match.
Independent `spec_auditor` ordinary_carrier_contract returned CLEAN for exact
bundle conformance. Primary confirmed no playground runtime change between
`35e87f844` and discovery HEAD `b5d70994d`; changes since the draft's observed
`2e25a510d` are proofs/design records only. No source premise was silently
changed. The three matching files were committed together and rechecked byte
for byte against `885012b42` before consumption. The explicitly unapproved
`answer-draft-revision-1.md` archive remains untracked and excluded.

## Consumed scope and remaining gates

The governing [decision](../../notes/design/2026-10-16-initialization-order-global-effects.md)
records the exact replacement scope. Effect-producing lines cannot be exchanged
with one another. This does not make every such line individually immovable,
and forward demand alone does not authorize initialization that violates their
ordering. Escaping top-level initialization effects receive global handling or
an error; handlers around a value reference do not supply initialization
handling. Current scope permits automatic handling of `nondet`, `io` and similar
effects, without adding arbitrary global-handler registration.

Neither offered alternative's blanket dependency-first timing is approved.
No effect-detection algorithm, additional uninitialized-reference rule, concrete
owner-switch mechanism, old A/B publication law, reachability theorem, proof
closure or production cutover follows. Existing internal handler semantics is
retained. The primary assigned a bounded architectural source correspondence
for exact entry/return, order and global-consumer obligations. The local
initializer-to-caller handler boundary can be proved separately from scheduling;
its implementation still requires that proof and independent review. Native
inference proofs continue independently.

## Applied local escaping-effect boundary

The [local gate](../../notes/progress/2026-10-16-playground-initializer-boundary.md)
now implements the approved escaping-effect rule after constructive proof and
CLEAN semantic/spec reviews. It prevents caller-handler search across pending
GlobalRead while retaining internal handlers, live state and normal cache return.
All 108 playground tests pass. The answer is not reapplied as dependency-first
permission: effect-order observation/source scheduling and whole materialization
remain OPEN. No old A/B or automatic-global-consumer law is inferred.
