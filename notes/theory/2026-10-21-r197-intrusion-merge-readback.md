# R197 — R187 intrusion merge and source readback

Status: source-qualified provisional merge observation; no counterexample or theorem closure.

## Pinned inputs and run

The probe reran the R187 `bridge`/`relay` source through the existing read-only
candidate APIs, with the R195 local Capture owner records. Worktree source
hashes:

| File | SHA-256 |
| --- | --- |
| `candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `candidate_source.rs` | `937ce62065be19473fcb37a104f1aaf68e9a9431b8683d8e9a33d221c9e6c26a` |
| `candidate_scheme.rs` | `48094aff85175ef7b30d1ef8be0e8fc42d6e5282d0c4d562c4a730c13d401b25` |
| `shadow_apply.rs` | `5204a36cf0d2bf45fe74d1d42b60c5e7ab6dd7807104e0f1466acdc9db8c3da4` |
| `local_source_observation.rs` | `dd2ec5b5b0efb55966e39b54cfcba19b8fc8a6edc33247cf4436f247d403cb38` |
| `lib.rs` | `24f480355979ee5d96305a08abf6aab67025ede32c2a1575b779e46f5e23b436` |

Probe driver SHA-256: `f80ecf25c5446199fdfcd68d9045c114db8708f38743bdbe75eed8d16df2d6c3`.
Probe output SHA-256: `b0de245f7f304e0813d8e14fd9e6297cbc102bedeeca2420ca3ea17105ec3bbe`.
The single offline Cargo invocation succeeded; no retry was needed. Scratch was
confined to `target/r197-merge-readback/` and removed at closeout.

## Retained intrusion events and parent links

The observation returned 4 source events, 4 parent links, one group, no reuse,
and `pending=4/4`. All parent links have source set 0 with `source_events=[0]`;
their source event is checking occurrence 9 / slot 0, origin local definition
ordinal 0 (`bridge`) and receiver module definition `outer`:

| Parent | Copy → final representative | Parent representative | Side | Target | source event |
| ---: | --- | --- | --- | ---: | ---: |
| 0 | Value 26 → 24 | Value 24 | positive | 1 | 0 |
| 1 | Effect 26 → 9 | Effect 9 | positive | 1 | 0 |
| 2 | Effect 27 → 25 | Effect 25 | negative | 1 | 0 |
| 3 | Value 27 → 9 | Value 9 | negative | 1 | 0 |

The event table separately maps event 0 to the checking occurrence and the
source local/module identities above. Event 1 is occurrence 13, local ordinal
1 (`relay`) to local ordinal 0 (`bridge`); event 2 is occurrence 18, module
`outer` to local ordinal 1 (`relay`). The parent records therefore join the
actual `bridge`-to-`outer` source checking event to settled copy/representative
identities. They are retained final-state records, not an event-time replay of
every intermediate write.

## Join to local Capture ownership

For relay Apply 18, Capture boundary is 1. Its rows `Value(9)` and
`Effect(9)` are nonlocal; its rows `Value(12)` and `Effect(29)` are local. The
settled value/effect parent links 3 and 1 both end at those exact shared row
ordinals. The captured bounds include owner `Value(12)`, positive, item
`Value(9)`, relation 60, and owner `Effect(29)`, negative, item `Effect(9)`,
relation 53. Thus this accepted candidate fixture really does contain a
merge-to-shared-representative transition adjacent to later local Capture
owners. The merge event is tied to the source checking event, not inferred only
from equal numeric endpoints.

This establishes a mixed shared/local boundary in the observed fixture and
shows why equal levels at the initial Name/Lambda constructor cannot alone
close the induction. It does not establish the R183 three-edge falsifier:
the readback shows one local-owner edge to each shared row, while it does not
join (a) a shared-owner edge back to the same local row and (b) a second
required local-owner edge to the same R. The Capture readback intentionally
stops at nonlocal rows.

The relation-53 snapshot has coverage mask 120; the other relay snapshots have
mask 56. Those gaps omit antecedent, processing/ordinary-seed lineage, and for
relation 53 Replay-use antecedents. The retained merge source-event association
does not authenticate every original admission or prove a missing edge absent
from the shared owner's unexpanded physical bounds. No source-qualified
counterexample is established.

## Parent application

R197 sharpens the exact universal premise: successful source history can merge
fresh copies into shared representatives while later local rows still point to
those shared identities. The proof must now show, for each such rehomed
original edge, that an independent provider/Function path carries the missing
side of the chain, or find one accepted history where the same local owner
needs two uncompensated edges through the unexpanded shared owner. The original
parent, A/B, source/native correspondence and production gates remain OPEN.
No source edits or tests occurred. Solo primary; no independent review.
