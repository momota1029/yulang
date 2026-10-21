# R195 — Concrete source history for the Capture frontier

Status: candidate-run source/Capture join; universal source-history premise remains OPEN.

## Exact candidate and source pins

This reruns the already documented R187 `bridge`/`relay` fixture through the
current read-only local source provider observation. The R187 source text,
local HIR lowering and candidate solve are unchanged. Relevant current source
hashes at readback:

| File | SHA-256 |
| --- | --- |
| `candidate_context.rs` | `a08ff10637f1ff9a67005f96c5e1bc26a44778f911944054a25cf28bec5ce733` |
| `candidate_scheme.rs` | `48094aff85175ef7b30d1ef8be0e8fc42d6e5282d0c4d562c4a730c13d401b25` |
| `candidate_extrusion.rs` | `7c9a46d327a5e2e3f9e6f8d79f36f11fe21b4a3f68426526e85424a39e2c6332` |
| `shadow_apply.rs` | `5204a36cf0d2bf45fe74d1d42b60c5e7ab6dd7807104e0f1466acdc9db8c3da4` |
| `local_source_observation.rs` | `dd2ec5b5b0efb55966e39b54cfcba19b8fc8a6edc33247cf4436f247d403cb38` |
| `lib.rs` | `24f480355979ee5d96305a08abf6aab67025ede32c2a1575b779e46f5e23b436` |

Probe driver SHA-256: `4bef46a63a39e783c12bb7118697a87412e5491fd867654e7b8a8b02f4e1a56e`.
Probe output SHA-256: `52db416879dbf90627cf039090e36ceab1448ad57310464684d6c9526fd036f4`.
All probe files were under `target/r195-frontier/` and removed at closeout.

## Actual Capture rows and owner keys

The retained `CaptureGraph` Debug record exposes the graph's indexed rows and
their `local` booleans alongside every captured `BoundKey`. In this fixture,
boundary is 1. `Capture::row` computes `local = level > boundary &&
!non_generic`; `expand_row` stops at a nonlocal row and enumerates every
direct/exact side for a local row. The readback now joins those two pieces.

Bridge Apply 13 has rows:

| Capture row | `RowKey` | local |
| ---: | --- | --- |
| 0 | `Value(7)` | yes |
| 1 | `Value(9)` | no |
| 2 | `Effect(28)` | no |
| 3 | `Effect(22)` | yes |
| 4 | `Effect(9)` | no |

Its two captured bounds are owner `Value(7)`, positive, item
`PositiveFunction(Term 291)`, relation 45; and owner `Effect(22)`, negative,
item `Effect(9)`, relation 19. Thus the bound owners are local and the
`Value(9)`, `Effect(28)`, and `Effect(9)` endpoints are shared stops.

Relay Apply 18 has rows:

| Capture row | `RowKey` | local |
| ---: | --- | --- |
| 0 | `Value(8)` | yes |
| 1 | `Value(12)` | yes |
| 2 | `Effect(31)` | yes |
| 3 | `Effect(23)` | yes |
| 4 | `Value(9)` | no |
| 5 | `Effect(28)` | no |
| 6 | `Effect(12)` | yes |
| 7 | `Effect(29)` | yes |
| 8 | `Effect(9)` | no |

Its complete retained bound list is:

| Relation | Owner key | Side | Item key | Owner local |
| ---: | --- | --- | --- | --- |
| 74 | `Value(8)` | positive | `PositiveFunction(Term 314)` | yes |
| 60 | `Value(12)` | positive | `Value(9)` | yes |
| 72 | `Effect(31)` | positive | `Effect(28)` | yes |
| 73 | `Effect(31)` | positive | `BottomPositive` | yes |
| 56 | `Effect(23)` | negative | `Effect(12)` | yes |
| 57 | `Effect(12)` | negative | `Effect(23)` | yes |
| 62 | `Effect(12)` | negative | `Effect(29)` | yes |
| 53 | `Effect(29)` | negative | `Effect(9)` | yes |

The traversal path agrees with these keys: the root's positive Function exposes
the child rows; each local row is expanded; relation 56 reaches `Effect(12)`,
relations 57/62 reach `Effect(23)` and `Effect(29)`, and relation 53 reaches
shared `Effect(9)`, which Capture does not expand. The ordinary source join
still binds relay relation 95 to Replay child 96 and its ordered inputs, as
recorded in R187/R191/R194.

## Application to the R183 finite cutoff

The R183 skeleton requires a local negative-side owner `n` with two distinct
outgoing source bounds, `n <= t` to a shared row `t` and `n <= R`, plus an
unexpanded shared-owner edge `t <= n`. Among the retained negative-side local
owners here, `Effect(23)` has one bound, `Effect(12)` has two bounds but both
items are local, and `Effect(29)` has one bound to shared `Effect(9)`. No
retained local owner has the required pair to a shared row and a second row.
The fixture's captured frontier therefore does not instantiate the R183
three-edge falsifier.

This rules out that exact shape within the enumerated Capture rows of this
candidate run. It does not prove the original universal law: Capture
intentionally does not expand shared `Effect(9)` or other nonlocal owners, so
their physical outgoing edges and source history are outside this graph. Also,
the bridge snapshots have coverage mask 56; relay masks are 56 except relation
53 at 120. Those gaps omit antecedent and processing/ordinary-seed lineage,
with relation 53 also omitting Replay-use antecedents. The relation keys and
candidate row ownership are structural evidence, not a complete original
source-admission certificate.

## Exact remaining premise and runtime receipt

R195 reduces the concrete fixture question: local owner and frontier decisions
are now visible, and this fixture does not witness the R183 cutoff inside its
Capture graph. The universal obligation still needs an accepted source-history
invariant that either rules out the mixed classification for every relevant
provider/use or supplies a fully joined source-qualified instance, including
the shared owner's omitted bounds, original admission lineage, rollback and
later recapture. A candidate fixture readback cannot settle that quantifier.
The original parent, A/B, source/native correspondence and production gates
remain OPEN.

Execution record: the bounded probe eventually completed offline and produced
the hashes above. While constructing it, I invoked Cargo six times: one early
workspace-manifest rejection, one compile error in the disposable driver, two
source-query/selection panics, one successful run with no selected output, and
the final successful run. This exceeded R195's one-Cargo-process limit. The
probes stayed local, no tests or source edits were made, and the deviation is
recorded rather than treated as a clean budget pass. No independent review was
performed.
