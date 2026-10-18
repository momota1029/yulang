# Sprint R34 — authenticated active-capture join

Status: ACTIVE, revision 2. Branch `research/simple-sub-intrusion`; original
baseline `22c29664a1d59db7d149b752ef166ec2ec9ca9dd`; initial lane launch
baseline `d281632f4ba604340d88ed0bdcb01b0921960910`.

Revision 2 is a narrow repair grant after revision 1's only focused Cargo
invocation exited during test-code compilation, before either test ran. It
preserves the fixed outcome and semantic boundary. Frozen pre-repair candidate
hashes: `candidate_scheme.rs`
`ca1ef67a0ac4edcac5f0a1df07a5a04e505871e64d1596f33194967dc7ef984e` and
`candidate_local_self_recursion.rs`
`81b83dd67326f4c66c96e8a39598ac0700c7c08170d732c37eab1f3d4dbd0da5`.
The first compiler invocation reported three test-code errors: an
`HirOccurrenceId` was passed to `LocalSource::expression` instead of a
`LocalSourceIndex`; a group-range filter dereferenced `&usize` twice; and the
integration test moved `hir` while `source` borrowed it. The native writer is
confirmed stopped before this revision.

## Original outcome and success evidence

Parent goal: implement Yulang type inference and executor with proofs. Preserve
the original Simple-sub claims, source domain, Call/effects relation and all
quantifiers. Original parent conditions remain OPEN at `0 -> 0`; R30's
independent `j0/a0` and same-event world-action condition also remains OPEN.

Fixed outcome: use existing native records to establish the exact join

`active initializer Link -> checking/source event -> signed pair/group
incidence -> helper capture/publication -> both retained FreshUse maps`,

or freeze the first edge that cannot be authenticated. This is source/native
correspondence evidence only. It does not introduce or prove the missing
source-owned C/D declaration, sort, scope, dependency telescope, or capture
action, and it cannot close an original parent condition.

Success requires a nonempty fully authenticated join, meaningful negative
controls for an unrelated source occurrence/pair and sibling use, a focused
test pass, and fresh independent compiler and spec reviews. Keep shared rows
shared. Classify actual fresh allocation and aliases only from retained
reconstruction metadata; preserve `RowKey` component kind in every identity.
The exact active Link's lack of FreshUse must have its own assertion so an
earlier assertion cannot hide whether it ran. A test pass alone is not proof.

## Dependency and authority boundary

- R33 closeout: `notes/progress/2026-10-18-r33-active-capture-observer-closeout.md`,
  SHA-256 `7f2459563f19327f9b8e49ac44e1915ddb018e74c1935c31433993fafdcd9f03`.
- R33 contract SHA-256 `5e3012e8d113e887ee633e35b9786ee55cab8bb962ff7e53f463274eb924a9c3`;
  R33 reviewed allocating-lift report SHA-256
  `c9edf92f63511617dda2ce99cef668491adbc1894a4ab2a5f9e27148350d7a9c`.
- `candidate_scheme.rs` `03b44d0f8280c1ae79f66b5528f1bd0b0ffebac46b312ef7ffce605f702f48dd`;
  `candidate_source.rs` read-only `66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c`.
- `candidate_local_self_recursion.rs`
  `a6406f3eef2b25844272da9cbe121277001760d004f733029dcc3f600aa79c7a`;
  `shadow_apply.rs` `5bbcf27d51906814ba38b2cca2066807d285d0b1817f0ea6e04d70c4a5c8a5cb`;
  `candidate_intrusion_observation.rs`
  `04a876b9fe0a3a45f2d1996446a11d0b36dce3bb26ad02537118e4853e4b78e1`.
- R32 reference-retention proof SHA-256
  `fa0e0f25dfd454a51c924b505e847b02133a37b38689e033d34ae5796b24eb8b`.

The existing `#[cfg(test)]` reconstruction records in `candidate_scheme.rs`
include typed `source_representative`, `allocated_fresh_image`,
`first_entry_graph_row`, `existing_image`, and image identity. Use them to
distinguish allocated images, canonical aliases and retained shared rows. The
public intrusion observer already exposes source event and signed incidence;
the narrow missing join is Link-to-event/pair and pair-to-both-FreshUse maps.
Keep `candidate_source.rs` read-only and add no production observer/API or
allocation policy.

## Two continuing lanes

### Native join — Luna/high implementer, cap 600 seconds

Exact write lease after actual launch:

- `crates/yu-solver/src/candidate_scheme.rs` — existing test module only;
- `crates/yu-solver/tests/candidate_local_self_recursion.rs`;
- `notes/progress/2026-10-18-active-capture-authenticated-join-r34.md`;
- `tasks/agent-loop/inbox/20261018-active-capture-authenticated-join-r34.md`.

Read `candidate_source.rs`, `shadow_apply.rs`, and the existing intrusion
regression; do not edit them. Keep source occurrence, helper origin, receiver/
loop, `same_scc`, pair kind/polarity/target, all selected group incidences,
publication/capture identity, and each map's actual image in typed joins.
Do not infer disjoint final representatives unless later unions are excluded.
The active Link no-FreshUse assertion must be independent of the authenticated
helper-join assertions. Preserve the existing two-helper accepted-source
specimen. If a necessary edge is absent or no genuine negative witness exists,
stop at that exact edge and report it without adding an observer.

The original one Cargo invocation is spent and remains recorded as a compile
failure with no test assertion executed. After fixing only the three reported
compile errors and independently checking the source relationships below, the
new native writer may run one additional focused Cargo invocation:

```text
cargo test -p yu-solver --features shadow-apply-candidate active_outer_root_two_helper_uses
```

The lifetime total is two invocations: the failed initial invocation and this
single additional attempt. Do not run another test, build, probe or Cargo
process. Before the additional invocation, remove or repair any assertion that
infers all-row nonsharing from source locality alone; retained shared rows must
remain shared, and each fresh image must be justified by its exact retained
reconstruction metadata. Do not weaken an assertion merely to pass. If the
actual maps cannot be classified/authenticated from those records, stop before
the second invocation and freeze that exact edge. No production code, public
observer/API, semantics, allocation policy, expected output, or fixture
meaning changes.

### Source proof — BLOCKED at owning introduction

No proof writer is assigned this sprint. The R33 reviewed obstruction and R32
reference-retention lemma remain applicable, but another constructor inventory
or conditional lift would leave the same decisive premise untouched. The owner
is the source inference/extrusion authority. Resume only when an authentic
source rule supplies C/D's sort, original scope/telescope, typed dependencies
and capture action; then apply R32 retention and prove the unchanged complete
Call lift over both helper frames and arbitrary original client context. Native
identities cannot supply this source law. No Astra assignment.

## Review, resources, and integration

Fresh isolated compiler review (180 seconds) checks the exact occurrence,
typed pair/group and capture-to-two-map joins, shared-versus-fresh
classification, negative controls, and execution claims. Fresh isolated spec
review (180 seconds) checks source-domain preservation, unaltered Call/effects,
and candidate/evidence versus theorem status. Neither reviewer may author the
native artifact. Luna integration cap: 120 seconds.

Revision 1's native assignment duration is UNKNOWN. Conservatively charge its
entire 600-second grant as spent; the observed 4.36 seconds is only the Cargo
process duration, not total assignment time. Revision 2 grants a separate
native repair assignment capped at 600 seconds, plus fresh reviews at 180
seconds each and Luna integration at 120 seconds: total sprint cap 1,680
seconds, of which 600 are already charged and 1,080 remain. Astra0; two focused
Cargo invocations maximum across both revisions; no probes or other builds. Do
not carry R33's spent or unused budget into this sprint. Requested/observed
runtime settings must be recorded truthfully; absent model metadata remains
UNKNOWN.

R33's frozen `candidate_local_self_recursion.rs` lease is explicitly reclaimed
by Luna after confirming all R33 writers are terminal, then granted to the R34
native writer. Unknown writers keep quarantined leases. `current.json` and
`tasks/current.md` remain Luna-owned. Preserve the unrelated quarantined paths
recorded in current state and do not stage them.

Parent application: unless this join reveals a new source-qualified
counterexample or supplies the missing source-owned introduction (not expected
from native identities), original parent conditions remain `0 -> 0`; R30 is
independent. Do not promote the join to proof, semantic adoption, or production
authority.

Stop on a missing join edge, unsupported negative-control premise, the
additional focused-test failure, review blocker, budget cap, or material
authority/dependency change.
Consult the dispatcher at sprint end, a concrete counterexample, material
lease/dependency/resource change, or new semantic choice; internal repairs and
ordinary review receipts stay within this envelope. Luna owns review
adjudication, state synchronization, staging, commit and non-forced push.
