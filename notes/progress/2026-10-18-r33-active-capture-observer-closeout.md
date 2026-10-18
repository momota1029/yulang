# R33 closeout — active-capture observer join

## Result

- Original parent conditions discharged: **0 → 0**. The parent remains OPEN;
  the independent R30 `j0/a0` and same-event world-action gate is unchanged.
- The proof lane applies R32's reviewed reference-retention lemma, then locates
  the candidate allocating lift's first failed constructor inversion at
  Generalize §3.3: there is no independently specified source introduction for
  the receiver-owned C/D declarations, scopes and dependency telescope. It does
  not establish that every possible allocating extension is impossible, nor a
  source-qualified counterexample.
- The native lane's focused Cargo invocation compiled but failed at the first
  new assertion. It had established a private active-root `Action::Link`, two
  helper `Action::Local` records and two nonempty FreshUse maps. It did **not**
  reach the later assertion that the active Link has no FreshUse, or any
  `intrusion_observation` event/pair/group assertion. No full Link-to-pair-to-two
  map join or external integration test was established.
- The failed assertion required every row in both maps to be disjoint. This
  contradicts `prepare_candidate_fresh_use`, which can retain boundary/shared
  rows in both maps. Fresh compiler and spec reviewers also found: the
  attempted representative control discarded component kind; source-event
  identity was not checked against helper origin and loop receiver; signed
  pair/group claims were not fully qualified; and selected pairs were not
  connected through helper capture/publication to either FreshUse map. The
  reviewer classified the proof obstruction CLEAN and the native diff BLOCKED.
- I reverted only the two leased code/test files after review. They are
  byte-identical to R33's pinned baseline. No production code or public
  observer/API changed.

## Frozen evidence

- [Allocating-lift proof](../theory/2026-10-18-active-capture-allocating-lift-r33.md), SHA-256 `c9edf92f63511617dda2ce99cef668491adbc1894a4ab2a5f9e27148350d7a9c`
- [Proof handoff](../../tasks/agent-loop/inbox/20261018-active-capture-allocating-lift-r33.md), SHA-256 `af657387bf17d35ba39ad4ee0879458f3079483a05f41b551548fe5794ef5e14`
- [Native report](2026-10-18-active-capture-native-join-r33.md), SHA-256 `2fa1b11dbb328b8a9d8ef5580689c4bf2f967f4e264d41776a8da325eb1ece11`
- [Native handoff](../../tasks/agent-loop/inbox/20261018-active-capture-native-join-r33.md), SHA-256 `43902993c186843f818ae2b0b322c918ce2de96770bbbf1fa6867057cfe921ca`
- R33 test-diff snapshot: `candidate_source.rs` `7e0a0e71fa219e63e7b16729910c74126bf67e41709448e95cc43c743c369b4d`;
  `candidate_local_self_recursion.rs` `3b90ed2dd2b58a546b820ea5bb1b388e76b0f0e605efd0b9bead2fe37ae5633c`.
  The leased code files were then restored exactly to pinned baseline hashes
  `66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c` and
  `a6406f3eef2b25844272da9cbe121277001760d004f733029dcc3f600aa79c7a`.
- [R33 contract](../../tasks/agent-loop/sprints/active-capture-observer-join-20261018-r33.md), SHA-256 `5e3012e8d113e887ee633e35b9786ee55cab8bb962ff7e53f463274eb924a9c3`.

## Checks and limits

One focused Cargo process was run:
`cargo test -p yu-solver --features shadow-apply-candidate active_outer_root_two_helper_uses`.
It failed with 0 passed, 1 failed, 729 filtered out; elapsed time was about 29
seconds. No retry, other test, build or probe ran. Fresh compiler and spec
reviews were read-only. Static `python3 tools/agent_sprint.py check` and
`git diff --check` validate repository state only.

## Next discriminating evidence

Any retry needs a new bounded check grant. First filter genuinely fresh local
images using authenticated reconstruction metadata while preserving shared
rows; source locality alone is insufficient. Then match the exact Link to its
helper origin/loop receiver, exact signed pairs/groups and both retained map
images. Keep `ComponentKind` in representative keys and reject substitutions
with a real unrelated pair. If any join edge cannot be derived from existing
records, stop at that precise edge and consider a test-only private observer in
a separate contract. The allocating proof independently still needs an
authentic Generalize §3.3 C/D introduction and a whole-tree lift for every
original Call witness.
