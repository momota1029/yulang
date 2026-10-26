# Independent review: native birth-level SCC correction

Revision: r1. Reviewer: `/root/call_entry_review`, independent non-author of
the Rust correction and integration files. Requested model/effort: inherited;
separately observed runtime model/effort metadata: unavailable. No configured
role is presented as observed runtime evidence. Baseline:
`0f6346a2de0a8bff863f41d487eb4b29cf8fb5f3`.

## Verdict

**CLEAN within the assigned native qualification correction and static Lean
integration scope.** No blocking, major, or minor defect found in this bounded
pass. This is not certification of full source inference soundness, every
retained-support consumer, or Imported identity handling.

The four Rust files and producer handoff matched their assigned hashes at
intake and again at review completion:

| Frozen input | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_value_graph.rs` | `aaaa88a374083f898188cd390b8cf0244855d8c09c8939b9e68ee2831bc692cf` |
| `crates/yu-solver/src/candidate_source.rs` | `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a` |
| `crates/yu-solver/src/candidate_intrusion_tests.rs` | `12bf5b890f04a577f8fe633724d7c6ea526e4b5da744bb26aa3797d1fb444668` |
| `crates/yu-solver/tests/candidate_intrusion_observation.rs` | `9aec9745908177e2e2ebef67634444fb0d5f703732735951121db9d74e1ffc23` |
| `tasks/agent-loop/inbox/20261026-inference-birth-native.md` | `007dceffd19c50dc170421513bf7944c2688d859bcbf506dd5b8c1b89c78e80d` |

## Source and implementation correspondence

Authority inspected: the October 24 birth-level SCC design and corresponding
BL1/helper discussion, with the October 11 inference principles and actual
planner as context. Qualification requires mutual reachability through
vertices at one immutable birth level. Equal endpoint births in a global SCC
are insufficient. Raw cross-level references remain available. Rejection by
this rule does not forbid equality arising from independent valid constraints.

1. **Birth comes from the existing source planner.**
   `candidate_source.rs:1073–1090,1211–1215,1285–1286,1305–1306,1356–1378,1383–1402,1444–1498,1547–1560`
   threads the graph's fragment table through the actual work traversal.
   Root/formal parameters, catch/case binders, and initializer Values receive
   the levels selected at their declaration or constructor. Nested initializer
   work receives the existing incremented level. Unused catch/case binders
   also receive their declaration level. No mutable row/union-find level is
   used to recover a birth.

2. **Names preserve identity and birth.**
   `candidate_value_graph.rs:48–94,103–115` keeps resolved semantic Values
   interned once; modules start at level 1 for forward references. Conflicting
   assignments fail. `record_expression_level` updates an occurrence's
   expression vertex, if present, and helper; it does not reassign the resolved
   Name target's birth. Group/Ascription continue to expose the underlying
   semantic value. The deeper-first-use case-binder regression is pertinent
   to this distinction.

3. **Helpers have planning levels, with the local invariant checked before SCC.**
   At `candidate_value_graph.rs:354–366`, sealing first requires complete level
   metadata and then checks every raw edge whose target is a helper for equal
   source/target planning levels. This is the local helper-target premise used
   by `BirthLevelSCC.PlanningInvariant`; it is stronger evidence than merely
   asserting that an arbitrary whole path preserves levels. Helper-to-semantic
   Name edges may cross births and are retained. The helper construction at
   `:255–345` keeps binding initializers out of enclosing statement-block helper
   links, allowing their independently selected deeper level.

4. **Both native SCC passes use the same filter.**
   `candidate_value_graph.rs:371–391` skips unequal-level edges in the forward
   finishing-order traversal and the reverse component traversal. Singleton
   components remain valid. `qualifies` at `:395–396` compares these filtered
   component labels. Neither pass deletes or rewrites the raw adjacency
   (`:96–101`). The equal-endpoint/different-level-detour test is therefore a
   useful falsifier for the former global-SCC behavior.

5. **Nested applications retain their actual owner.**
   `candidate_value_graph.rs:194–199,218–222` now descends through FieldTail
   receivers and OperatorApplication operands with the same owner. This
   agrees with the existing inference walk at
   `candidate_source.rs:1267–1277`. Nested initializer owners remain separate
   at `candidate_value_graph.rs:230–251`. The FieldTail regression exercises a
   retained application inside a nested initializer, not merely a synthetic
   owner label.

6. **The added work is structurally linear.**
   Birth recording performs constant expected-time identity lookup per existing
   expression/binder visit. Sealing performs one metadata pass, one raw-edge
   invariant pass, and the two adjacency-based SCC passes: O(V + E), subject
   to the existing hash-table cost model. There is no per-level SCC rescan,
   per-event reachability search, or helper-elimination rescan. The new
   `Option<u32>` vector is O(V) and counted at `candidate_value_graph.rs:411`.
   The existing fragment vector is reused and lives through inference rather
   than being recomputed. This is static complexity/accounting review, not a
   new peak-memory or timing measurement.

## Consumer and regression assessment

Inspected the unchanged qualification consumers in
`candidate_intrusion.rs:325–355,383–416` and sealing lifecycle in
`lib.rs:1551,10401`. The correction changes which retained events qualify;
the four-file diff does not alter pair merging, bounds, row levels, or
freshening. Source-event provenance and actual parent/copy records remain.

The approved expectation changes at
`candidate_intrusion_tests.rs:310–338` and
`tests/candidate_intrusion_observation.rs:31–73` retain the original source,
successful solve, reciprocal owner/receiver occurrences, real parent records,
kind agreement, valid event indices, provenance/reuse checks, and consumption
accounting. They change the cross-birth qualification expectation and remove
the rule-specific equality requirement. They do not require inequality of
representatives, which could be false for an independent legitimate reason.

The added graph regressions at `candidate_value_graph.rs:780–868` cover
immutable birth/deeper Name use, case-binder declaration birth, FieldTail
ownership, the wrong-level detour, and missing/inconsistent helper metadata.
Graph fixtures now obtain births from actual source collection. The synthetic
SCC fixture supplies uniform explicit metadata and retains its component
checks. Existing bounded-linear graph coverage was retained.

## Retained execution evidence

Read all six listed log/JSON files under
`/workspace/scratch/f98087c7ac1a/inference-native/`; their hashes match the
producer handoff. The JSON receipts report exit code 0, an absolute cargo path
under `toolchains/rust-1.99.1`, `--locked`, the candidate feature,
`--test-threads=1`, and a 6 GiB address-space limit.

| Check | Observed test result | Log SHA-256 | JSON SHA-256 |
| --- | --- | --- | --- |
| `graph-tests-01` | 24 passed, 0 failed | `04fb27193bfda412cf3d2ad77c9d0d5ee55beff697faa0eddcbfa3b8f2d9c815` | `a520d2a12ad03a8b206dbff6984f8a6d25db15de761820df6e7970459749321e` |
| `intrusion-unit-01` | 17 passed, 0 failed | `eb39dd4def99546b278a1189a33ab8f94984d4923fcf226477a2625d6ed96d3a` | `116eee38eab730807c5a693f771f4d1600b187c216e485d2f21e3f37c4c2e875` |
| `intrusion-observation-01` | 3 passed, 0 failed | `15ef3e5bc6a44269eeffc1124c35968e44e10b2955ba9d3584854d20c62a3a94` | `ec63f8a2c09f2b0b1f0123b8d45fe1b251a39e412f77fd554f1bfa0b727739a7` |

These are retained execution receipts, not reviewer reruns or independent
toolchain-provenance verification. Compiler warnings occur in the retained
logs; this review does not certify warning cleanup. No concrete gap requiring
a further checker/test process was found.

## Static Lean integration check

Read the entire three-file integration diff against the baseline:

| File | Reviewed SHA-256 |
| --- | --- |
| `notes/theory/lean/lakefile.toml` | `cab85ff9a8a7dc5103fe932739dcea0dfc02e6420b1277565449882c802473bd` |
| `notes/theory/lean/YulangClosure/InferenceProofs.lean` | `2911f3fe5e1e0188c4762f8d01c96bab36e411cebbfbb898b9a3361c97cd6651` |
| `notes/theory/lean/AuditInferenceProofs.lean` | `a8d8f19cdeb1e5f9c5db669dd1c5d5bb5f02dff8f20468bf26cf3b2c7b535bea` |

The default library globs preserve `YulangClosure` and
`YulangClosure.ProofAdvancement`, adding `YulangClosure.InferenceProofs`.
The new aggregate imports `BirthLevelSCC` and expressly preserves the original
inference-soundness boundary. The 54-line audit uses actual originating module
indices, enumerates all theorem constants including generated/private ones,
rejects project axioms, checks the four required application roots, checks and
prints each theorem's axioms, and rejects dependencies outside
`propext`, `Classical.choice`, and `Quot.sound`. The explicit `Nat` annotation
on the counter at line 28 affects audit elaboration, not the theorem scope or
axiom policy. No bypass found. This portion is static review; a new aggregate
build/audit execution is not certified by this receipt. The prior separate
BirthLevelSCC review records its 57-theorem/32-root execution evidence.

## Severity-tagged scope observations

| Severity | Location | Observation and recommended action |
| --- | --- | --- |
| INFO | `candidate_intrusion.rs:325–326,383–385,393–394` | Existing any-support qualification consumers remain outside this correction's closure claim. Preserve the separately tracked support-policy obligation; do not infer that all retained equality publication is now proved lawful. |
| INFO | `candidate_value_graph.rs:103–115` | Imported identity resolution/fallback is unchanged. Preserve its explicit separate boundary; do not claim complete source identity/incidence coverage from these four files. |
| INFO | `candidate_value_graph.rs:354–393`; `BirthLevelSCC.lean` | Static inspection supports this native filtered Kosaraju implementation, and its checked helper premise matches the Lean model. Native algorithm correctness and full source-to-model incidence are not newly formalized here. Keep that distinction in completion claims. |
| INFO | `YulangClosure/InferenceProofs.lean:3–7` | Eligibility and helper projection do not close full source inference, BL-JOINT/shared-witness constraints, or original `SourceProblem.InferenceSoundness`. Retain the aggregate's explicit boundary. |

## Inspected scope and cessation

Inspected the complete four-file Rust diff, all graph production code and
changed graph tests, relevant actual planner work cases, unchanged consumer
and sealing seams, the complete changed integration test, the authoritative
source material, retained logs/receipts, and the three Lean integration files.
Followed repository instructions and the proof skill already read in this
session. Did not review every ordinary-source solver path, all dependencies,
the full compiler, performance empirically, or unrelated working-tree changes.

Only this exact leased receipt was written. Read-only Git inspection was
explicitly authorized by the primary; no Git mutation occurred. No source,
cache, scheduling record, other receipt, or semantics was changed. No children
or checker/test processes were launched. **Receipt frozen; writes STOPPED.**
