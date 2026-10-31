# R103 Rust source handoff — effect permission capture coherence

Sprint / contract: `EFFECT-PERMISSION-CAPTURE-COHERENCE/20261101-R103`,
`tasks/agent-loop/sprints/effect-permission-capture-coherence-20261101-r103.md`,
SHA-256 `084e12892159d2ed9b503a4691442fe8b2975b216270767c0a3d01d052526156`.
Assignment: R103 Rust source lane; handoff revision 1.
Parent: original source effect hygiene and logical-occurrence obligations.
Outcome class: implementation of a test-only comparison repair plus provisional
source-native observation; the R102 source/capture failures are not closed.
Role requested: Luna/high implementer. Observed model/effort: UNKNOWN (runtime
metadata unavailable). Worker state: STOPPED; no descendants.

## Exact paths and hashes

Only these assigned paths were written by this lane:

- `crates/yu-solver/src/candidate_effect.rs` SHA-256
  `3484817594e72e7faa259177139057e221356edccb6cdf53df8074add3fbff62`.
- `crates/yu-solver/src/candidate_scheme.rs` SHA-256
  `bf8f5c80ce2761dc2a1235d2e02e348a91bc9e8965653db26b9abd4c8d6ca631`.
- This handoff, SHA-256 `TBD_AT_FREEZE`.

`candidate_effect.rs` contains the preceding R103 source-trace changes already
present at assignment plus this lane's change to
`formal_permission_symbolic_effect_memo_trace_tolerates_missing_constructor_identity`.
That check now normalizes only decimal digits inside `TermArenaBrand(...)` in
the debug snapshot comparison. Term indices, keys, collection order and all
remaining debug shape stay compared, so the normalizer preserves the observed
alias/sharing structure. R102's failure printed otherwise identical snapshots
whose sole difference was arena brand 25 versus 26 at term index 268. This is a
test-observer repair, not a solver behavior change. It has not been executed.

The R103 test-only typed events currently expose constructor input, parameter
row, nested source Effect sites and paths, raw allocated permission rows,
memo hits/misses, delegated signature ports, canonical capture interning,
materialized captured Effect-row nodes and owner/root export. Their falsifiers
are wrong owner/occurrence/path, changed concrete members, omitted origins,
swapped ports, canonical-row substitution, and a capture node absent from the
returned owner graph. These events are provisional: this turn did not execute
them. Cleanup owner: Luna after independent review or replacement by an
approved source/native witness.

## Parent application and five R102 failures

The actual source constructor is `candidate_formal_annotation`: it reads the
HIR `SourceAnnotation`, selects the live parameter Value row, recursively visits
the annotation tree, creates nested effect rows/ports, records retained
permission metadata and only then publishes the formal domain and permissions.
Capture in `candidate_scheme::Capture::intern` canonicalizes endpoints and
materializes an Effect row node; owner graph publication associates that graph
with its source owner. R102's passing finite identity-observation case joined
distinct source paths, origin concrete operands, capture rows and returned
owner ports. It did not establish unequal transport or a connected consumer.

1. `formal_and_whole_annotation_share_tail_in_the_returned_effect_fiber` fails
   at `session.errors.is_empty()` immediately after source-root execution,
   before its manual effect constraint and graph capture. This is the earliest
   observed divergence. R102 logged no diagnostic/action identity, so the
   owning annotation/source constraint is still unknown. The sibling
   `whole_annotation_failure_preserves_the_preexisting_formal_tail` proves a
   transaction rollback case only; it does not identify this error. Do not
   infer that memo sharing or capture caused it.
2. `formal_permission_constructor_owner_domain_graph_export_join` observes
   raw allocation `r` equal to captured representative `q` for both source
   permission origins: `[(21,21),(23,23)]`. Reused R102 and earlier source
   transport evidence places the first missing transition upstream of capture:
   no source-attributed demand was shown reaching the same nested permission
   Effect row with `original_level > target`, retaining a qualifying source
   Parent and activating it, followed by a merge write that changes `r`'s own
   representative chain before joining independently materialized `q`. The
   contract's `r != q` assertion remains unchanged. Owner TODO:
   source-action/constraint owner must provide that exact demand, level,
   qualified pending Parent, activation and copy-side representative write.
3. `formal_permission_consumer_residual_observation` prints
   `consumer-returned-effect-forms=[]`. Reused reviewed source evidence shows
   the fixture recursively calls `f pair`; it contains no return/projection of
   `pair` connecting input `callback` to the result bound as `left`. There is
   therefore no demonstrated provider edge to the consumer. This is a fixture
   source-evidence gap, not permission to broaden the assertion or infer
   subtraction. Owner TODO: source owner must provide a result/provider path
   and an actual handler/subtraction consumer under an authorized source
   fixture; no such source change is in this lease.
4. `formal_permission_symbolic_effect_memo_trace_tolerates_missing_constructor_identity`
   differed only by `TermArenaBrand(25)` versus `(26)` for index 268, as the
   R102 log records. The leased comparison now ignores just those brand digits
   and preserves term indices and the rest of the snapshot. No execution shows
   the repaired check passing yet.
5. `views_keep_fresh_use_ownership_and_intrusion_rollback_restores_relations`
   reaches its route graph assertion, where every fresh-use route lacks a
   positive `Support` effect operand. R102 supplies no source-event to live
   constraint/propagation/captured route trace for this assertion. The first
   visible divergence is fresh-use route capture; the producer/consumer owner
   that should create the support endpoint is not yet localized. Preserve the
   assertion and rollback checks. Owner TODO: a source-qualified fresh-use
   trace must identify the expected support-producing constraint and its first
   absent propagation/capture edge.

The current typed observer is enough to inspect annotation-to-capture joins if
it runs, but it does not yet record the complete live-constraint propagation
and fresh-use route lineage needed to close failures 1, 2, or 5. It does not
prove an A/B premise or authorize cutover.

## Correspondence, evidence reused and checks

- Source annotation to native permission construction: statically inspected in
  `candidate_formal_annotation` and its recursive `candidate_formal_value_pair`
  / effect-port path; the current `FormalEffectSite` and `Origin` events are
  provisional instrumentation of that construction.
- Native capture/export: statically inspected in `Capture::intern`, captured
  `Node::Row` materialization, graph publication and the already-present
  owner export assertions. R102's finite identity observation passed the
  source-origin/captured-row/export-port joins for its identity fixture.
- Propagation and fresh-use: no R103 runtime trace was available to connect
  these source rows through the live worklist into the failing route or answer
  graph. The unequal-transport and consumer assertions remain OPEN.
- Reused/rejected evidence: reused the R102 independently reviewed execution
  receipt and its 45/5/2 result, the earlier consumer-residual handoff, and the
  source-transport handoff's exact strict-level/qualified-Parent/copy-side
  requirement. R102's green finite identity joins do not close those premises.
  Rejected any inference from the test-only observer's presence to its runtime
  trace, from a passing test to a theorem, or from the recursive source fixture
  to a provider or handler transition.
- Checks run: `git diff --check --` on the two leased Rust files passed.
  No Cargo command ran, per assignment. No tests or execution receipt were
  produced in this lane.

Direct dependency hashes rechecked against R103 contract and unchanged:
`shadow_apply.rs` `caeb837cd13b2e75e76fbed59dcc601e8c9d0a6a6a6f56f6959c0b0b9a98007f`,
`candidate_receiver.rs` `3ec1a45f5cdcfa5f5f28c2ef433c37d03322150a3155228f898e6fc5b77725cf`,
`lib.rs` `6eb6b5df29bda1d1bd1fecabcbc2cc6e85e777dda2045f1d1ab86084f64cd84f`,
`candidate_context.rs` `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905`,
`candidate_intrusion.rs` `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97`,
`crates/yu-solver/Cargo.toml` `aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed`,
root `Cargo.toml` `a8852982d5a3ff4d159aa546767b217000d50c9ff8617ac139700885bf5b090a`,
`Cargo.lock` `de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5`,
and HIR `module.rs` `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646`.

## Boundary and next related step

No source behavior, effect semantics, expected output, diagnostic, source domain,
or protected assertion changed. Mathematical closure, source/native
correspondence, semantic approval, whole-language A/B and production remain
OPEN. No new source-qualified counterexample is claimed. No cutover follows.

Exact next in-envelope step: obtain the missing diagnostic/action identity for
failure 1 and source-attributed strict-level/qualified-Parent/copy-side evidence
for failure 2; identify the support-producing live constraint and first lost
edge for failure 5. Failure 3 requires the separately owned source provider and
handler evidence. Then Luna can decide whether one exact Cargo invocation is
still admissible under the fixed gate; this lane did not spend it.

Changed repository paths: the two Rust source paths above and this handoff.
No generated or scratch output was created; no Cargo process ran. No other new
path is known from this lane. Writes stopped at this handoff; no descendants
remain. No commit-ready milestone, independent review, execution receipt or
primary acceptance is claimed. Frozen handoff ID:
`effect-permission-capture-coherence-r103-source`, revision 1; its frozen-byte
SHA-256 is reported by the submitting worker alongside this file.
