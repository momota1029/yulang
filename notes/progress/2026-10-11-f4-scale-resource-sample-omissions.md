# F4 scale witness omitted two boxed SCC sampling boundaries

## Finding

The focused `tests::f4_chain_scale_matrix_is_linear` run reported 12,006 resource
samples for `chain/1000`, while its exact expectation was 10,006. A bounded source
audit traced the 2,000-sample delta to two existing per-component calls in the
successful boxed SCC path:

- `ResourceBoundary::SourceDrafts`, after source-buffer reservation;
- `ResourceBoundary::AllDrafts`, while all drafts coexist before finalization.

The chain witness has `C = 1000` components, so these calls contribute exactly
`2C = 2,000` samples. The existing expected-count formula omitted both. The
coverage ledger also records these as two distinct named boundary kinds, while
its exact expected coverage omitted both. The calls and formulas predate the
current handoff diff; this identifies a source/expectation mismatch, not a
baseline test result.

Pre-write conformance review identified an omitted accounting term in the F4
scale witness expectations. The successful boxed component path samples source
storage after reservation and all coexisting drafts before finalization, as
authorized by F5 §26. These contribute exactly 2C samples and two named
boundary kinds; incoming event/scratch additions do not include them. The
correction preserves exact causal assertions and changes no runtime behavior or
semantic contract.

## Authority and disposition

F5 foundation §§26, 34 and 35 authorize named causal resource sampling and
retain the F4 resource contract. `rules/testing.md` requires expected values to
follow causal semantics and pre-write spec review. The spec-auditor approved
the narrow arithmetic correction before the expectation is changed. No runtime
sampling code or semantic contract is changed.

The source/count derivation is bounded to this witness and does not establish a
general inference theorem. Historical test behavior was not independently run
at the pinned baseline. Other previously observed scale failures remain
unadjudicated and do not authorize broad reruns.

## Evidence

- The focused chain test observed 12,006 against 10,006.
- The source audit enumerated the two unconditional per-component sample sites
  and confirmed the chain witness takes the boxed SCC path.
- The pre-write spec review approved adding checked `2 * witness.components`
  to the resource expectation and adding two distinct boundary kinds to the
  coverage expectation.
- No runtime behavior, sample sites, or semantic expectation is changed by the
  planned correction.
