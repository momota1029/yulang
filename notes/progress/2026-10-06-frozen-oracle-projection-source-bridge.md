# Frozen Oracle: source-rooted bounds at the signature collector handoff

Date: 2026-10-06
Status: frozen research-only source-window characterization; independently compiler-referee-reviewed, two minor citation/control-flow repairs closed
Yulang3 baseline: `5a8a83f77eb610848676e33093ed98e63dce0193`
Frozen Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`, `/tmp/yulang2-oracle-rebuild`
Exclusive lease: this note only
Semantic and implementation authority: none

## Objective and result

Trace the remaining solver-bound-to-signature seam near
`OriginalAssocType_X(beta,p0,j_call;s0,c0)`. The method is a bounded static
source-to-artifact audit, without Oracle execution or a supplied transition
checker. The source demand can remain reachable through replay, structural
child constraints and stored bound derivations. A projection entry can still
carry that bound's record identity and selection evidence immediately before
compact signature collection. The positive compact collector then explicitly
selects only `entry.bound.clone()` from that entry.

This identifies a **consumer boundary**, not global provenance destruction:
the graph and a separate generalized-witness collector retain selected
attribution. The new narrow result is the positive projection-entry handoff
and its connection to child-bound storage. It does not construct original
contribution typing, original slots, admission, or either licensing direction.

## Authority, dependencies and overlap

Current governing sources are [inferred call views](../design/2026-10-05-inferred-function-call-views.md)
§§1.1–5, [directional protection](../design/2026-10-06-directional-inferred-effect-protection-addendum.md)
§§2–4, and [nested-block meaning](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
§§1–3. The exact open leaf is the [Attach attempt](2026-10-06-attach-law-construction-attempt.md)
§§3–5; [main source generation](2026-10-06-main-source-generation-minimal-clause.md)
§6 separates footprint/incidence from local interpretation and admission.
The accepted same-source contract, original joint `xi=(nu,K,D)`, upper-only
protection, actual provider role/entry, Q independence and nested capture
meaning are retained. No historical mechanism selects successor semantics.

Prior-note overlap is explicit:

| Prior artifact | Already established interface reused here |
|---|---|
| [Application endpoints](2026-10-06-frozen-oracle-presolve-application-types.md) | Demand ports, post-submission argument-owned expected provenance; no repeated endpoint attack |
| [Function paths](2026-10-06-frozen-oracle-function-path-attribution.md) | Labelled children and distinct generalized path collection; no repeated pure-passthrough/path discriminator |
| [Signature applicability](2026-10-06-frozen-oracle-signature-applicability-archaeology.md) | Negative record discard, four-port collection and duplicate-shape fold; no multiplicity attack |
| [Claim-qualified attribution](2026-10-06-frozen-oracle-claim-qualified-signature-attribution.md) | Separate certificate-bearing witness capture after projection; no new certificate inversion claim |
| [Source boundary](2026-10-06-frozen-oracle-source-boundary-eligibility-mechanism.md) | Origin allocation and later ownership classification; classifier not retraced |
| [Solved observation](2026-10-06-frozen-oracle-solved-output-observation.md) | Later specialization joins; not inspected or used as a source constructor |
| [Solver mechanism](2026-10-06-frozen-oracle-missing-producer-solver-mechanism.md), [solver transfer](2026-10-06-frozen-oracle-source-producer-solver-transfer.md) | Demand upper insertion, conditional Function replay and weights; no stack-normalization attack |

## Hypotheses and claim classes

H1: the ten inspected Oracle source files equal the frozen blobs, and the
thirteen current direct dependency documents equal the stated baseline.
Byte equality and their identities were checked. This is established evidence.

H2: ordinary application demand admission returns with its source origin and
nontrivial constraint record retained. The demand is an upper of the callee
variable. This alone does not cause Function decomposition.

H3: an appropriate Function lower subsequently supplies a prepared, admitted
replay pair with retained replay provenance; a selected Function child is
nontrivial and reaches variable-bound insertion without subsumption/resource
failure. These are candidate execution premises, not accepted-source or
solver-correctness results.

H4: the relevant variable/polarity is visited by scheme collection, scoped
projection succeeds, and the selected bound is returned as a projection entry.
The source audit does not establish H4 for every application/port.

The result under H2–H4 is a conditional historical dataflow derivation. It is
not a current-language theorem or a complete source/profile characterization.
The one-entry witness below is a representation discriminator; its realization
as two admitted source programs is unverified.

## Exact producer-to-consumer derivation

Locators are relative to the frozen Oracle tree.

1. `crates/infer/src/lowering/expr/tail.rs:535–563` supplies source origin `o`
   to the callee-variable/negative-Function demand `r`. Canonical admission
   retains root origins, including additional origins on an existing record
   (`constraints/machine/entry.rs:1357–1425`). Variable-left propagation
   stores the demand upper with `BoundDerivation::Constraint(r)`
   (`machine/propagate.rs:99–152`). This reuses the already documented source
   producer, rather than claiming a new current slot introduction.
2. Upper-triggered replay enumerates lower records and, for a prepared pair,
   retains both lower and upper `BoundRecordId`s in `BinaryReplayDerivation`
   (`machine/bounds.rs:3582–3644`). Under H3's stated order, where the lower
   arrives after the demand upper, the lower-triggered route instead creates
   the prepared pair and retains both bound references in
   `BinaryReplayDerivation { rule: LowerBoundAdded }`
   (`:3422–3476`; call site `:727–735`). Application of replay actions calls
   `enqueue_replay_subtype` (`:3833–3848`); admission retains the derivation
   subject to its explicit budget (`machine/entry.rs:1165–1288`). Thus the
   Function comparison parent `q` can lead back through the demand upper to
   `r`. Its other replay premise is also retained: this is a graph with
   potentially several sources, not unique application ownership. Both
   insertion orders have these separate upper/lower-triggered routes; this
   note's H3 uses the lower-triggered route.
3. Function comparison creates separate child constraints `d_i` carrying
   `(q,FunctionArgument/FunctionArgumentEffect/FunctionReturnEffect/FunctionReturn)`
   (`machine/propagate.rs:211–269`; `machine/entry.rs:1427–1507`). When a child
   reaches a variable endpoint, the same propagation dispatch supplies
   `BoundDerivation::Constraint(d_i)` to bound storage. Lower insertion
   records the derivation and projection index (`machine/bounds.rs:630–711`);
   upper insertion records its derivation and producer claims (`:815–885`).
   `BoundRecord` stores owner, endpoint, weights and derivations separately
   from `WeightedLowerBound { pos, weights }` / `WeightedUpperBound { neg, weights }`
   (`constraints/mod.rs:2723–2733,3225–3233,3316–3324`). Equal semantic-bound
   keys can accumulate derivations (`:2511–2555`), so reachability is relational.
4. `scheme_projectable_lowers_in_scope` returns selected entries with
   `record`, `bound`, `reason` and `projection_evidence`
   (`constraints/structural_kernel/access.rs:862–896`). Excluded entries are
   absent; qualified entries carry selection evidence. The bound record is
   therefore still available **at this API**, before the compact consumer.
5. The positive `SchemeProjection` branch calls `compact_scheme_lower_bounds`
   (`compact/collect/mod.rs:833–834`). Its successful API result is mapped to
   `entry.bound.clone()` (`:864–874`), then passed to the lower fold
   (`:874,898–919`). That map does not pass the record, reason or certificate
   to the shape fold. The negative branch separately discards record IDs
   (`:837–842`), as already recorded by the signature note.
6. Function shape collection recursively places endpoints in the four fields
   (`compact/collect/type_nodes.rs:13–23,114–124`);
   `CompactFun` contains those four fields (`compact/mod.rs:541–546`). This
   retains structural field position and recursively represented type
   variables/weights. These routines receive neither the source origin nor
   the child derivation label as a Function-field association argument.

The conditional retained graph is therefore

```text
o <- r <- demand-upper b_u <- replay q <- child d_i <- child-bound b_i
                                                        |
                               projection entry(record=b_i,bound,selection)
                                                        |
                                      shape consumer selects bound only
```

Arrows on the first line mean retained predecessor references, not a unique
inverse or current typed path. The source root is retained in the graph;
selection identity stops being an explicit argument at the compact handoff.

The separate witness collector demonstrates why this is not global erasure:
it consumes the same projection API and explicitly keeps record and selection
evidence (`generalize/provenance.rs:218–280`), or negative record IDs
(`:281–285`). Its independently traversed structural paths and partial
whole-scheme coverage were already characterized by the earlier notes
(`:23–78,308–338`). This audit claims no new complete sidecar correspondence.

## Smallest local discriminator and stopping point

Let `w` be one supplied projected `WeightedLowerBound`. Compare one-entry
API payloads `[(b,w,Unclaimed,None)]` and `[(b',w,Unclaimed,None)]`, with
`b != b'`. At the positive collector's explicit map, both become `[w]`.
Consequently that map has no inverse recovering the input record identity
from its output alone. This needs one entry and one changed metadata field;
there is no duplicate-shape or occurrence-count mutation.

These are supplied representation inputs. Canonical bounds inside one machine
can share a record when owner/endpoint/weights agree, so this is **not** a
claim that both records coexist for one canonical key, that two source
programs realize them, or that whole collectors with different machines
necessarily return identical schemes. Equal subsequent collection additionally
requires the same shape queries, weights and remaining collector state.
The provenance sidecar can distinguish the records; dropping that sidecar
would be an unexecuted diagnostic mutation, not an observed Oracle behavior.

The exact blocker remains an original source introduction of
`OriginalAssocType_X(beta,p0,j_call;s0,c0)`. An intact historical predecessor
graph and a four-field compact Function do not interpret `s0` or type `c0`,
retain the required original joint semantic row, or identify complete
invocation contribution with an effect endpoint. Most of this route overlaps
prior traces, and the new consumer boundary leaves that premise untouched.
The lane stops here instead of constructing another equivalent attribution
probe. No repository-wide absence or impossibility result is asserted.

## Independence, coverage, checks and resources

Frozen source grounds the historical assignments independently of current
research notation. Its solver, query and witness collector share the same
historical representation and proof assumptions; they are not independent
semantic oracles. No checker or binary was executed. No seeds, enumeration
ranges, executed mutations, performance samples or test counts apply.

One lightweight shell/Python process ran at a time. Ten Oracle source files
were inspected, below the approximately fifteen-file source budget; no build,
test or Oracle run occurred. CPU, peak RSS and total wall time were not
instrumented. The assigned wall cap was twenty minutes. Early combined
context captures truncated; decisive source windows and dependency comparisons
completed without truncation. No completeness claim relies on omitted output.

An independent compiler-referee review found no blocking or major issue and
confirmed the bounded dataflow/discriminator. It identified two minor evidence
precision issues: the successful lower-fold locator was corrected to `:874`,
and the replay locator now matches H3's lower-arrives-after-upper order via
`LowerBoundAdded` (`bounds.rs:3422–3476`, call site `:727–735`). The reviewer
also checked all ten cited Oracle files against the pin and the prior-note
overlap. No semantic conclusion changed.

Read-only commands: `git rev-parse HEAD`, `git status --short`, scoped `rg`,
bounded `sed`, and Python byte comparisons against `git show <pin>:<path>`.
All twenty-three compared source/document files matched their respective pins.
No Git mutation, compiler edit, shared-record edit or child delegation occurred.

Failure conditions include trivial child admission, bound subsumption,
unprepared replay pairs, replay-provenance budget loss, changed source bytes,
projection exclusion/failure, a port not visited by the collector, and a
structural position absent from the final generalized shape. Omitted scope:
other replay/storage routes, source acceptance and realization of the witness,
complete projection/proof correctness, generalization transformations,
all typed paths, complete profiles/admission, and current soundness,
principality, adequacy or production conformance.

Recommended next action: derive the current original owner/view contribution
typing clause itself, using this exact handoff as a preservation audit once a
source-generated association exists.

## Dependency snapshot

The Git blobs below, plus their revision pins, identify exact checked bytes.
All direct dependencies were unchanged from their pins; no changed hash exists.

| Current dependency | Blob at Yulang3 baseline |
|---|---|
| `notes/design/2026-10-05-inferred-function-call-views.md` | `9493abd55e61dbc59de31f319c2ff9670204069a` |
| `notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md` | `a72d434fcc48f71da14f044d006096fdf7fb19d3` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `704048bc866d1638ef8811e2364a25e31c0ebb96` |
| `notes/progress/2026-10-06-main-source-generation-minimal-clause.md` | `457c924b807540685b24b656425c99e9dbe4fdee` |
| `notes/progress/2026-10-06-attach-law-construction-attempt.md` | `415e92ddc37d4e6cec6f3813516770f4cba309e2` |
| `notes/progress/2026-10-06-frozen-oracle-function-path-attribution.md` | `38945591b2c5c0170aa42e8d8be276568df02c7d` |
| `notes/progress/2026-10-06-frozen-oracle-signature-applicability-archaeology.md` | `f341b9e317928fb33f44e76d7c6e0fd0e618de39` |
| `notes/progress/2026-10-06-frozen-oracle-presolve-application-types.md` | `f68836a28fc27f896f253b4686273513ab9e02f8` |
| `notes/progress/2026-10-06-frozen-oracle-claim-qualified-signature-attribution.md` | `356385ed44652f83bd5a7418c1097dd25f7a4c4c` |
| `notes/progress/2026-10-06-frozen-oracle-source-boundary-eligibility-mechanism.md` | `09f5eb0efd153b6b69a44e11cbdbfcb04dce756d` |
| `notes/progress/2026-10-06-frozen-oracle-solved-output-observation.md` | `a89148214e5ccf2e865e72ee941f1778f9d0e20d` |
| `notes/progress/2026-10-06-frozen-oracle-missing-producer-solver-mechanism.md` | `a596d1fe319b08bf531ebbe313bbc6ee95288e17` |
| `notes/progress/2026-10-06-frozen-oracle-source-producer-solver-transfer.md` | `bb6e4e51f2f824f0e887738f58dde254fcbba28e` |

| Oracle source, relative to `crates/infer/src/` | Blob at Oracle pin |
|---|---|
| `compact/collect/mod.rs` | `2e0e8ac841e7240ee3b6b8db23915233f7ab832e` |
| `compact/collect/type_nodes.rs` | `3cc7de8d397ac1ea5398ef1ff7fb1e9827e6f65f` |
| `compact/mod.rs` | `17387c9e31580fab2e8dceee5f9544d0ede27639` |
| `constraints/machine/propagate.rs` | `d558e7b9c17d33e91c5bb39c4cd85ebbfa4a8b09` |
| `constraints/machine/entry.rs` | `d75544523281cc7f5c6f1778fbe25eb42b7dfe7b` |
| `constraints/machine/bounds.rs` | `365ed25a8b3b7e468a7a4e57159125be53209708` |
| `constraints/structural_kernel/access.rs` | `416ddcc2759c529d3b07fe34e7ebf2556d9e23a6` |
| `constraints/mod.rs` | `14860e3664a7ac05f7493f1d51fe69a6f34216e5` |
| `generalize/provenance.rs` | `62a70745be4d0e5e7880adec727216f188640b4a` |
| `lowering/expr/tail.rs` | `8289bfdc6a17b2469ae168ac7939d34813fda474` |

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-frozen-oracle-projection-source-bridge.md`.
- Baseline SHA: `5a8a83f77eb610848676e33093ed98e63dce0193`; Oracle pin:
  `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Dependency changes: none; exact checked blobs are listed above.
- Claim/review status: frozen bounded historical characterization and conditional
  dataflow derivation; compiler-referee-reviewed with two minor citation/control-
  flow repairs closed; non-authoritative.
- Checks already run: both revision pins, bounded source windows, source/document
  byte equality and blob/SHA-256 computation; final lease whitespace/status check.
  No tests, builds, executions or Git mutations.
- Proposed research-checkpoint commit message:
  `research: trace source-rooted bound handoff into Oracle signatures`.
- Shared-record deltas left for primary/curator: optionally record the positive
  collector's bound-only handoff and the retained separate provenance channel;
  retain prior overlaps and the exact `OriginalAssocType_X` blocker. No theorem,
  gate, profile, licensing, semantic-authority or production-status promotion.
