# Frozen Oracle inferred signatures: call producers and coverage limits

Date: 2026-10-06
Status: frozen, independently compiler-referee-reviewed research-only historical characterization
Yulang3 baseline: `758fe982d3d37541bee26614f72301daba9e4e6a`
Branch supplied by primary: `research/simple-sub-intrusion`
Frozen Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`, `/tmp/yulang2-oracle-rebuild`
Exclusive lease: this note only
Semantic and implementation authority: none
Review: compiler_referee PASS on content SHA-256 `5e1ced556b914e22de54bcfcc56609e0c13f28e5218edd54dded368e3015b0c6` before this metadata-only update; scope limited to cited historical producer/grouping/collector claims, bounded derivations and authority boundary

## Objective and authority

Locate the historical mechanism closest to the first missing constructor in
[original-profile applicability](2026-10-06-original-profile-applicability-derivation.md)
§5: original inferred-signature applicability/contribution formation, with
exhaustive inversion and forward/reverse coverage on one whole original row.
This pass separates source emission, historical marker grouping, and downstream
signature projection. Frozen Oracle is not semantic authority. This result is
not a source proof, theorem closure, or implementation authorization.

Current governing clauses read directly are [inferred call views](../design/2026-10-05-inferred-function-call-views.md)
§§1.1–5, [nested-block meaning](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
§§1–3, [directional protection](../design/2026-10-06-directional-inferred-effect-protection-addendum.md)
§§2–4, and [source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
§2, the opening source grammar of §3, §6.1, and §§8–9. Source formation must
retain the shared inferred contract, original scopes and `xi=(nu,K,D)`;
admission remains independent of the pending comparison. The selected upper
output receives directional protection without back-protecting provider lowers.
The exact nested block returns the captured local function value. No language
meaning is selected or reopened here.

The previous whole-tuple, producer follow-up, solver-mechanism and original
source-producer archaeology notes were read first. Their identity, annotation
feedback, solver transfer and partial provenance traces are retained rather
than rerun as independent findings. The new evidence is the exact historical
marker grouping/frame selection and the signature collector's loss of
occurrence multiplicity.

## Hypotheses and claim class

H1: the twelve historical files in the hash inventory equal their pinned Oracle
blobs; the nine direct current documents equal the Yulang3 baseline. Verified
byte-for-byte. Established results here are revision/byte identity and the
cited field assignments and branch structure.

H2: a historical lowering trace reaches the cited defined-parameter and ordinary
application routines with resolved local `DefId` and live endpoints; allocation
and subtype submission complete. This is a candidate execution premise, not
acceptance of the surface candidate or a solver-soundness claim.

H3: for the local marker invariant, the selected frame is initially empty and
remains the same; its map/list are changed only by the cited unannotated-call
routine and ordinary frame initialization. For projection calculations, the
supplied compact bounds/shapes are available and projection admission succeeds.
These are explicit bounded state premises; no completed source row is assumed.

Claim class: bounded historical characterization, with conditional local
derivations under H2/H3 and a minimized representation witness. There is no
conditional theorem asserting current profile formation. Current whole-row
existence, exhaustive source licensing and admission remain unverified.

## Historical producer, grouping, and signature construction

All code locators are relative to the pinned Oracle tree.

1. **Parameter input and application demand are actual source producers.**
   `crates/infer/src/lowering/expr/lambda.rs:644–736` allocates each formal's
   live `TypeVar`, connects annotations/patterns, and installs a Defined frame.
   Annotation absence produces `arg_eff=Neg::Bot`, no annotation effect
   contract, no public/erased callable upper and `Unannotated` call-return state
   (`:1244–1264`; `expr/constraints.rs:31–33` implements `never_neg`).
   `expr/tail.rs:535–563` allocates result/call endpoints and emits
   `Pos::Var(callee.value) <: Neg::Fun(actual.value,actual.effect,returnEffect,resultValue)`.
   This uses the actual operand endpoints; it does not first reconstruct
   them from a solved signature. The call origin is submitted to the machine.
   Application expected provenance follows that submission (`:564–586`),
   as established by the prior archaeology.

2. **The nearest inferred contribution grouping is a frame/formal map.**
   `lowering/local.rs:179–195` initializes
   `unannotated_call_subtracts: FxHashMap<DefId,SubtractId>` and separate
   output/latent weight lists. `expr/tail.rs:740–798` first requires a resolved
   local `Def::Arg`, `Unannotated` return state, and a selected Defined frame.
   At the first successful lookup miss for that `DefId`, it allocates one
   subtract ID, declares an Empty fact against that call's effect variable,
   inserts the map entry and adds one pop to the frame list. Later calls
   finding the entry reuse the ID. Each successful call still gets its own
   positive and negative push wrappers on its own call-effect endpoint.
   Reuse does not redeclare an Empty fact for each later effect variable.

3. **Frame ownership is explicitly conditional.**
   `expr/tail.rs:801–830` begins with the formal's introduction frame. With a
   currently active Defined frame it normally chooses the innermost Defined
   frame, but chooses the introduction frame when the call crosses an inner
   active defined skeleton. Without a current Defined frame it chooses the
   introduction frame only inside a sub-syntax scope; otherwise it returns
   `None`. The introduction frame is assigned at `:832–842`.
   Defined lowering registers an active skeleton when `self_value` is present
   (`expr/lambda.rs:745–775`). The local-binding producer supplies
   `Some(recursive_value)` (`expr/block_local.rs:545–570`) and passes that
   argument through its defined-lambda path (`:866–896`). This is the exact
   historical condition relevant to a captured outer formal in an inner local
   definition. Full parser/dispatcher acceptance and the complete live stack
   for the surface candidate are not established in this pass.

4. **Lambda synthesis exports a Function lower from those inputs.**
   `expr/lambda.rs:946–975` constructs a positive Function with selected
   argument, annotation argument-effect port, and body output ports.
   `lambda_param_public_arg` normally returns `Neg::Var(param.value)`
   (`:978–1038`). The observed-call replacement path requires
   `call_erased_used`; the unannotated absence branch has no erased upper,
   and the application records observed uppers only behind that erased-upper
   guard (`expr/tail.rs:603–613`). Thus unannotated calls still constrain the
   live formal through the ordinary machine, even when they are not entered
   in the annotation feedback list. Under the stated absence/ordinary path
   premises, that list is not an exhaustive inventory of such calls.
   `expr/tail.rs:1058–1073` combines Defined-frame and annotation weights and
   deduplicates them; `:1092–1113` wraps both body effect and body value output
   when the predicate is nonempty. A marker therefore is not itself a single
   typed output-effect occurrence inventory.

5. **Generalized signature collection is downstream projection.**
   Local generalization drains selection/subtype work before snapshotting
   (`expr/tail.rs:951–969`). `generalize/mod.rs:75–90` starts from
   `compact_type_var_for_scheme`; `compact/surface.rs:12–24` enters a legacy
   projection query and completes that query, with failure poison explicitly
   delegated to its gateway. `compact/collect/mod.rs:816–879` reads projected
   lower/upper bounds and records query failure. Negative projected bounds
   discard their record IDs in the fold (`:837–842`). Lower bounds fold with
   positive merge (`:898–921`); upper bounds fold with negative merge
   (`:938–950`). The Function branches preserve four recursively collected
   ports and polarity/weight routing (`collect/type_nodes.rs:13–23,114–124`).
   `CompactFun` itself has only those four fields (`compact/mod.rs:541–546`).
   This is a representation formed from accepted projected bounds, not a
   pre-query source rule giving every original contribution its slot witness.
   Historical projection queries are not asserted identical to current `Q`.

## Conditional local derivation and smallest representation witness

For a fixed selected frame under H3, let `Calls_d` be the successful executions
of the unannotated-call routine for one formal `d`. Induction on this routine's
execution sequence gives:

```text
Calls_d empty     => no map entry allocated by this routine for d
Calls_d nonempty  => exactly one allocated map entry s for d in that frame
each c in Calls_d => wrappers Push(s,Empty) on that c's own effect endpoint
```

The first call inserts `s` and the pop; every later call takes the existing
entry branch. Inverting an entry newly allocated by this routine recovers a
first successful call and its branch predicates. It does not recover all
individual call origins from the map: the key has no call occurrence, output
position or receiver. A different selected frame can allocate another `s` for
the same `d`. This is exact forward/reverse accounting for one historical
routine under H3, not exhaustive inversion of all source signature rules or
current applicable slots. It neither licenses `Slots(beta)={(frame,d)}` nor
identifies `Empty`/push/pop with current protection semantics.

The smallest multiplicity discriminator needs one versus two equal Function
shape entries. For any supplied `CompactFun F` with four fixed ports, compare
the compact merge inputs `[F]` and `[F,F]`. In
`compact/merge/entries.rs:288–307`, the first entry initializes the accumulator
and every further Function folds into its four ports; the result is a single
Function. Each duplicate port merge returns the unchanged port by the equality
branch of `compact/merge/mod.rs:151–161` (the preceding empty branches also
return the same empty value). Thus both supplied lists produce exactly `[F]`.

This analytical witness refutes recovery of occurrence multiplicity from that
merged shape alone. It does not prove two distinct current slots are required,
that a historical solver necessarily admits both duplicate bounds, or that
every upstream provenance sidecar loses them. It is not a language
counterexample or executable mutation. The smallest difference is one extra
equal shape entry, with the same four endpoints and no changed semantic row.

## Forward/reverse coverage test against the current missing constructor

| Required interface | Historical evidence | Exact remaining gap |
| --- | --- | --- |
| Licensed source exposure produces its contract obligation | Application emits a Function demand using the same live callee/actual endpoints | This supplies unsolved constraints, not every original slot/contribution |
| Invert every original applicable witness to its source constructor | Marker allocation can be inverted locally under H3 | Its map groups calls and has no complete typed-position/witness inventory |
| Relate each contribution to its original slot without painting provider lowers | Historical call wrappers, frame/formal grouping and separate Function lower synthesis are concrete | No correspondence to current seed, `beta`, upper occurrence and contribution is established |
| Preserve forward and reverse coverage on one whole original row | Shared variables and one projection snapshot retain symbolic identity | No independently interpreted current whole-row relation, providers/world kernel, admission or completion follows from snapshot identity |

The closest historical mechanism is the source application/parameter/lambda
constraint producer with frame/formal grouping, followed by projected signature
collection. The collector consumes bounds; the grouping consumes eligible call
executions. Neither cited structure furnishes the missing exhaustive
original-signature licensing judgment. This is bounded evidence about these
paths, not repository-wide absence. Other historical mechanisms could refine
the correspondence; none is excluded by this search.

## Independence, checks, coverage, and stop

Frozen source assignments are independent evidence from the current stipulated
transition checkers. A binary built from this source would share the same
lowerer/solver assumptions; agreement would not independently prove its source
rules or the current language semantics. No checker, executable Oracle,
compiler build/test, mutation, random seed, finite input range, performance
sample or Git mutation was used. Only the leased note was written.

Commands/results: read-only revision/branch/path status reads; bounded `rg -n`,
`rg --files` and `sed -n` windows; Python byte comparisons against
`git show <pinned SHA>:<path>`, with Git blob SHA-1/SHA-256 computation.
All twelve historical and nine current dependencies matched their pins.
Several initial aggregate captures and one broad compact locator capture
truncated; decisive producer/collector/merge windows were subsequently read
without truncation. Speculative nonexistent locator files were corrected;
neither truncation nor failed locators supports an absence claim.

Resource use: lightweight read/hash processes only; no heavyweight process,
build cache, generated log or scratch output. CPU, peak RSS and total wall time
were not instrumented. Output lease consumed: one research note. Coverage is
the listed historical constructors, frame routine and compact collector/merge,
with no complete repository search. Broader source contracts were read only at
the governing sections named above, not as a fresh audit of that whole proof.

Failure conditions: changed blobs invalidate locators; a different dispatch or
live frame defeats H2; other writes or frame replacement defeat H3; projection
denial or changed port/weight state defeats the supplied merge analysis.
Unverified: literal-source acceptance and exact end-to-end trace, complete
solver/generalizer correctness, annotations and other call routes, recursion,
provider evidence, complete original profile, admitted rows and history,
whole-row soundness/adequacy/principality, and production conformance.

Recommended next action: construct the current original-signature licensing
judgment and its inversion directly over original source upper occurrences and
one shared row; preserve occurrence witnesses before any shape fold. Use the
historical map and fold only as correspondence checks, without adopting them
as current slot semantics. This completes the bounded archaeology pass;
writes stop at submission for frozen review.

## Frozen dependency inventory

Every historical file matched its commit blob; identifiers below are Git blob SHA-1.

| Oracle path under `crates/infer/src/` | Blob |
| --- | --- |
| `lowering/expr/lambda.rs` | `724b103cda8b4e2c457aacf0a674372fb191e3d6` |
| `lowering/expr/tail.rs` | `8289bfdc6a17b2469ae168ac7939d34813fda474` |
| `lowering/expr/block_local.rs` | `a406f4f9b7bc8e7e976014f2b348978e002a1191` |
| `lowering/expr/constraints.rs` | `bf76fa1a18b18e0ccce4b09c6652f22b31b89b11` |
| `lowering/local.rs` | `5b60e91edc1ff194486fe3292b53b292bf54d529` |
| `generalize/mod.rs` | `de356fed68ac159cea22c6cfac23ef334f1e942b` |
| `compact/surface.rs` | `0c79a4678c3e3bed588da0b620ff141722cd07a8` |
| `compact/mod.rs` | `17387c9e31580fab2e8dceee5f9544d0ede27639` |
| `compact/collect/mod.rs` | `2e0e8ac841e7240ee3b6b8db23915233f7ab832e` |
| `compact/collect/type_nodes.rs` | `3cc7de8d397ac1ea5398ef1ff7fb1e9827e6f65f` |
| `compact/merge/mod.rs` | `185f48489f32a4478c8a3b0cecb18f36d6227aaf` |
| `compact/merge/entries.rs` | `297fe155b7efc1320d5b102ede96dafc1b355199` |

Direct current dependencies, all matching the baseline, SHA-256:

| Path under `notes/` | SHA-256 |
| --- | --- |
| `design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `design/2026-10-06-directional-inferred-effect-protection-addendum.md` | `6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7` |
| `design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `progress/2026-10-06-original-profile-applicability-derivation.md` | `d66a7ec9a57c676668d0ad4531a1607594e681a59c17d0cf239e29cd7cd02905` |
| `progress/2026-10-06-frozen-oracle-whole-tuple-source-producer-correspondence.md` | `fcc23c134001e25f02a28a251c38ef083872b51458e39948fcfb3dc0c8652dae` |
| `progress/2026-10-06-frozen-oracle-missing-producer-followup.md` | `d211a365acca703b782e2fc936864b9c0c189a5861ce34729326c3f3b642d6ee` |
| `progress/2026-10-06-frozen-oracle-missing-producer-solver-mechanism.md` | `68249800e84b767860b76a88086bbe9321c060304065f408fea4afc2f32cd3f9` |
| `progress/2026-10-06-frozen-oracle-source-producer-archaeology.md` | `4f3cfff031dd9e5a90b5df3e2f7aded3535007f16ca5abd45c7892f6567a244b` |

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-frozen-oracle-signature-applicability-archaeology.md`.
- Baseline SHA: Yulang3 `758fe982d3d37541bee26614f72301daba9e4e6a`;
  Frozen Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none; all direct dependencies matched pinned blobs.
- Review status: frozen unreviewed bounded historical characterization and
  conditional local derivations; no independent review or semantic authority.
- Checks already run: bounded source windows/searches, revisions/branch/path
  reads, twelve historical/nine current blob comparisons and content hashes;
  no build/test/execution or Git mutation.
- Proposed research-checkpoint commit message:
  `research: trace Oracle inferred signature producers and coverage limits`.
- Shared-record deltas intentionally left for primary/curator: record historical
  frame/formal marker grouping, conditional frame ownership and downstream
  Function-shape multiplicity loss; retain original signature applicability,
  exhaustive inversion, same-row coverage, complete profile and independent
  admission as open. No shared task/theory/index/question record was changed.
