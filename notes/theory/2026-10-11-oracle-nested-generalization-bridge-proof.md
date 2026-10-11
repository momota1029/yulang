# Oracle nested generalization bridge: exact source premises and stopping point

Date: 2026-10-11
Status: frozen, unreviewed research derivation; H remains OPEN
Claim class: source-derived constructor/consumer facts and conditional selection/export lemmas; neither a complete local hygiene proof nor a source-qualified counterexample
Primary baseline: `a92fc1c8eeb73eb2718a91251d329e7e7fa5c877`, branch `research/simple-sub-intrusion`
Oracle checkout: `/tmp/yulang2-oracle-read`
Oracle revision: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Exclusive output lease: this file only; leaf, no delegation
Budget: Sol/high, 45 minutes, static inspection only; no compiler executions, probes, tests or builds

## 1. Frozen objective, original theorem and candidate

The governing sources are
[annotation hygiene integration](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–5, [contextual admission](../design/2026-10-10-contextual-attachment-admission-design.md)
§6, [negative formal proof](2026-10-11-negative-formal-effect-source-proof.md)
§§1,5–6, [global Oracle proof](2026-10-11-oracle-global-effect-hygiene-proof.md)
§§1–5 and [nested falsification](../progress/2026-10-11-oracle-effect-nested-scheme-falsification.md)
§§1–3. The primary supplied the global proof's independent PASS. That review
does not independently review this note or close H. General negative concrete
admission remains disabled. Top-level inference principles §§1–5 control
normal inference and necessary abnormal safety.

The unchanged parent H quantifies over every Oracle source program in the
original successfully lowered domain, every successfully lowered
composed-negative concrete annotation occurrence, its original lexical scope
and binders, every actual copy/instantiation, and every actual call/output
route involving that occurrence. Authorized subtraction removes only its
attachment-qualified contribution; an independent same-family contribution
survives. Symbolic tails remain connected, and every current/future concrete
lower reaching the relevant receiver encounters its actual retained check.
Original occurrence, attachment, scope, provider/call binder and correlated
residual lineage remain identified through copying and generalization up to
the actual consistent fresh-use renaming. Incorrect lowers must encounter
authentic errors and safe nonpublication. Successful suspension preserves
accepted dependencies. This packet neither narrows those quantifiers nor
adopts a provider independently for checking and output.

The local task fixes the candidate tree and calls from nested falsification §1:

```yulang
pub act tick:
    pub ping: () -> ()
my f(cb:(() -> (() -> [tick] ()))) = (cb ()) ()
```

```text
B = Function(Unit, None, None,
      Function(Unit, None, [resolved tick], Unit))
```

Let f be the owner, cb its original formal, a the inner result row, E the
resolved nullary tick, sigma their original lexical scope, k1 the first call
and k2 the call of k1's returned Value. These are distinct identities.
Both result descents preserve the formal's Negative polarity. The source
contains no concrete callback provider body, second same-family contribution
or symbolic tail. Their universal H cases remain required. The exact source
text's successful parsing/resolution was not established in the preceding
packet and is not established by this static lane; constructor facts below
take the fixed tree and successful indicated lowering as their stated scope,
rather than presenting an executed source witness.

Required local conclusion: decide whether the inner ID is discharged or
sufficiently exported when pruned, or retained/quantified and consumed on the
actual delayed Effect/output route with its correlated symbolic/current/future
checks. Merely choosing one branch from the raw tree is insufficient.

Shared assumptions: pinned source bytes, valid arena handles, ordinary Rust
collection behavior, successful indicated constructor calls and nonwrapping
fresh ID allocation. No complete replay, coverage-root invariance, final
compact shape, selected quantifier, attachment/provider equivalence,
publication success or observation-preserving erasure is assumed. No Catch,
runtime operation elimination, global soundness/principality, artificial source
restriction, eager solving or new representation is introduced.

## 2. Actual paired construction and both application roots

All Oracle locators are relative to the checkout above.

From `annotation/constraints.rs::lower_value_bounds` (363–389), the inner
paired Function is exactly of the following shape; U+/U- are the actual paired
Unit bounds, and S+/S- denote the actual omitted-row bounds:

```text
S+ = Bot
S- = Row([], Top)                         // pure_effect_bounds, 492–499
q  = function_boundary_effect_stack_inner([E])
i  = fresh_subtract_id()                  // distinct from coordinate q
w  = PUSH_i(Set(E))
d  = POP_i with FILTER(Set(E))

I+ = Fun(U-, S-, Stack(q+,w), NonSubtract(U+,d))
I- = Fun(U+, S+, Stack(q-,FILTER(Set(E))), U-)
B+ = Fun(U-, S-, S+, I+)
B- = Fun(U+, S+, S-, I-)
```

The concrete constructor and declared fact are 451–470,590–620,657–690.
`connect_value_detailed` (124–137) emits B+ <= C- and C+ <= B-, where C is
cb's actual Value coordinate. The outer node returns only its immediate
omitted-result-row vector, hence []; it does not return the inner vector d.
`lambda.rs:1278–1307,1571–1596` therefore supplies no cb call predicate,
public upper or erased upper for this candidate. No public-annotation
reconstruction branch is activated by that empty predicate.
`mark_lambda_param_call_predicate` (919–936) cannot supply d.

For each call, `tail.rs::make_app_with_origins` (535–627) independently
allocates result Value Rj, result Effect Aj and invocation Effect Jj, and emits:

```text
k1: C+  <= Fun(U1+, V1+, J1-, R1-)
    cb-evaluation-effect+ <= A1-
    J1+ <= A1-

k2: R1+ <= Fun(U2+, V2+, J2-, R2-)
    A1+ <= A2-
    J2+ <= A2-
```

Uj and Vj are the actual Unit argument Value and evaluation Effect from
`unit_expr` (tail.rs:729–736); no argument Effect is discarded in this
inventory. k1 has an Annotated local formal, so its return interface is bare
J1, not the separate unannotated-local-call subtraction branch (740–757).
The k2 callee is an App, whereas `local_callee_def` (844–850) accepts Var
only; its return interface is also bare. Neither call extends the latent
frame with d. Actual applications are created as App nodes at 626.

Given an admitted comparison of B+ against k1's demand, the FunctionReturn
child is I+ <= R1-. Given its actual replay against k2's demand,
`propagate.rs:210–269` emits these separate children:

```text
Stack(q+,w) <= J2-                        // FunctionReturnEffect
NonSubtract(U+,d) <= R2-                  // FunctionReturn
```

The omitted argument Effect S- is Row([],Top), not Neg::Bot, so this I+
comparison uses the ordinary swapped argument-Effect branch. It is incorrect
to substitute the pure-argument passthrough branch by looking only at the
word "pure". The positive I+ source constructor retains all four ports.

These last two children are **derived consequences of admitted Function
comparisons**, not claims that storing the original lower and upper guarantees
their replay. The production replay gate is explicit in §4.

`lambda.rs::wrap_lambda_param` (946 onward) uses
`tail.rs::lambda_output_predicate_vars` (1092 onward) to build the defined
outer Function; empty predicates leave its actual body Effect/Value unwrapped.
The recursive skeleton alternative likewise connects empty predicates via
the variable owners at lambda.rs:1183–1237. Neither is a source of a hidden
matching d on A2. No equality between body, skeleton, call or annotation
coordinates is assumed here.

## 3. Unit POP and live-machine checking have different owners

There is a direct source-derived terminal fact absent from the raw tree
argument. Upon processing the NonSubtract child above,
`propagate.rs:25–36` prefixes d and calls the ordinary derived-subtype owner.
`machine/entry.rs::canonical_subtype_constraint` (1092–1119) calls
`terminal_subtype_weights` (1783–1797). A nullary non-effect Con on either
endpoint is terminal by 1799–1816, and Unit is such a constructor. Consequently
the attempted U+ <= R2- constraint is canonicalized with empty weights.
The same holds when the compact collector visits the nullary Unit:
`compact_pos_id` passes the weight into `compact_con`, but there are no
type arguments on which d could survive.

This does not by itself prove safe semantic discharge of the Effect
permission. It proves that the Unit return's raw POP cannot be cited as an
exported latent Effect POP or as a check on q. That Value route is terminal;
the separate FunctionReturnEffect child remains the candidate carrier of w.

For live-machine checks, if the actual paired inner comparison I+ <= I- is
admitted, positive Stack normalization exposes q and its actual w before the
negative Stack normalization. The latter invokes
`constrain_pos_lower_by_filter(q+,Set(E))` before erasing the wrapper
(propagate.rs:11–56). This calls
`bounds.rs::constrain_type_var_lowers_by_filter` (3213–3255) on q.
The registered-filter lemma independently reviewed with the global note then
applies: current q lowers are checked at registration; new semantic q lowers
are checked at insertion (3285–3301); recursive Var lowers retain the check
on the encountered variable (3303–3360). It does not traverse Value Functions.
This is an actual operational activation conditional on reaching that
comparison, not a consequence of the declared fact alone.

No retained q filter table is serialized in Scheme. Live-machine invocation
of this check therefore cannot certify an arbitrary later scheme instance's
current/future checks. The imported lemma's machine boundary remains intact.

## 4. The actual demand replay and projection spine

Actual replay does more than enumerate the raw bounds. At C and then R1:

1. Lower/upper mutation uses `bounds.rs::add_lower_bound` (630–774) and
   `add_upper_bound` (815–925), including level-selected extrusion,
   subsumption, canonicalization, provenance and claim registration.
2. `cpk_lower_bound_replay_actions` (3381–3490) obtains prepared routes from
   `proof/mod.rs::prepare_replay_routes_for_lower` (9205 onward).
   `compose_prepared_replay_route` (9410–9537) selects a pair precisely when
   `requires_generic || !pair_upper_entries.is_empty()`. Covered claims may
   otherwise select incremental replay or SkipAlreadyCovered.
3. The lower replay owner skips a pair with no `pair_replay` (3450 onward).
   Selected work still passes canonicalization, exact-duplicate handling and
   evidence-only handling at `push_replay_constraint_or_prefilter`
   (3648–3711), then actual enqueue/application at 3832 onward.
4. `register_constraint_upper_replay_claims` (962–1030) may derive claims
   from qualified parents; it otherwise introduces a Direct claim. Even a
   Direct claim's label is not a proof that its coverage root remains
   uncovered along every relevant child/reduction route.

An additional source pass discharges the relevant **demand** coverage decision
without assuming that every raw lower is generally projectable:

- The original k1 and k2 constraints are fresh Var-to-Fun source producers,
  admitted with their own source origins by `make_app_with_origins`. Before
  any replay they have no claim-qualified parents. Upper insertion therefore
  introduces an original Direct claim for each exact demand producer
  (bounds.rs:1013–1030). The annotation C+ <= B- likewise originates directly
  from `connect_value_detailed`, rather than from a row reduction.
- A production search finds only row_effect.rs:523 inserting a live coverage
  state. `register_unweighted_row_reduction` (483–535) obtains its claim with
  `try_original_upper_replay_claim_transaction` for that *row constraint's*
  producer. The transaction (constraints/mod.rs:1717–1810) keys original
  claims by bound record and producer. The demand producers' immutable
  upper endpoints are Fun, so none can be the Var-to-Row producer of this
  reduction. Structural ancestry does not change that producer key. A
  sibling argument's pure Row can create its own covered root, but cannot
  cover these original Direct roots. Later additional parent admissions
  leave the original uncovered demand root available.
- Consequently, when the relevant live lower and demand upper meet,
  `any_uncovered` is true for at least that Direct root, hence
  `requires_generic` is true and `pair_replay` is present (proof/mod.rs:
  9450–9537). B+ and I+ are Function lowers. They are neither terminal,
  trivial self-variable pairs nor eligible for the Var-to-Var evidence-only
  shortcut (bounds.rs:3814–3830). An exact duplicate reuses the same semantic
  constraint; its original admission is queued by entry.rs. Successful
  normal drain therefore emits I+ <= R1- and the two distinct k2 return
  children in §2. The same argument reaches the paired inner check in §3.
- Lower insertion does not invent a copy of I+ or q here. Oracle extrusion
  traverses the existing type nodes and lowers encountered variable levels
  (`bounds.rs:4523–4725`); it returns the same node ID. In particular it does
  not rename i while traversing Stack/NonSubtract. These q and i still belong
  to the original a/sigma/cb tree. Positive Stack normalization of the k2
  return Effect emits the distinct-variable q+ <= J2- relation with left w.
  Its first insertion is not an alias cycle; a later identical insertion
  retains the same live semantic bound.

There is also a finite source-owned projection arm for this spine. The source
annotation lower B+ <= C- has an original source carrier and no covered row
claim. The two demand uppers have the uncovered Direct roots just derived.
For actual binary replays the registration owners emit
`RecordProofClause::ReplayConjunction` with the actual lower/upper records;
for structural FunctionReturn, FunctionReturnEffect and Stack normalization
they emit `DerivedUnary` pointing to the actual parent constraint
(bounds.rs:1178–1245,1925–1959,2916 onward;
entry.rs:1564–1588). `add_lower_bound` registers those actual parent clauses
when materializing the resulting lower (2332–2369,2476–2570). This includes
the q+w lower at J2; it is not a model-supplied clause.

Induct on that finite derivation arm. The source lower is included;
`eval_record_uncached` includes an upper with an uncovered root, and
`eval_root_coverage` tests that root's actual live-state set. A
ReplayConjunction includes the child when both actual premises are included;
a structural DerivedUnary includes it when its parent is included
(proof/mod.rs:11632–11923). The selected arm proceeds from the source lower
through C/k1, R1/k2 and Stack normalization, with no backward dependence on
the resulting J2 lower. Thus this arm is not a circular Visiting fallback.
Under successful normal completion of these fallible registration/preflight
owners, `project_lower` returns Included for that live J2 bound (or Unclaimed
before any ledger is necessary). Additional arms cannot turn its disjunction
into Excluded. No FailOpenIncomplete branch is used as proof evidence.

This is a bounded source/operational derivation for the specified tree and
normal completed owner sequence, awaiting independent review. It proves
neither arbitrary replay omissions nor a full bound census. Extending the
same argument along the source J2+ <= A2- relation gives a projectable q+w
producer at the body Effect: its original upper is Var, not Row, so its Direct
root also cannot acquire row-reduction coverage; replay weights compose w
with the source empty weight. Exact duplicate or existing direct q+w bounds
retain the same included arm. Actual top-level output compaction and
simplification are the next, separate obligation in §5.

## 5. Exact selection and export implications after that premise

The following additional owner facts delimit the next proof. The projection
spine in §4 supplies the body Effect's projectable q+w lower; it does not
supply the final compact/scheme invariant stated below.

**Projection.** `compact/collect/mod.rs:848–877` uses
`scheme_projectable_lowers_in_scope`, not every stored lower. The actual
query (`constraints/structural_kernel/access.rs:862–900`) excludes records
whose `project_lower` decision is Excluded. The proof evaluator
(`proof/mod.rs:9993–10125`) returns Unclaimed only when both its support
and exact-formula ledger are absent; otherwise it validates/evaluates those
clauses. Neither "ordinary source" nor existence of a lower permits assuming
Unclaimed. If the actual q+ with w lower is returned, collector 899–920 and
`compact_pos_bound_id` (1099–1130) produce a secondary covariant CompactVar
(q,w), rather than recursively substituting arbitrary q lowers. This is the
precise constructive projection implication.

**Actual definition pipeline.** Top-level schemes use
`analysis/session/instantiate.rs::quantify_component` (14–82), which calls
`analysis/session/generalize.rs::generalize_root_with_prepasses_and_metrics`.
Its owner is not just `generalize_type_var_with_boundaries`. It collects a
scheme projection with merge constraints (580–602), applies merge/dominance
work and re-enters collection (102–180), handles cast/role work, applies
floor simplifications (421 onward), expands aliases and simplifies (478
onward), cleans stacks (513 onward), and finally selects them (544 onward).
Finalization additionally applies actual scheme ancestors. The candidate's
final coordinates, fetch boundary and their levels must be derived through
that path; q's fresh allocation alone does not prove its final quantification.

**A sufficient selection fact, proved from the selector.** Fix a compact
snapshot at the selector after its empty-entry cleanup. If some structurally
covariant variable v is quantified, and its actual weight has an i entry with
a nonempty stack, `core/stack_ids.rs:23–49,72–100,176–180` selects i.
Selection requires `level_of(v) > boundary` and exclusion from non_generic
(generalize/mod.rs:900–918). The earlier dead-candidate pruning cannot remove
i while such a covariant PUSH is present (prune.rs:61–77); live-stack cleanup
also excludes it from the dead set (605–620). A declared Set(E) PUSH with zero
POPs and empty floor is not an Empty/spent/instantiated entry removed by
630–729. Selected i is absent from the stray set at generalize/mod.rs:205–238.
Conversely a filter-only negative occurrence of q, with no such positive
PUSH at a quantified coordinate, cannot select i. This fact does not prove
that simplification or ancestor processing preserves the antecedent.

Polar elimination checks whole-compact bipolar occurrence
(compact/analysis/mod.rs:41–56); the nested negative row tail and outer
positive q+w would protect their same variable if those occurrences both
survive. Co-occurrence/sandwich and the definition prepasses still require the
candidate's actual snapshot. No final compact tree is fabricated.

**Negative export.** If the inner I- ret Effect is compacted as the actual
Stack(q-,FILTER(Set(E))), `type_nodes.rs::compact_neg_stack_effect`
(545–583) emits an E Row prefix and compacts q with the *outer* weight.
The filter itself is not placed on that tail. Positive and negative Function
collectors carry weight into different ports (1–135). `compact/finalize.rs`
604–611 exports the actual Row/tail; 586–602,837–839 resets variable filters
to All. Thus literal cloning of a filter registration is not the export
route. A structural Row can be sufficient only after its actual provider,
residual and later-lower consumers are proved observationally adequate.

**Retained ID and root POP.** If final selection actually retains i,
`SchemeInstantiator::instantiate_scheme_parts` (instantiate.rs:620–647)
freshens it once, clones all scheme parts through the same map, and wraps the
cloned root with POP_i' count u32::MAX (770–787). This new root POP is real
consumer syntax. Upon actual Function comparison, return ports preserve its
context and argument ports swap it (propagate.rs:210–269); at a surviving
result Stack(q',PUSH_i'(E)), Stack normalization composes that prefix before
the carried root POP. The directed count formula gives the pre-guard pair
(MAX-1,0) for this single PUSH; no active i' PUSH remains in that calculation.
Alias normalization/capping and right/left mixing are additional operational
owners, not type equalities imported from this count equation. Distinct j
entries are unchanged by the exact i' lookup. The formula does not establish
the source's independent contributions, whole provider compatibility or
complete residual observation.

The **first remaining unprovided premise** is the full source-owned final
compact invariant at `quantify_component` for this candidate: after its
actual output connection, level changes, recording-merge projection,
negative-Function/row merging, simplification and ancestor processing, either
(i) a covariant quantified coordinate still has the correlated i PUSH and
its actual negative contract survives, or (ii) the transformations that remove
it have discharged or sufficiently exported its complete observation. The
body lower established in §4 does not decide that invariant. In particular,
the annotation upper B- and the first-call demand are both collected at C;
the latter refers to R1, whose upper is k2's demand. Negative Function merging
therefore sees both the annotation's q/filter contract and the inferred J2
contract. Treating the callback argument as the annotation B- alone would
discard a real owning input before this seam.

Pruning also has an exact owner: `without_ids` preserves the global filter
(poly/types.rs:444–455), while `prune_dead_subtract_weights_in_type`
(prune.rs:504–557) removes the chosen entries throughout all Function ports.
There is no owner here that automatically converts the absence of i into a
proof of safe discharge. Neither alternative (a) nor (b) is therefore
established for the fixed source candidate by this packet.

## 6. Economy audit and next owner

The prior global live-machine/copy route and nested predicate route both left
actual generalized observations unproved. The present method traces real
application children, terminal erasure, replay selection and the ordinary
definition prepasses. It establishes additional owner facts but does not count
a conditional selection lemma as progress closing H.

Audit under compiler-engineering's proof-obligation economy: checking and
preserving the selected ordinary nested annotation through actual
generalization/use is A/B. Recovering source attachment/provider incidence
from an equal compact row would create D debt; the paired source constructor
and application roots already know their own identities. Oracle's current
projection/coverage proof must establish its own observation-preserving
omissions; retaining another guessed permission or adding a reconstruction
checker would assume the disputed fact. No scope restriction or new compiler
certificate is proposed in this lease. Independent same-family and symbolic
tail cases cannot be obtained by choosing independent witnesses for this
closed source.

One next action: primary assign the definition compaction/negative-Function
merge owner to establish the final compact invariant in §5, using the exact
body projection arm from §4 and both C uppers. Preserve q/i/a/sigma/cb/k1/k2.
Then apply the selector facts and prove Row/root-POP current/future consumption.
Fresh independent review of this note remains primary-owned.

## 7. Checks, resource use and runtime

Commands were static bounded cat/sed/rg owner reads and SHA-256
snapshot/recheck. No Oracle/Yulang execution, executable checker, Cargo,
test, build, benchmark, network lookup or child delegation ran. No compiler,
test, design, rule, config, task/index/theory-status or other leased file was
edited. Initial read-only Git orientation checked branch/revisions/status;
no Git mutation occurred. The requested prohibition was on Git changes.
Some early large read captures were truncated; decisive owner excerpts were
reread narrowly. Guessed nonexistent simplify/definition paths produced
read errors and were replaced with the actual source paths.

Final static checks: no trailing whitespace was found; all 31 listed
dependency hashes were identical across the note-write/freeze recheck. An
initial hash comparison used a truncated capture and was discarded; the
full-budget recheck supplied the byte-stability result.

One leaf reasoning assignment, at most three independent short read processes
in an early batch, then sequential lightweight source reads; no heavy CPU/RAM
job. Numerical aggregate CPU/RSS was not instrumented. Wall-time cap was
45 minutes and was not expanded; primary heavy-verification budget consumed:
zero. Static note whitespace and dependency-byte stability checks are recorded
in the handoff. Source compilation/acceptance, actual solved graph and
projection closure, complete generalization/copy/extrusion/intrusion, symbolic
and independent-family cases, complete Call, error publication, soundness,
principality and F5 cutover remain unverified.

Requested runtime: `gpt-6.1-sol/high`, normal prover leaf. The project role
is registered and its model/effort keys are absent; defaults are Sol/high.
Observed runtime model/effort: unknown, since effective metadata was not
provided. No Astra, override-effect or reload claim. No jobs were launched
by this leaf.

## 8. Dependency snapshot and commit packet

SHA-256 snapshot of inspected bytes follows. Paths beginning `/tmp/` are
Oracle source files. The final recheck covers note construction/freeze;
comparison to the pinned primary revision remains the primary's integration
duty. No dependency was edited by this worker.

| Dependency | SHA-256 |
| --- | --- |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| `notes/design/2026-10-10-contextual-attachment-admission-design.md` | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `notes/theory/2026-10-11-negative-formal-effect-source-proof.md` | `262c2569935c30a369846f50fede295d7f024677dca203b5d11e56ed6484f856` |
| `notes/theory/2026-10-11-oracle-global-effect-hygiene-proof.md` | `6ac3f9665f89633adb4a7feacaee79abfddab693eed2c5078241e51df9545df1` |
| `notes/progress/2026-10-11-oracle-effect-nested-scheme-falsification.md` | `fd6cb9ea14adb8bbe873d118dae3e52bf498696d9caf37be2155c346e6b86ecb` |
| `/tmp/yulang2-oracle-read/crates/infer/src/annotation/constraints.rs` | `3c0482d4549a2bfc7e651a6b2cc15fa4e70488fe8f68fcbfca34c1bfb72920db` |
| `/tmp/yulang2-oracle-read/crates/infer/src/lowering/expr/lambda.rs` | `2e0206bdcfdfbe98d13c12eec7ba8f7964383bc08c92947352ad370754024db9` |
| `/tmp/yulang2-oracle-read/crates/infer/src/lowering/expr/tail.rs` | `ac406b309fbb0ba558a18e37aba63a8e7ffeabbc377a111566b1f97d786f93b8` |
| `/tmp/yulang2-oracle-read/crates/infer/src/constraints/machine/propagate.rs` | `8695fa5d7dfac805cd7d66e9e0760c8c298002b952b0cd8a43dcd1f8eb6f7086` |
| `/tmp/yulang2-oracle-read/crates/infer/src/constraints/machine/bounds.rs` | `c300c8c0c495da46822e1e1df38b833a6bffe5f3707642ae2cd26910b0608df7` |
| `/tmp/yulang2-oracle-read/crates/infer/src/constraints/machine/entry.rs` | `00c70ca0938b24d4d2dd38de6598fe54217aebd28150ac279b52839046b340b8` |
| `/tmp/yulang2-oracle-read/crates/infer/src/constraints/proof/mod.rs` | `bc0f3fbcf8f5ed01245e74283d3fd9cb13aa1713aff252a1847fde76b11b8e03` |
| `/tmp/yulang2-oracle-read/crates/infer/src/constraints/structural_kernel/access.rs` | `ad90bc1444be22df6080c7131ef49fedace884178c375af84ecb09416b38740f` |
| `/tmp/yulang2-oracle-read/crates/infer/src/constraints/row_effect.rs` | `080472bb5dcb3f724e808ff745c6fba304cc7ea2574b8f8eb3e3466964e937c2` |
| `/tmp/yulang2-oracle-read/crates/infer/src/compact/collect/mod.rs` | `828fa02521e2426297a9369df2fd9ef1560b7403a668ddfe881063ef16bdfd40` |
| `/tmp/yulang2-oracle-read/crates/infer/src/compact/collect/type_nodes.rs` | `96dc38a9a05c447f019bb0421e0b37057d283026ba87bce121bb33959b0d8ab2` |
| `/tmp/yulang2-oracle-read/crates/infer/src/compact/analysis/mod.rs` | `9c5e7a863f25ad94b10b7c7865af523e30c6ac361847f20f58307f1025432463` |
| `/tmp/yulang2-oracle-read/crates/infer/src/compact/analysis/occurrence/mod.rs` | `7bf082236f7c90a33fe9d0084dc3d993d3528bb5a272a44265df8f27728e46a2` |
| `/tmp/yulang2-oracle-read/crates/infer/src/compact/analysis/sandwich.rs` | `8935b5f295e6c6bda2838385ac1fca8298fe964061a7c6d800f612b2bbcd16f2` |
| `/tmp/yulang2-oracle-read/crates/infer/src/compact/finalize.rs` | `53a2452b109ddb461d98f6124d410fa2e771e700e272084f3b83ed87b4f3d272` |
| `/tmp/yulang2-oracle-read/crates/infer/src/generalize/mod.rs` | `03bfda4e4997347b59483de96eca652b67477639fc363e0890d546d2cf36fcef` |
| `/tmp/yulang2-oracle-read/crates/infer/src/generalize/core/stack_ids.rs` | `adb9cd35d483af62ea0c3ebc572b9a0535761f3bfb99aedad49b371833b95f8f` |
| `/tmp/yulang2-oracle-read/crates/infer/src/generalize/core/prune.rs` | `05e6d343c90f1bbc77def8e50f9acb746451ceb3889bb50dd17342621afba26d` |
| `/tmp/yulang2-oracle-read/crates/infer/src/generalize/finalize.rs` | `a8e5a1c8e6ad57d1fac7e25a1ab6a329093e5c76e6d84c0625c124c349f07492` |
| `/tmp/yulang2-oracle-read/crates/infer/src/instantiate.rs` | `876ede0627a1ac64b155d3d7896a386ac1fa81d8814c40c77a0f3893128a9b2c` |
| `/tmp/yulang2-oracle-read/crates/infer/src/analysis/session/instantiate.rs` | `bf21175f47df78f35f2070fea51b3483d59a91ac4a606bace9e24f32878c2d19` |
| `/tmp/yulang2-oracle-read/crates/infer/src/analysis/session/generalize.rs` | `ed946b9ffb15f40c1fd721d8b2cb0907a6540c21d0bf690f784577307660e64a` |
| `/tmp/yulang2-oracle-read/crates/infer/src/constraints/directed_weight.rs` | `de71ae7ed5a5aed22f3e5d35ca0ebcd52872ff965fcc22523a662cffdd6f28db` |
| `/tmp/yulang2-oracle-read/crates/infer/src/constraints/mod.rs` | `ad3cf5fd60462cb1a08ef1a5d6fc57c4fd640148597bc3b331d09729616d8392` |
| `/tmp/yulang2-oracle-read/crates/poly/src/types.rs` | `9211e62291b82e71e1b78763b83fe9f1d81e0fe4396d9e12d42e9a4a9b13b47c` |

Commit packet:

- Exact leased/change path: `notes/theory/2026-10-11-oracle-nested-generalization-bridge-proof.md`; frozen at handoff, writes stopped.
- Baseline: `a92fc1c8eeb73eb2718a91251d329e7e7fa5c877`; Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none authored; inspected snapshot above, freeze recheck in handoff. New inspected owners include entry.rs, proof/mod.rs and the analysis/session definition prepasses. Baseline/dependency acceptance remains primary-owned.
- Review: unreviewed research-only derivation. Neither branch for the candidate, H, source counterexample, complete Call, soundness/principality nor admission/implementation is certified.
- Checks already run: exact static source reads, hash inventory/stability and leased-note whitespace inspection; no executable inference verification.
- Proposed checkpoint: `research: trace Oracle nested call and generalization bridge premises`.
- Shared-record deltas left for primary/curator: record terminal Unit POP erasure, the bounded uncovered-demand replay/projectable-body arm, and the actual top-level definition prepass owner; replace a guessed direct generalize-type-var route with quantify_component's route; assign the final compact/negative-Function merge invariant before applying the conditional selector/export facts. Keep the original H and all dependent parent gates OPEN. No shared record is written here.
