# Frozen Oracle: nested returned-function output consumer boundary

Date: 2026-10-06
Status: frozen research-only bounded source characterization; independent review pending
Yulang3 baseline: `46772a7a82826d945d1ca25ff666e61a32560bc9`
Frozen Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Historical checkout: `/tmp/yulang2-oracle-rebuild`
Exclusive lease: this note only
Semantic and implementation authority: none

## Objective, method, and result

Trace the exact candidate

```text
my apply f = { my step x = f x; step }
```

from local `step` construction/generalization through its returned reference
to the outer frame's collected `pop(s)`. The
[preceding transfer note](2026-10-06-frozen-oracle-source-producer-solver-transfer.md)
derived cancellation only if a particular wrapped effect port is consumed.
This continuation follows the nested source joins instead of assuming that
the application result effect directly occupies that outer output.

**Result:** conditional on the historical lowerer recognizing the indicated
ordinary binding/block route, local binding supplies `self_value` even for
this nonrecursive `step`. Its active Defined skeleton makes `f x` select the
outer `f` introduction frame, which receives `pop(s)`. The inner wrapper
finishes and `step` generalizes before the final `step` name is lowered. The
block forwards the returned name's value; the outer wrapper places its pop on
that **returned-function value** and on the block's computation effect. The
block's computation effect is not the latent effect of `f x`.

There is a concrete conditional consumer: a later comparison of the outer
positive Function against a negative Function forwards the pop-wrapped
returned value to its result demand. If that result demand eventually exposes
a negative Function, weighted comparison can forward the pop to the returned
function's covariant result ports. This investigation does not establish such
a demand for the exact definition alone, or survival of the original push
through local Scheme formation. Generalization can prune stack IDs and
instantiation can freshen them. The preceding transfer note's exact H3 path therefore
remains unproved; its missing premises are now localized to these stages.

Method: static producer/consumer inspection and conditional field derivation.
No source acceptance, CLI output, compiler execution, or self-assuming checker
is used. Current governing sources remain
[call views](../design/2026-10-05-inferred-function-call-views.md) §§1.1–5,
especially §3, and the
[nested-block addendum](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
§§1–3. Their selected captured-function meaning is retained. The main
minimal-clause §5, prior transfer note, multi-use continuation, and Oracle
crosswalk are current dependencies. Historical behavior selects no current
meaning or implementation permission.

## Hypotheses and claim classes

H1: thirteen decisive historical files and six current dependencies equal
their pinned blobs byte-for-byte. Verified; hashes below.

H2: the historical frontend presents the indicated source as one unannotated
outer formal, a non-record expression block containing ordinary local binding
`step` with one unannotated formal, and final ordinary name `step`. Names in
the inner body resolve to outer `f` and inner `x`. No explicit result
annotation, supplied parameter upper, method selection, or special binding
route changes these calls; lowering completes. This is a lowerer-input
premise. Parser recognition and accepted source coverage were not established.

H3: normal local generalization takes the Scheme branch, completes its
projection/compaction/simplification, and its returned-name instantiation is
admitted. The alternative pending-selection live-root branch is recorded
below. Exact resulting compact roots, quantified variables, surviving stack
IDs, and live external bounds are not assumed known.

H4: a later independently supplied negative outer Function demand reaches
the produced outer positive Function; its returned-value demand eventually
exposes the returned function's positive lower against a negative Function.
Bounds replay/structural children are admitted and not prevented by terminal
proof/resource failure. H4 is the missing consumer premise, not a fact derived
from the declaration or its printed scheme.

Established facts: H1 and the cited assignments and transfer branches.
Bounded characterization: the source joins and Scheme transport seams.
Conditional derivations: frame selection under H2, output placement under
H2, and possible consumer routing under H4. No independently reviewed theorem,
whole-program historical absence claim, exact-source acceptance, or current
semantic closure is claimed. H2–H4 remain candidate premises.

## Exact historical source joins

All paths below are relative to the frozen historical checkout.

1. **Expression block.** `crates/infer/src/lowering/expr/chain.rs:593–596`
   sends a non-record BraceGroup to `lower_expr_block`.
   `expr/block_local.rs:69–86` lowers its item list, then truncates locals.
   The ordinary Binding branch first lowers the binding, then the rest, then
   prepends a block (`:122–127`); a final Expr returns its computation directly
   (`:130–133`). H2 includes the exact syntax classification; these methods
   do not prove the parser produced it for the source bytes.
2. **`step` receives a self endpoint and active skeleton.** Ordinary local
   binding allocates `recursive_value`, installs its definition, and calls
   `lower_local_binding_body(...,Some(recursive_value))`
   (`block_local.rs:554–569`). One argument routes to Defined lambda lowering
   (`:866–896`, `expr/lambda.rs:244–268`). It pushes the `x` frame, remembers
   `before_frames`, builds a skeleton when `self_value.is_some()`, and records
   `ActiveDefinedLambdaSkeleton{before_frames,params}`
   (`lambda.rs:658–660,732–772`). This allocation is a historical construction
   detail; it does not assert source recursion or extend the selected meaning.
3. **Outer frame selection.** Let the outer `f` frame be index `j`, with the
   inner `step` entry starting at `j+1`. During `f x`, the current frame is
   `j+1`, and the inner active skeleton covers that one parameter. Hence
   `j < before_frames <= current < before_frames + params.len()` holds and
   `unannotated_call_frame_index` returns `j`
   (`expr/tail.rs:801–824`). The already characterized eligible return-view
   helper consequently records its `pop(s)` in the outer frame and emits
   positive/negative `push(s,Empty)` call-effect views. It does not add this
   pop to the inner `x` frame on the inspected route.
4. **Inner body anchor and wrapper.** Before final wrapping, the inner active
   skeleton receives links from the body effect/value and replaces the body's
   anchors with skeleton body endpoints (`lambda.rs:788–808`). Initial
   skeleton construction was made before the body with empty frames
   (`:750–767`); final output predicates are intentionally attached by the
   wrapper, according to the comment at `:794–796`. Active skeletons are
   truncated after body lowering (`:836–839`). Final Defined wrappers consume
   their parameter frames (`:852–863`). `wrap_lambda_param` produces a positive
   Function using that frame's output predicate (`:946–975`). Thus the inner
   frame has no selected outer `pop(s)` to attach at this stage.
5. **Local generalization precedes the returned name.** Binding replaces its
   local value with the completed public wrapper root and generalizes it
   (`block_local.rs:570–585`) before `lower_block_items` proceeds to the tail.
   `generalize_local_binding` drains selections/constraints first; if a
   selection still produces this local root, it stores no Scheme and returns
   (`tail.rs:951–968`). Otherwise it forms environmental non-generic variables,
   calls the generalizer/finalizer, records provenance, and stores a Scheme
   (`:970–1010`). The exact nonrecursive body does not reference `step` under
   H2; the recursive-body-dependent forced-quantifier route therefore has no
   such source witness here. This does not compute the finalized Scheme.
6. **Captured environment is a real generalizer input.** The remaining outer
   local `f` contributes its value and variables in its bounds to the
   non-generic set (`tail.rs:1014–1040`). Closure follows bound-connected
   variables while excluding the local public root (`:1210–1238`). This
   mechanism matters because freshening a Scheme's explicit coordinates does
   not freshen every captured live endpoint. The full compact outcome is not
   reconstructed from this collection alone.
7. **Returned name.** `lower_local_name` instantiates that local value,
   creates/resolves a RefId to the same `step` definition, and emits
   `Computation::value` (`lowering/name_ref.rs:146–173`). With a Scheme,
   `instantiate_local_value` allocates fresh result `q`, instantiates the
   Scheme with provenance, and submits `predicate <: Neg::Var(q)`
   (`tail.rs:855–941`). Without a Scheme it returns `local.value` immediately
   (`:856–858`). Neither route is an invocation of `step`.
8. **Block forwarding and outer outputs.** `prepend_block` sends the local
   binding's computation effect and tail-name effect to fresh block effect
   `B`, and sends tail value `q` to fresh block value `Q`
   (`block_local.rs:1284–1306`). Inner function construction and ordinary final
   name are value computations; their latent `f x` body effect belongs inside
   the returned Function. If the outer binding also uses a skeleton, its
   `B,Q` are linked into outer body anchors by the same `lambda.rs:788–808`
   mechanism. Write those actual anchors as `B_o,Q_o`.
   The outer frame's predicate then wraps both outputs:

   ```text
   outer.ret_eff = NonSubtract(Pos::Var(B_o),pop(s))
   outer.ret     = NonSubtract(Pos::Var(Q_o),pop(s)).
   ```

   Predicate collection and wrapping are established by the preceding note
   (`tail.rs:1058–1109`, `expr/constraints.rs:137–145`); the outer Function
   embeds these outputs (`lambda.rs:958–969`). This is the exact placement
   distinction missing from the previous same-effect-pivot hypothesis.

## Scheme transformation boundary and discriminating fields

The ordinary Scheme route is not an identity transport of the call's stack
weight. `generalize/mod.rs:75–90,110–133` compacts and simplifies the live
root. Preparation prunes and cleans stack weights (`:805–829`). Quantifier
planning excludes non-generic variables (`:900–915`), gathers live covariant
stack IDs on quantified variables (`core/stack_ids.rs:23–49,72–99`), and then
removes IDs outside the stack quantifier set from compact weights
(`generalize/mod.rs:188–238`, `core/prune.rs:504–523`). The exception extending
declared-All IDs (`mod.rs:867–887`) is not implied by the original Empty fact.
Another cleanup removes internal Empty entries with a matching plain negative
variable occurrence (`core/prune.rs:630–704`). Which conditions hold in the
exact compact `step` root is unverified.

Conditional field lemma: if all surviving covariant `s` entries occur only on
non-generic variables and no declared-All extension applies, `s` is absent
from the stack quantifiers and any remaining compact `s` weight is stripped
before finalization. This is a consequence of those tests; the antecedent is
not proved for the exact candidate.

If a stack ID does survive into the Scheme's stack quantifiers, ordinary
instantiation freshens it using one memoized substitution and wraps the whole
predicate in a root `Pos::Stack` carrying `u32::MAX` pops for that fresh ID
(`instantiate.rs:620–636,741–747,770–785`). Thus it is unsafe to identify a
Scheme's returned-name weight directly with the original frame ID `s`.
Unmapped captured type variables are retained (`:750–760`), and their live
bounds may still carry original IDs; Scheme weight freshening does not prove
that all original `s` paths disappear from the solver.

Smallest local discriminator: one Scheme with a surviving explicit `s` weight
and `stack_quantifiers=[s]` gives a returned-name predicate with fresh `t` and
root `pop(t,u32::MAX)`. A later `pop(s)` cannot cancel that explicit fresh-ID
entry solely by ID equality. A monomorphic live-root return instead returns
the original endpoint. This compares supplied representation states, not two
accepted source programs; no executable mutation was run. The actual candidate's
Scheme/live branch and surviving captured bounds must be determined before
either scenario can explain it.

## Consumer path, precise stop, and falsifier

The final wrapper itself submits a positive Function lower to a fresh variable;
its nested ports are not independently compared by that constructor. If H4
supplies an outer negative Function demand, the solver's covariant return-value
child is the concrete first comparison of the pop-wrapped returned value
(`constraints/machine/propagate.rs:264–269`). `Pos::NonSubtract` normalization
moves the pop to its left weight (`:26–36`). Bound replay can then bring the
returned `step` positive Function to an appropriate negative Function demand.
The Function rule preserves that weight on its covariant effect/value children
(`:257–269`) and swaps it on the argument path (`:226–232`). This supplies a
conditional output-value-to-inner-result route, not H4 itself.

There is also a distinct representation consumer: compaction processes
`Pos::NonSubtract` by weight **union**, and a positive Function routes its
incoming weight only to its covariant result ports
(`compact/collect/type_nodes.rs:13–23,83–94`). Scheme compaction uses the
projection-query path (`compact/surface.rs:12–24`). This is not the ordered
`compose_for_replay` calculation from the previous note. Its exact output
depends on compact variable expansion, simplification, and pruning. The
outer binding's publication/generalizer entrypoint was not traced here.

**Precise stop:** the supplied definition and inspected constructors produce
the outer wrapped value, but this pass does not derive the particular negative
outer/returned-Function demand, post-generalization live bounds, and admitted
replay that reconnect original `push(s,Empty)` to `pop(s)`. Neither the final
name nor an unconstrained result sink establishes that Function demand.

A falsifier for an unconditional H3 claim in the preceding transfer note is
an actual frozen-source trace
showing either (a) `s` was pruned/freshened with no original-ID bound route to
the consumed returned Function, or (b) no Function-shaped result demand reaches
that returned endpoint. A positive closure of that preceding-note H3 must
instead exhibit the
exact local Scheme/live branch, compact/instantiated endpoints and stack map,
outer return comparison, and admitted bound path retaining the matching ID.
Successful CLI acceptance or printed output cannot substitute for this trace.

Recommended next action: obtain one bounded actual solver-state trace for
those named stages under separate execution authorization, or keep the
preceding transfer note's H3 open.
Another stipulated weight-count probe would leave these source premises
untouched.

## Coverage, omissions, and provenance

No current `Delta_formal`, original profile/receipt, joint `(nu,K,D)`,
comparison-independent admission, Handler role rule, soundness, principality,
or production permission is derived. Exact parser acceptance, whole-program
lowering execution, finalized `step` Scheme, compact variable expansion,
outer publication, actual future call context, alias/recursive/method paths,
mixed uses, solver saturation, failures, and runtime behavior remain unverified.
Changed source blobs, special routes, failed lowering/projection, competing
selections, changed frame shape, unknown live bounds, or absent demands
invalidate the corresponding conditional joins.

The historical lowerer/generalizer/solver share one implementation's
assumptions. Their source is independent of current toy checkers, but is not
an independent language oracle. Blob checks establish provenance only.

Checks: read-only revision/status reads, bounded `rg`/`nl`/`sed`, Python
byte equality against `git show SHA:path`, SHA-256. Nine sequential historical
captures, including verification, consumed the twelve-capture budget. The
first locator was too broad and truncated; several guessed file locators did
not exist, and `&&` stopped two captures before later reads. Decisive windows
were recovered using real paths. Omitted output is not absence evidence.
No tests, builds, Oracle runs, formatting, Git mutations, parallel processes,
random seeds/ranges, executed mutations, or performance samples. Captures
took about 0.1–0.2 seconds each; total wall/CPU/peak RSS were not instrumented.
The approximately fifteen-minute wall cap was the scheduling limit; exact
consumption is unknown. All writes stopped at frozen submission.

Historical SHA-256 (all exact blob matches):

| Path | SHA-256 |
| --- | --- |
| `crates/infer/src/lowering/expr/chain.rs` | `e7b4c12f4abb58ad8b9c57045e61aa2aa94ba549bc0442b814417a33c16d47f6` |
| `crates/infer/src/lowering/expr/block_local.rs` | `661386fe559d8e207a9597962cfee3c11f05f21aa2888e22b2c0143825051898` |
| `crates/infer/src/lowering/expr/lambda.rs` | `2e0206bdcfdfbe98d13c12eec7ba8f7964383bc08c92947352ad370754024db9` |
| `crates/infer/src/lowering/expr/tail.rs` | `ac406b309fbb0ba558a18e37aba63a8e7ffeabbc377a111566b1f97d786f93b8` |
| `crates/infer/src/lowering/name_ref.rs` | `699c7dc84a2b4889355ffe9cd23b3e871c295957dbcb3fbad96ee9ee36470ede` |
| `crates/infer/src/generalize/mod.rs` | `03bfda4e4997347b59483de96eca652b67477639fc363e0890d546d2cf36fcef` |
| `crates/infer/src/generalize/finalize.rs` | `a8e5a1c8e6ad57d1fac7e25a1ab6a329093e5c76e6d84c0625c124c349f07492` |
| `crates/infer/src/generalize/core/prune.rs` | `05e6d343c90f1bbc77def8e50f9acb746451ceb3889bb50dd17342621afba26d` |
| `crates/infer/src/generalize/core/stack_ids.rs` | `adb9cd35d483af62ea0c3ebc572b9a0535761f3bfb99aedad49b371833b95f8f` |
| `crates/infer/src/compact/collect/type_nodes.rs` | `96dc38a9a05c447f019bb0421e0b37057d283026ba87bce121bb33959b0d8ab2` |
| `crates/infer/src/compact/surface.rs` | `1516be08117a372269909fcb7f64780cee4389a52a4f86ef63dd6eaa752b0d89` |
| `crates/infer/src/instantiate.rs` | `876ede0627a1ac64b155d3d7896a386ac1fa81d8814c40c77a0f3893128a9b2c` |
| `crates/infer/src/constraints/machine/propagate.rs` | `8695fa5d7dfac805cd7d66e9e0760c8c298002b952b0cd8a43dcd1f8eb6f7086` |

Current SHA-256 (all exact baseline matches):

| Dependency | SHA-256 |
| --- | --- |
| Inferred call views | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| Nested-block addendum | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| Main minimal clause | `495aceda697cef317f27be0375423246d9b2c7a341ea81a2bbf8df6e28910b4e` |
| Prior solver transfer | `10de73ca5dc50d3498823cc8e10e161e051b99407048dfbb4bcfcb69d25a6aec` |
| Multi-use continuation | `ba24a24339402daf9b24d089935754401c0af87786cca6b82dce74bcb9432b67` |
| Main Oracle crosswalk | `d192164e3b07328620fd58c75f4f359b277333885747c815d073520b9bb67784` |

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-frozen-oracle-nested-output-consumer-trace.md`.
- Baseline SHA: Yulang3 `46772a7a82826d945d1ca25ff666e61a32560bc9`;
  Frozen Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none; thirteen historical/six current blobs matched.
- Review status: frozen unreviewed research-only bounded characterization and
  conditional derivation. No independent-review claim or authority.
- Checks already run: revision/status, nine sequential bounded historical
  captures, exact blob equality/SHA-256, narrow output-scope inspection.
  No build, test, Oracle run, formatter, or Git mutation.
- Proposed one-line research-checkpoint commit message:
  `research: localize Oracle nested returned-function output consumer`.
- Shared-record deltas intentionally left for primary/curator: record outer
  value-output placement, intervening local Scheme/prune/freshen seam, and the
  exact missing demand/live-bound path; retain the preceding transfer note's
  H3 and this note's H3/H4 as unresolved where applicable, plus all current source-rule,
  profile/admission, and proof/production gates as open. No shared records edited.
