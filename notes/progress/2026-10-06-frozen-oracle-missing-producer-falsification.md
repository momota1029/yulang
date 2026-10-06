# Frozen Oracle: annotation-state falsification at the ordinary-formal call

Date: 2026-10-06
Status: compiler-referee reviewed research-only bounded characterization; no blocking/major findings; minor issue repaired by primary in companion solver note
Yulang3 baseline: `f93fb06cd40c12fed6caf5051e045f206c4b2da6`
Frozen Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`, `/tmp/yulang2-oracle-rebuild`
Exclusive lease: this note only
Semantic and implementation authority: none

## Objective and result

Method: bounded static producer/control-flow falsification. Inspect the nearby
historical producers for argument effect view, application shape, formal
annotation state and call-frame eligibility. Distinguish the source-level
annotation locations without repeating the previous mutation of the argument's
`Evaluation` field or the frame-selection investigation.

**Result:** neither an ordinary `Value` argument nor absence of an
`ArgEffectContract` identifies the historical special unannotated-return
path. An absent formal annotation and a formal `_` annotation produce the
same absent contract, but different call-return classifications. A postfix
`_` annotation on the callee use preserves the underlying variable expression
and its binder classification. This is a conditional comparison of source
lowering routes and a local non-injectivity result for the marker channel.

No source-valid counterexample to the complete proposed historical/current
correspondence is established. Exact surface parsing, successful typechecking,
solver consequences and runtime behavior were not checked. The result defeats
only a reconstruction that treats absent markers plus ordinary-value evidence
as sufficient to identify that historical path; it does not defeat the
user-selected current singleton outcome.

## Baseline, authority and hypotheses

Current authority is [inferred Function call views](../design/2026-10-05-inferred-function-call-views.md)
§§1.1–5 and the [nested-block addendum](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
§§1–3. The exact missing predicate is [main source generation](2026-10-06-main-source-generation-minimal-clause.md)
§5. Internal protected Handler seed, ordinary-value refinement on the same
inferred formal/use relation, actual callable role/entry preservation, and
annotation-scoped permission remain selected. Nothing here reinterprets them.

Inputs are the existing [source archaeology](2026-10-06-frozen-oracle-source-producer-archaeology.md),
[missing-producer continuation](2026-10-06-frozen-oracle-missing-source-producer-continuation.md),
[annotation/call archaeology](2026-10-06-frozen-oracle-annotation-call-producer-archaeology.md),
and [argument-effect channel](2026-10-06-frozen-oracle-argument-effect-contract-channel.md).
The prior evaluation-tag erasure and marker port-position loss are retained
results; they are not this lane's new attack.

H1 (established provenance): all nine directly inspected historical source
files match their pinned Git blobs; all seven current dependencies above match
the Yulang3 baseline blobs.

H2 (candidate route premise): successful ordinary defined-parameter lowering
uses variable patterns, no supplied parameter upper, and one direct call of
resolved formal `f` to ordinary unannotated formal `x`. The call is reached
with an eligible Defined frame and no preexisting subtraction for `f`. CST
annotations, when present, lower as described below. This is not an accepted
program theorem. For the nested candidate, the approved lexical meaning is
retained, while historical dispatch and active-frame eligibility remain
premises.

H3 (local comparison premise): all three routes complete normally. Compare
structural port constructors and metadata, allowing fresh-ID renaming and the
additional annotation constraints; do not assume identical solver state or
final solution sets across the routes.

Established facts are the cited assignments and blob equality. Claim classes
are bounded historical characterization and a conditional local derivation
under H2–H3. No current theorem, independently reviewed result, historical
whole-repository absence result or production conformance is claimed.

## Smallest discriminating annotation-location comparison

The following are source sketches denoting three stipulated CST routes, not
claims of exact-byte parser acceptance:

```text
A: my apply f x = f x
B: my apply (f: _) x = f x
C: my apply f x = (f: _) x
```

One annotation is the only source change in B and C. One formal/call pair is
sufficient; capture, recursion and multiple uses add no needed discriminator.
Removing the call removes the return-demand observation. Minimality is local
to this comparison, not a global smallest-source claim.

| State at the inspected call | A | B | C |
| --- | --- | --- | --- |
| Contract extracted for formal `f` | `None` | `None` | `None` |
| Local effect installed for `f` | `None` | `None` | `None` |
| Formal call predicate / erased upper | empty / absent | empty / absent | empty / absent |
| `f.call_return_effect` | `Unannotated` | `Annotated` | `Unannotated` |
| Callee expression identity | `Expr::Var(ref -> f)` | `Expr::Var(ref -> f)` | preserved `Expr::Var(ref -> f)` |
| Argument `x` producer | `Value`, exact-pure effect, no effect view | same producer class | same producer class |
| Selected return-demand constructor under H2 | `Stack(Var(call_effect), push(s, Empty))` | bare `Var(call_effect)` | same weighted constructor as A |
| New frame pop for this formal | yes | no | yes |

Derivation, with paths relative to the frozen tree:

1. `crates/infer/src/annotation/builder.rs:184–189` lowers the source `_`
   token to `AnnType::Wildcard`. Its bounds are `Pos::Bot` and `Neg::Top`,
   with no output subtraction (`annotation/constraints.rs:324–328`). The
   connector submits `Bot <: Var(value)` and `Var(value) <: Top`
   (`:124–137`). These are historical constraints, not a claim about current
   source holes or their complete meaning.
2. Formal annotation absence produces `local_effect=None`, contract `None`,
   empty predicates and `Unannotated` (`lowering/expr/lambda.rs:1252–1264`).
   For `_`, the annotated route is taken; it has no effect stack
   (`annotation/constraints.rs:263–288`), and the non-Effectful fallback leaves
   the local effect absent (`lambda.rs:1316–1327`). Its call predicate is empty
   (`:1581–1593`), so no public/erased call upper is built (`:1284–1309`).
   `_` is not a Function, so its argument contract is `None` (`:1357–1368`).
   Nevertheless the annotated route sets `call_return_effect=Annotated`
   (`:1337–1341`). This gives the new marker non-injectivity witness: absent
   annotation and `_` annotation both map to `None`, while the classification
   controlling the call differs.
3. Pattern installation stores the supplied classification on the resolved
   `Def::Arg` (`lowering/pattern.rs:236–281`). The no-parameter-upper premise
   excludes the separate classification override (`lambda.rs:690–696`).
   Defined lowering marks an unannotated argument's frame only when that
   classification is `Unannotated` (`tail.rs:831–841`).
4. `lower_local_name` always returns `Computation::value` for these references;
   an unannotated `x` gets a fresh exact-pure effect and no sidecar view
   (`lowering/name_ref.rs:146–187`). Its producer is unchanged by the location
   of `_` on `f`. No final effect solution equality is asserted.
5. At a postfix `_` annotation, effect-upcast collection returns no paths
   because `_` is not Effectful (`lowering/expr/method_body.rs:1789–1797,
   :1823–1826`). `lower_type_annotation_tail` connects the existing value,
   exports the empty subtraction list and returns the same `acc`
   (`tail.rs:52–86,:1075–1082`). Thus C retains the same callee expression and
   does not modify the binder's classification. The connector changes
   constraint state; this is not a claim that C and A have identical traces.
6. `local_callee_def` recognizes that preserved `Expr::Var`
   (`tail.rs:844–848`). The return helper checks the binder classification
   before frame selection (`:745–767`). B returns bare positive/negative
   variable ports at the `Annotated` guard. A/C under H2 proceed to allocate
   `s`, declare `Empty`, record a pop, and construct matching push-weighted
   ports (`:769–798`). All routes still generate the four-port Function
   demand and submit the same kind of formal endpoint comparison (`:543–563`).

This demonstrates which source metadata controls this helper. It does not
identify `Empty` with current full protection or its removal, and it does
not show that a different demand constructor yields different final program
behavior.

## Other nearby producers and the unchanged blocker

`LocalEffect::Stack` explicitly separates the full ordinary effect from an
inner weighted view (`lowering/local.rs:43–52`). Name lowering puts the full
effect in `Computation.effect` and retains the stack in `effect_view`
(`name_ref.rs:176–198`). The inspected application uses `arg.effect` and
`arg.value`, while its return helper receives only callee and call-effect
inputs (`tail.rs:543–552`). This agrees with the prior continuation; no new
effect-view mutation or claim about all consumers is added.

The surviving blocker is the interpretation from historical value/effect
constraints and annotation/frame metadata to the current complete
`U_c(xi; seed,refined,argument,invocation)` on one original `(nu,K,D)`.
Even marker presence/absence cannot recover the historical annotation state
needed by the local helper. Keeping the actual classification would repair
that information loss, but would still leave the semantic interpretation
unproved. No current carrier or implementation change is proposed.

Typed receipts, original `beta/Slots(beta)` and profile incidence, correlated
joint `(nu,K,D)`, Q-independent initial/context admission, principality,
soundness, source adequacy and production conformance remain open. A second
equivalent tag/frame toy probe would leave the same interpretation premise
untouched. Recommended next action: derive the current §5 whole-tuple
predicate from source-owned evidence; retain this note only as a historical
warning against recovering annotation state from the marker channel.

## Independence, coverage and resources

No Oracle execution or behavior is used as authority. Frozen implementation
assignments are independent of current stipulated-transition checkers, but
the historical producer/solver are one implementation and share its
assumptions. Static control flow proves these bounded constructor choices;
it does not independently validate their source semantics. A checker supplied
with this table would test the supplied table, not prove its source rules.
The producer claims no independent review of this note.

Commands: read-only `git rev-parse HEAD` and initial status; bounded `rg -n`
and `sed -n` windows; Python byte comparison against `git show SHA:path` plus
SHA-256. Eight sequential frozen-source read/search captures, one revision
read and one combined dependency-validation capture were used. Initial
combined current-context output was truncated; decisive authority, §5,
continuation and historical windows were recovered narrowly. No omitted
search output is treated as absence evidence.

Local operating cap communicated to the primary: one sequential lightweight
source process, approximately twenty minutes; no numerical CPU/RAM cap was
provided in the assignment. No build, test, compiler edit, executable probe,
Git mutation, formatter, secondary output path, randomized seed/range,
performance sample or executed mutation was used. The three routes are a
static annotation-location mutation only. CPU, peak RSS and elapsed wall time
were not instrumented. No heavyweight process ran.

Unverified: exact surface/CST acceptance, historical complete candidate
dispatch and active-frame stack, solver draining/normalization consequences,
final solutions and runtime behavior, effectful annotations beyond this local
sidecar check, aliases/methods/recursion, full multi-use aggregation, and all
current formation/proof gates above. Changed blobs, failed annotation/call
lowering, supplied parameter uppers, a non-variable callee, or an ineligible
frame invalidate the relevant comparison premises. The marker
non-injectivity fact remains local to the inspected annotation producer.

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-frozen-oracle-missing-producer-falsification.md`.
- Baseline SHA: Yulang3 `f93fb06cd40c12fed6caf5051e045f206c4b2da6`;
  Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none. Seven current dependencies and nine
  historical files matched pinned blobs. Additional historical bridge files
  checked here: annotation builder SHA-256
  `baad6a964909eaee3e7822aa5445dca8cd2f70185bd5a1f2157e878a512ddf7b`;
  annotation constraints
  `3c0482d4549a2bfc7e651a6b2cc15fa4e70488fe8f68fcbfca34c1bfb72920db`;
  effect upcasts in method body
  `3319db30fd3d6771eea156a2b902372c59db75ce1e27f64fcb44d987c3e52b74`.
- Review status: compiler-referee reviewed research-only characterization;
  no blocking/major findings and one companion-note minor issue repaired by
  the primary. No current semantic or production authority.
- Checks already run: revision/status reads; bounded producer windows;
  byte-for-byte baseline/blob checks and SHA-256; narrow artifact scope check.
  No builds, tests, Oracle execution or Git mutations.
- Proposed research-checkpoint commit message:
  `research: distinguish Oracle formal annotation state from absent markers`.
- Shared-record deltas left for primary/curator: record that marker absence
  cannot recover formal annotation state and that use annotation preserves
  the binder classification on this route; retain the complete historical
  correspondence, current `U_c`, typed receipt/profile/joint relation and
  independent admission as open. No shared record was edited.
