# Frozen Oracle: argument-effect demand and solver transfer

Date: 2026-10-06
Status: compiler-referee reviewed research-only bounded characterization; minor dispatch-premise precision repaired by primary
Yulang3 baseline: `f93fb06cd40c12fed6caf5051e045f206c4b2da6`
Frozen Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`, `/tmp/yulang2-oracle-rebuild`
Exclusive lease: this note only
Semantic and implementation authority: none

## Objective and retained authority

Continue the [producer-boundary trace](2026-10-06-frozen-oracle-missing-source-producer-continuation.md)
at its solver edge. Trace the already emitted ordinary-argument effect and
negative Function demand through canonicalization, bounds, Function transfer,
and the immediate return-stack normalization. This is static source archaeology
and a conditional local derivation, not another stipulated-transition checker.

Current governing sections are [inferred call views](../design/2026-10-05-inferred-function-call-views.md)
§§1.1–5, [nested-block interpretation](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
§§1–3, and [minimal missing clause](2026-10-06-main-source-generation-minimal-clause.md)
§5. The selected internal fully protected Handler seed and ordinary-value
`NonHandlerFormal` refinement concern the same inferred formal/use relation.
Actual supplied callable roles/entries remain distinct. The exact nested block
returns its captured local function value. Historical code changes none of
these decisions and supplies no current implementation permission.

**Result:** the old solver retains the ordinary argument's empty-row upper
and the shared formal's negative Function demand. Function decomposition has a
real special branch for a literal `Neg::Bot` **callee argument-effect port**:
it forwards the supplied argument effect to the call's return target after
stripping negative stack wrappers. That branch does not inspect the supplied
argument's evaluation tag or empty-row upper. It requires a positive Function
lower to reach the demand. No such positive lower is constructed by the
isolated variable-to-demand step itself. The exact unannotated empty push
also disappears during ordinary upper-stack normalization; that disappearance
alone is not a role-refinement witness. These are bounded old-side mechanisms,
not the missing current `U_c` predicate.

## Hypotheses and claim classes

H1: the nine historical files listed below equal their exact Oracle blobs;
the four current dependencies equal their pinned Yulang3 blobs. Verified by
byte equality and SHA-256, including both checkout revisions.

H2: the previous note's unannotated-name/application route has produced fresh
`epsilon`, shared `A_f`, and demand `G`. For the isolated fresh-effect prefix,
`epsilon` has no pre-existing bounds or aliases and only the two helper roots
are submitted. For the isolated formal-to-demand prefix, `A_f` has no projected
lowers and no unrelated queued work adds one. These are explicit lowerer/solver
state premises, not established acceptance of a surface program.

H3: a concrete positive Function lower later reaches `G` with specified
constraint weights `W`; canonical/proof admission succeeds and the drain is
not stopped by a terminal proof/resource failure. The unweighted calculations
below specialize to `W=empty`. Endpoints are distinct where stated.

**Established representation/provenance facts:** H1 and the cited branch and
field operations. **Bounded characterization:** this transfer inventory.
**Conditional local derivations:** the isolated prefixes and structural pair
below under H2/H3. No complete historical absence result, source-adequacy
theorem, reviewed theorem, current semantic closure or production conformance
is claimed. H2/H3 are candidate analysis premises.

## Transfer inventory

All source locations below are relative to the Frozen Oracle tree.

1. **The emitted bottom lower is trivial; the empty-row upper is stored.**
   `lowering/expr/constraints.rs:7–28` emits
   `Pos::Bot <: Neg::Var(epsilon)` and
   `Pos::Var(epsilon) <: Neg::Row([], Neg::Top)`.
   `constraints/machine/entry.rs:1092–1119` drops the former before it obtains
   a constraint record; therefore it does not install an explicit bottom lower.
   `machine/propagate.rs:99–152` routes the latter to
   `row_effect.rs:88–119`. Its unweighted reduction shortcut immediately
   returns false for empty items (`row_effect.rs:231–243`), so the row is
   inserted through `add_upper_bound` (`machine/bounds.rs:816–912`). Under H2,
   this prefix leaves an empty-row upper and no lower on `epsilon`. It does
   not replace the variable node by a literal `Bot`, an empty positive row,
   or a role tag. The helper's name is not a proof of its full denotation.

2. **The formal demand is an upper bound, not an eager Function synthesis.**
   `lowering/expr/tail.rs:535–563` emits

   ```text
   G = Neg::Fun(Pos::Var(A_x), Pos::Var(epsilon), R, Neg::Var(V))
   Pos::Var(A_f) <: G.
   ```

   Entry uses empty weights and drains (`machine/entry.rs:493–499,970–995`).
   The variable case (`machine/propagate.rs:99–152`) inserts `G` as an upper.
   Bounds replay pairs it with existing projected lowers and composes their
   weights (`machine/bounds.rs:3583–3642`). Under H2's zero-lower premise,
   there is no such pair and no Function-decomposition step from this root.
   Extrusion preserves the node IDs/heads while traversing their variables
   (`machine/bounds.rs:4535–4650`); it does not synthesize a positive Function.
   This does not assert that the full enclosing program never supplies a lower.

3. **Function transfer distinguishes a literal port, not ordinary argument
   evidence.** When replay supplies
   `F=Pos::Fun(a,ae,re,r)` against `G` with weights `W`, the branch at
   `machine/propagate.rs:213–271` submits:

   ```text
   A_x       <: a                  with swap(W)
   if ae is literally Neg::Bot:
     epsilon <: stripNegStacks(R)  with bothFromRight(W)
   else:
     epsilon <: ae                 with swap(W)
   re        <: R                  with W
   r         <: V                  with W.
   ```

   `stripNegStacks` is the entire loop at `machine/propagate.rs:401–410`.
   The predicate is `types.neg(ae)` matching `Neg::Bot`, not a traversal of
   `epsilon`'s bounds or of `ae`'s bounds. Weight operations are defined at
   `constraints/mod.rs:3566–3607`; both are empty for empty `W`. In the special
   branch with `R=Neg::Stack(Neg::Var(rho),w)`, the new unweighted link is
   `epsilon <: rho`. The variable-to-variable rule installs an `epsilon`
   lower on `rho` and a `rho` upper on `epsilon` (:102–129 of `propagate.rs`),
   subject to the normal admission assumptions. It does not copy the empty-row
   upper forward onto `rho`; later opposite bounds can replay through the link.

4. **The exact empty push is also erased on the normal upper path.**
   The inherited unannotated helper emits `w=StackWeight::push(s,Empty)` on
   both polarities and declares `(call_effect,s,Empty)`
   (`lowering/expr/tail.rs:740–798`). Declaration records a subtract fact
   (`machine/entry.rs:901–946,1832–1864`); this immediate recording step does
   not decompose a Function.

For `Pos::Var(z) <: Neg::Stack(Neg::Var(rho),w)` with initially empty weights,
the variable-left dispatch reaches upper-stack normalization directly
(`machine/propagate.rs:36–59`), which first observes
`w.filter=All`, which adds no filter constraint. The active push list is
`[Empty]`, whose common subtractability is `Empty`
(`row_effect.rs:805–818`); the explicit non-Empty guard skips that filter
too. The new right weight contains only pops. This fresh push has zero
pops (`poly/src/types.rs:311–355,523–539,612–627`), and conversion drops
zero counts (`constraints/directed_weight.rs:328–355`). The resulting
constraint is simply `Pos::Var(z) <: Neg::Var(rho)` with empty weights. This
is a local normalization fact, not evidence that handler protection vanished from
   the complete program: the corresponding **positive** wrapper enters the
   left weight (`machine/propagate.rs:11–24`), and subsequent frame pops and
   generalized evidence are outside this assignment. Non-empty filters,
   different pushes/pops, and composed replay weights require other analyses.

## Smallest structural discriminator

Keep the supplied ordinary-argument endpoint, its empty-row upper, and demand
fixed. Choose one return wrapper `R=Neg::Stack(Neg::Var(rho),push(s,Empty))`
and empty `W`. The other lower ports can be `a=Neg::Top`, `re=Pos::Bot`,
`r=Pos::Bot`, making their child comparisons trivial. Compare two positive
Functions differing only in their argument-effect port:

```text
F_B.arg_eff = Neg::Bot
F_V.arg_eff = Neg::Var(q), where q is fresh and q != rho.
```

H3 yields `epsilon <: rho` for `F_B`, and `epsilon <: q` for `F_V`.
The argument's ordinary status and empty-row upper did not change. Conversely,
changing only `epsilon`'s bounds cannot change this branch predicate at this
step. This analytical one-field mutation identifies the actual discriminator:
the positive Function's literal port. No executable mutation or accepted source
counterexample was run; this pair is not claimed to have equivalent denotations
or to be a cardinal-minimal language witness. It isolates the branch with one
Function comparison and one stack wrapper.

## Independence, coverage, and precise remaining gap

The frozen source is independent of the current toy checkers, but its lowerer,
solver and any built Oracle executable share one implementation's assumptions.
Blob provenance and this derivation do not independently validate language
semantics. No printed scheme, supplied Pure callback, or successful pending
comparison is used to establish current source membership or admission.

The immediate effect mechanism is now located. The unresolved correspondence
is why the **ordinary source use of the unknown formal**, before choosing an
actual provider lower, entails the selected refinement and which original
joint `(nu,K,D)` tuples that permits. A literal callee `arg_eff=Bot` conditional
does not establish that source premise. Neither does dropping an empty return
push on one negative path. Current `U_c`, typed contribution footprint, complete
profile/receipt schema, comparison-independent admission, generalization/capture
preservation, principality, source adequacy and production conformance remain
open. Repeating this transfer with larger toy ranges would leave the premise
untouched.

**Recommended next action:** derive the missing minimal-clause §5 source-owned
predicate on the shared formal before provider selection, keeping the exact
historical effect-routing conditional as a correspondence obligation rather
than adopting it as current Handler semantics.

Unverified: exact-source acceptance; actual enclosing lowering/runtime stack;
other expressions, aliases, methods, recursion and mixed/repeated uses;
nonempty weighted residuals; lower-wrapper/frame-pop composition; complete
solver soundness, saturation and generalized outputs. Different blobs, hidden
lowers/queued work, changed port heads/weights, duplicate/subsumed admissions
or terminal proof/resource failure invalidate the affected local derivations.

## Checks and resource account

Commands: read-only `git rev-parse HEAD`; bounded `rg -n`, `rg --files` and
`sed -n` source windows; a Python/subprocess loop comparing live bytes with
`git show <pinned SHA>:<path>` and computing SHA-256. All nine historical and
four current direct dependencies matched. Initial combined context captures
were truncated; decisive windows were recovered. Exploratory locators named
nonexistent `machine/subtype.rs`, `constraints/subtract.rs` and
`constraints/extrude.rs`; those searches were corrected to the actual files.
The failed locators and incomplete initial output are not absence evidence.

No builds, tests, compiler/Oracle executions, formatter, Git mutation, random
seeds, enumeration ranges, performance samples or additional output files.
Only lightweight source-read/hash processes were used, with bounded captures;
some independent reads were batched. CPU, peak RSS and total wall time were
not instrumented. No heavyweight-process budget was consumed. The producer
does not independently review this artifact; writes stop at frozen submission.

Verified historical paths: `crates/infer/src/lowering/expr/{constraints,tail}.rs`,
`crates/infer/src/constraints/machine/{entry,propagate,bounds}.rs`,
`crates/infer/src/constraints/{row_effect,mod,directed_weight}.rs`, and
`crates/poly/src/types.rs`. Direct current dependency hashes are:

| Dependency | SHA-256 |
| --- | --- |
| Inferred call views | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| Nested-block addendum | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| Main minimal clause | `495aceda697cef317f27be0375423246d9b2c7a341ea81a2bbf8df6e28910b4e` |
| Prior producer continuation | `7b31b95460725948b32f41a3f792c6efc125ade48d83389122f5f3145d36d552` |

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-frozen-oracle-missing-producer-solver-mechanism.md`.
- Baseline SHA: Yulang3 `f93fb06cd40c12fed6caf5051e045f206c4b2da6`;
  Frozen Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none; nine historical/four current files matched
  their pinned blobs. Current direct hashes are recorded above.
- Review status: frozen research-only bounded characterization and conditional
  local derivation; compiler-referee found no blocking/major findings and one
  minor dispatch-premise precision issue, repaired by the primary; no
  semantic/implementation authority.
- Checks already run: pinned revision reads, bounded source/path inspections,
  byte equality and SHA-256 of direct dependencies, narrow output-scope check.
  No executable test, build, formatting or Git mutation.
- Proposed one-line research-checkpoint commit message:
  `research: trace Oracle argument-effect solver transfer and empty stack normalization`.
- Shared-record deltas intentionally left for primary/curator: add the literal
  callee-port passthrough conditional, the absence of a Function lower in the
  isolated zero-lower prefix, and the normal empty-push erasure distinction;
  retain the current source predicate, typed footprint/admission, and all
  proof/production gates as unresolved. No shared record was edited.
