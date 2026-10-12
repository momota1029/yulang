# Same-family arm send: recursive skeleton source audit

Date: 2026-10-12
Status: frozen static characterization; independently reviewed, minor clarification closed
Claim class: bounded source-owner map and conditional replay derivation
Y3 baseline: `50df6083366debd9fe534860c6a0ed01d5049208`, `research/simple-sub-intrusion`
Oracle semantic source: immutable `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Lease: this file only; static leaf, no delegation or inference execution

## Objective and exact boundary

Attack the first remaining P+ operation in
[the reviewed handler proof](../theory/2026-10-12-same-family-handler-output-proof.md)
§§4–7: the independent arm-send row already derived at handler Effect T,
its actual forwarding into recursive body Effect R, and the Function/root
that supplies the public return. Reuse the reviewed B-to-T result without
repeating it. Original H remains exactly
[the original attempt](../theory/2026-10-12-oracle-effect-hygiene-original-H-proof-attempt.md)
§1, including original scopes, binders, actual uses, complete Calls and future
lowers. P+ acceptance, selected scheme and final output remain unverified.

The candidate is the same source in the input proof: annotated
`run(action: [ev] 'a): 'a`, complete catch, arm block containing the independent
`ev::send (s,n)` followed by `run (k ())`, value arm `v -> v`, and terminal
`run: ev::send (1,42)`. Family E is the actual nullary ev declaration.
T and R are constructor coordinates, never guessed numeric IDs. The accepted
P0 scheme and live capture instrumentation are excluded as semantic evidence.

Governing inputs are the reviewed proof §§4–7, the
[source route](2026-10-12-same-family-handler-source-route.md), original H §1,
and [top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5. The primary's selected annotation, attachment, residual and complete
Call meanings are retained. No new language or production decision is made.

All Oracle locators below are under `crates/infer/src/` at the immutable
revision. Every source read used `git show` or `git grep` on that revision in
`/home/momota1029/rust/yulang2-oracle-capture`.

## Established source-owner distinction: internal self and public root

The top-level header-argument owner is
`lowering/body/mod.rs:2263–2365::lower_single_binding_with_context`.
It allocates public definition root Q at 2282–2288 and calls
`lower_binding_body_with_args_to_named_self` at 2311–2318.
`lowering/expr/mod.rs:300–339` then allocates a *different* internal self Value
S and installs a LocalBinding named run with Value S, scheme None, Annotated
call-return mode, and empty call predicates. S is passed as the skeleton target.
After successful body lowering, the completed wrapper Value W is forwarded
to Q at 336–338. S and Q are not interchangeable providers.

For the recursive source expression, `lowering/name_ref.rs:73–75` therefore
takes the local branch. `lower_local_name` at 146–174 resolves the actual
reference immediately to this binding. `expr/tail.rs:855–858` returns the
existing local Value S when its scheme is None. No fresh per-use scheme,
ApplyRefResolution work item, or SCC OpenUse is needed to supply that recursive
callee. The recursive demand is imposed on S during body lowering.

This corrects the source-route note's description of the recursive run as a
global reference. Its empty-predicate conclusion still has a source reason:
the installed self binding has empty predicates, its Def is Let rather than
Arg, and the bare-return branch in `expr/tail.rs:740–757` applies. The empty
predicate does not follow from treating run as absent from local bindings.
The later outer run reference is a separate global/SCC consumer after the
internal binding has been removed.

The distinction is material to timing: `lifecycle.rs:219–221` only queues
analysis work, and `lowering/body/mod.rs:634–641` describes draining analysis
after binding lowering, but those facts do not delay this local recursive
demand. A provisional global-reference reading was rejected on finding the
named-self owner; no conclusion in this note uses that reading.

## Concrete constructor map before and after T-to-R

For the single action parameter, name the skeleton layer's Value F_s, output
Effect D, output Value J, body Value L, internal target S, and public root Q.
This is a structural map of the actual source constructors, not an observed
runtime census of every generated canonical record.

| Order | Source-owned constraint or port | Owner and actual explanation |
| --- | --- | --- |
| Before body | `Fun(Var(param.Value), skeleton_arg_eff, Var(D), Var(J)) <: F_s` | `lambda.rs:1146–1168`, direct Function lower |
| Before body | `F_s <: S` | `lambda.rs:1171–1173`, internal alias root |
| Before body | `R <: D`, `L <: J`, `J <: L` | `lambda.rs:1207–1224`; action is Annotated, and its output predicate is empty |
| In body | `S <: Fun(actual k-call.Value, actual k-call.Effect, Var(K_C), actual C.Value)` | recursive application's actual demand, `tail.rs:535–627` |
| Derived in body | `D <: K_C` | actual FunctionReturnEffect structural child of the comparison of that skeleton Function with that demand |
| In body | `K_C <: C_C`, `C_C <: B_eff`, `B_eff <: T` | application, block and arm forwarding; reviewed input owns their earlier derivation |
| After arms | `V <: Row({E},T)`, `Push_alpha(U) <: Row({E},T)` | actual scrutinee row; `control.rs:957–1021`; these are separate row producers |
| Completed body | `T <: R`, catch.Value `<: L` | `lambda.rs:797–802`; the Effect edge has unknown_internal root origin |
| After body | `Fun(public_arg, arg_eff, Var(R), annotated result.Value) <: W` | `lambda.rs:946–969`, `tail.rs:1092–1101`, empty final predicate |
| Named-self return | `W <: Q` | `expr/mod.rs:336–338`; Q is the public definition root |

`lowering/local.rs:137–144` makes the early empty skeleton connection depend
on Annotated call-return mode. `lambda.rs:1327–1340` establishes that mode
for the explicitly annotated action parameter. Initial frames are empty
(`lambda.rs:756–764`). The input source route's annotation/frame audit supplies
the empty final output predicate under normal completed constructors. Nothing
here adds a POP for alpha to the whole output.

The graph already contains the actual path
`R -> D -> K_C -> C_C -> B_eff -> T` before the closing Effect edge.
R is therefore an older exposed source with replay uppers, not a fresh block
receiver. The internal Function has port D; the final public wrapper has port
R. This is why a return-port argument must use the actual public-root path.
The recursive comparison has its actual structural and bound replay parents;
the root `T <: R` is emitted without those as explicit source parents. Internal
origin equality does not equate it with their coverage roots.

### Levels and extrusion

Skeleton allocation occurs at `lambda.rs:745–767`, before entering the body
child level at 776. T is allocated in the catch at `control.rs:927–928` inside
that body. Birth levels differ even if earlier constraints have already lowered
current levels. `add_lower_bound` extrudes its positive endpoint to R's current
level before alias insertion (`bounds.rs:645`).

This Oracle extrusion retains the original PosId: `extrude_pos` at 4523–4532
returns `pos` after traversal. `extrude_type_var` at 4701–4727 lowers the
existing variable's level and traverses its current lower and upper shapes.
It does not allocate a replacement T, make a parent/copy pair, or register a
fresh subtraction mapping. Thus an alias can still name T after extrusion.
This is an established source fact, not a theorem that all level/replay or
claim invariants survive generalization.

The user-provided cross-level recursion witness is:

```yulang
my odd n =
    my even n = if n <= 0 { true } else odd(n - 1)
    even(n - 1)
```

Here O and E denote the outer and nested definition-root vertices in the
approved **source-owner Value-reference graph**: the definition-root rule
assigns `O → E` and `E → O`, so this specified graph has a nontrivial SCC
despite lexical nesting and different inference levels. This is a source
semantics fact, not evidence that current Oracle/Y3 solver rows materialize
those vertices or that the pair remains in an SCC after local generalization.
It does not identify either Value as an extrusion parent/copy of the other.
For P+,
the internal-self graph above already supplies active recursion; replacing it
with a same-level/global SCC story would lose the actual owner. No odd/even
inference, expansion of this audit's source domain, or parent/copy claim was
performed.

## Exact operational seam and a discriminating conditional derivation

The §4 fresh-*receiver* argument cannot be transplanted unchanged. On stepping
`T <: R`, `propagate.rs:104–129` first calls `add_lower_bound(R,Var(T),...)`
and only afterward adds the upper on T. R's existing uppers may cause replay
admissions during that lower insertion. Root admission alone cannot assert
that `canonical_qualified_parents_by_root(c_TR)` is empty when the later
upper claims are registered.

The source map suggests a different, candidate invariant: **first positive
exposure of T**. In the catch source owners, T is the branch-result receiver
and the negative handled-row tail; the continuation takes V, not T
(`control.rs:1128–1133,1596–1629`), and this source has no guard or var-pattern
rewrites. The first direct `Pos::Var(T)` root is the body forwarding operation.
Row residual installation sends the actual source or gamma *to* T
(`row_effect.rs:156–170,216–233`), rather than using T as its feedback source.
This is a candidate sufficient route to proving a new canonical c_TR with no
qualified parents. It requires an induction over all already admitted derived
replays at this exact prefix; a direct syntactic endpoint census alone does
not prove that dynamic induction.

The precise first missing owner fact is:

> At the initial upper registration for actual c_TR, after positive extrusion
> and all lower-insertion replay admissions, the materialized T-to-R upper
> has an included support independent of recursive cyclic premises; in
> particular, the proposed route needs a Direct original claim q_TR whose
> coverage root is uncovered and whose Standalone clause remains present.

The decisive owners are `entry.rs:1357–1424` (new/duplicate canonical root),
`bounds.rs:647–657,4274–4295` (alias lower subsumption),
`bounds.rs:962–1029` (qualified-parent scan or fallback original Direct claim),
and `bounds.rs:3832–3848` (replay admission plus eager parent registration).
New semantic replay is queued there; canonical duplicates can receive parents
eagerly. The mere source root origin does not prove that fallback Direct branch
was taken. This audit does not report an invented actual parent/claim ID list.

If that owner fact is established, the inspected consumer gives this exact
conditional continuation of the reviewed source-to-T result:

```text
actual included E-row lower e_T at T (reviewed source-to-T result)
+ actual included T-to-R upper u_TR (the missing owner fact)
+ completed normal concrete-row replay/admission
=> actual E-row lower e_R at R with parents (e_T,u_TR).
```

The native planner chooses Generic if that upper has an uncovered claim
(`proof/mod.rs:9448–9517`); the row is not eligible for Var-to-Var evidence-only
skipping (`bounds.rs:3814–3829`). Nullary E extrusion leaves its concrete shape
unchanged. Actual projection parent construction supplies
`ReplayConjunction(e_T,u_TR)` (`bounds.rs:1179–1243,2332–2370`), whose consumer
at `proof/mod.rs:11735–11763` includes both included premises. This is a
conditional derivation from real producers/consumers, not a checker that
assumes forwarding, and not closure of the missing premise.

A Direct q_TR with immutable Var-to-Var producer cannot itself be the
Var-to-Row producer that activates row coverage at `row_effect.rs:490–540`.
That fact would protect its own uncovered root once the Direct claim is
established. It does not classify every alternative qualified route rooted
at scrutinee reductions, nor infer independence from an Independent enum tag.
The same lower record may have excluded cyclic/reduction clauses plus a
successful clause; the evaluator returns on a successful exact clause
(`proof/mod.rs:11705–11732`). A cycle visit returns Excluded at 11918–11929,
but that is not a source-qualified proof of total row loss.

No genuine excluded e_R route or lost-output counterexample was found. The
precise unverified claim registration above is the stop condition, not absence
of capture, P0 behavior, transitivity, or recursive SCC membership.

## Selected public Function and collection boundary

After the missing T-to-R owner fact, selection still has to follow W-to-Q,
its actual Function lower, and that Function's R return Effect. Module
generalization compacts Q through
`analysis/session/generalize.rs:580–602`; the accepted iteration subsequently
performs alias expansion, stack cleanup and generalization at 478–549.
`analysis/session/instantiate.rs:14–82` stores/finalizes those selected schemes.

The scoped query excludes records only on its actual projection decision
(`structural_kernel/access.rs:862–895`). `compact/collect/mod.rs:848–879`
passes included bound clones to the collector. Its alias case at 1099–1109
creates a secondary Var occurrence; an included alias `Var(T)` at R is not
by itself a materialized E row. The missing e_R concrete replay is consequently
a real consumer obligation. The actual positive Function collector follows
its supplied ret_eff (`collect/type_nodes.rs:13–22,196–225`), including R for
the final wrapper. No source rule selects the old P0 compact image here.

The later outer global run reference follows name_ref's queued resolution,
lifecycle's UseResolved owner, and SCC routing. `scc.rs:266–288` selects an
instantiation for a quantified target or an internal open route; selection's
OpenUse consumer (`session/selection.rs:1095–1117`) uses its actual target
root. These later routes do not replace the active local recursion above.
Selected-root projection, simplification, finalized scheme, per-use cloning
and outer complete Call output remain unproved by this audit.

## Checks, dependencies and resource accounting

Commands used: bounded `cat`/`sed`/`rg` governing reads; immutable
`git -C ... show a58eefc31e:<path> | nl -ba | sed -n ...`; immutable
`git grep`/`git ls-tree` owner lookup; read-only Git status/baseline/diff;
Python SHA-256 and immutable blob identity checks. The four direct Y3 inputs
below matched live bytes at inspection; the exact dependency diff against
`50df60833` returned no paths. No dependency was edited.

| Direct Y3 input | SHA-256 |
| --- | --- |
| reviewed handler proof | `d4d77622765d986cb46cbbe0b79fdfa6b18d9099ec53129c877b4cfc0e6f367f` |
| same-family source route | `5b797e286e5ce787e31d4a63a2a70981f03c0b3d1077677cfd4c216c223efa70` |
| original H attempt | `686d0970affd4c16aa82d87156fdae96ee6a48548a886212059d824e53651a48` |
| top-level inference principles | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |

Decisive immutable Oracle blobs:

| Path under infer/src | Git blob |
| --- | --- |
| `lowering/expr/mod.rs` | `5bbedd550c1edf877f4a7c254548ea02f47bcae8` |
| `lowering/name_ref.rs` | `929e21b022c5f7015c8168fb936ba590691100a4` |
| `lowering/local.rs` | `5b60e91edc1ff194486fe3292b53b292bf54d529` |
| `lowering/expr/lambda.rs` | `724b103cda8b4e2c457aacf0a674372fb191e3d6` |
| `lowering/body/mod.rs` | `f33bdfb5525ddcee02eba9bcd8c181acd1f9ea99` |
| `constraints/machine/bounds.rs` | `365ed25a8b3b7e468a7a4e57159125be53209708` |
| `constraints/machine/entry.rs` | `d75544523281cc7f5c6f1778fbe25eb42b7dfe7b` |
| `constraints/proof/mod.rs` | `3410858a5bfa0bc0073ab4988b2541738807abf5` |
| `constraints/row_effect.rs` | `d33c8d34f14dd5acc3b995050f4e9f7fa07ade25` |
| `compact/collect/mod.rs` | `2e0e8ac841e7240ee3b6b8db23915233f7ab832e` |

The method shares immutable source and H with the constructive proof lane;
it is complementary source evidence, not independent review or a second
semantic oracle. There was no executable model, seed/range, mutation run,
Oracle call, build, test, network request, compiler instrumentation, Git
mutation, child delegation, model-policy change or question-board write.
The conceptual P+ mutation remains the supplied arm send. Failure/omitted
cases include resource-terminal admissions, proof-ledger failures,
parameterized families, other skeleton modes, unknown scheme selection and
all universal H cases beyond this source.

Budget: 30-minute static lane; zero heavy processes and zero measurement or
execution samples. At most three independent lightweight reads were batched;
later reads were bounded and sequential. CPU/RSS and exact total wall time
were not instrumented. Initial combined captures were truncated and decisive
inputs were reread narrowly. Guessed absent `body.rs`/`body/definitions.rs`
paths were replaced with the actual `body/mod.rs` owner; chained empty grep
results were rerun with separate reads. No conclusion relies on those missing
reads. Runtime model/effort metadata was not supplied to this leaf.

One next action: have the constructive lane prove or refute the **first
positive T exposure / c_TR upper-claim registration invariant** over the
actual already admitted skeleton replays, using the internal S versus public Q
map above. This is a different source-owner premise from the earlier fresh
receiver argument. Stop if an authentic qualified parent or alias subsumption
invalidates it; do not spend the exhausted Oracle budget or substitute another
transition-assuming probe.

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-12-same-family-recursive-skeleton-source-audit.md`; frozen at handoff.
- Baseline: Y3 `50df6083366debd9fe534860c6a0ed01d5049208`; Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none among the checked direct inputs; no source dependency edited.
- Review status: unreviewed research source map and conditional replay derivation; no self-review, theorem promotion, H closure or source-qualified counterexample.
- Checks already run: immutable source/owner reads, direct dependency equality/diff, SHA-256/blob checks and final leased-note integrity checks; zero executions/builds/tests.
- Proposed checkpoint message: `research: map recursive run skeleton and T-return claim premise`.
- Shared-record deltas intentionally left for primary/curator: correct the recursive run reference owner in the source-route record to the named local self binding; retain its empty predicates for the actual construction reason; distinguish internal skeleton D from public wrapper R and public root Q; keep original H, P+ success/output and production gates OPEN; record the exact c_TR claim-registration premise. No shared task/index/authority or question bundle changed.
