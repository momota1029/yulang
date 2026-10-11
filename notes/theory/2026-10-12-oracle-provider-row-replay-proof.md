# Oracle provider: concrete row replay and the returned callback output

Date: 2026-10-12
Status: frozen producer derivation; independent review pending; original H OPEN
Claim class: bounded source-to-consumer derivation under normal admission/query completion
Y3 baseline: `148db454b6417890572a577ce4ea1c9618b59b52`
Oracle baseline: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Oracle read root: `/tmp/yulang2-oracle-read`
Exclusive lease: this file; leaf; no delegation, execution or Git mutations

## 1. Frozen statement, dependencies and scope

The source slice is the resolved, ordinary top-level fragment:

```yulang
pub act tick:
    pub ping: () -> ()
my direct(cb: (() -> [tick] ())) = cb
my provider() = tick::ping()
my observed_direct() = (direct provider) ()
```

Here `tick` denotes the actual resolved effect-declaration path, rather than
an independently chosen family with the same spelling. Unit and tick have zero
type arguments. These declarations have no result annotations, local schemes,
self uses, roles, imported/copy ancestors or other outgoing value references.
The source slice, fresh allocation, successful resolution, and normal completed
queue/admission/query/finalization without terminal resource/proof failure are
the operational hypotheses. The last hypothesis does not assert that an earlier
Oracle process produced a particular record dump or output. No such dump is used.

Governing authority is [hygiene integration](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–2 and [top-level inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5. The task boundary is `tasks/current.md`, §2026-10-12 Oracle direct-return
projection boundary. The accepted P/S/K image and the fresh-use maps are consumed
from [the direct-use note](2026-10-12-oracle-direct-use-discharge-proof.md), especially
§5. Their proofs are not repeated here.

**R.** In this slice, provider's installed positive Function has the concrete
result Effect `Row([Con(tick, [])])`, with no result-Effect variable, SubtractId or
stack. Its actual ordinary use in `direct provider` admits this Function at the
provider-use Value coordinate. Native replay compares its result Effect with
direct's instantiated negative callback `Row([Con(tick, [])], NegVar(x_u))`.
That actual comparison matches the prefix and emits no consequence to `x_u`.
In particular it does not instantiate a weighted-variable residual γ. Native
replay also activates the returned annotated callback against the outer
application's complete four-port Function demand. At observed_direct's output
collection, no concrete tick lower is reachable at its result Effect; its
remaining positive-only Effect aliases are eliminated and that exported port is
`Pos::Bot` (pure). This is a bounded inference/export result, not a theorem about
arbitrary providers or surrounding sources.

Original [H](2026-10-11-oracle-global-effect-hygiene-proof.md) §1 retains every
successfully lowered source-program and composed-negative occurrence quantifier,
the original scope and binders, every actual copy/use/call/output route, and
the independent same-family survival and retained-check requirements. R does
not promote H or prove/refute its complete operational independence/attachment
claim. Incoming uses of direct/provider act on fresh instantiated schemes,
not their original definition coordinates. Other source programs, recursion,
copy/import ancestors, parameterized tick, open rows, additional provider bounds,
and abnormal publication are omitted from R, not from H.

## 2. Actual operation constructor and provider predicate

All Oracle locators below are relative to `crates/infer/src/` unless specified.
The new construction starts at the actual operation reference, not at an
assumed installed provider predicate or a hypothetical tail lower.

### 2.1 The operation reference already receives its concrete Function

`lowering/expr/block_local.rs:990–1020` allocates the resolved operation-use
Value q and an exact-pure evaluation Effect, registers the RefUse, and queues
ApplyRefResolution. Crucially, :1015–1017 also calls
`constrain_act_operation_ref`. The selected target is the actual ActOperationDecl
for ping. The current sub-return target is provider, not ping, so the guard
at :1023–1027 does not suppress this hook. At :1029–1048, the hook builds
ping's stored signature, lowers it positively, and submits that predicate to
`NegVar(q)` with a native root origin. At :1050–1063 it also records the actual
resolved operation path in `poly.effect_operations`. This constructor operates
before any later ordinary scheme instantiation for this reference.

`:1066–1091` uses the operation declaration's own effect application.
`lowering/signature_helpers.rs:217–256` inserts it into the Function's return
Effect row, which initially has neither items nor a tail for `() -> ()`.
`lowering/mod.rs:571–617` lowers the Function's four ports. The positive
nonwildcard Effect-row branch at `lowering/signature_effect.rs:78–107` allocates
**`Pos::Row([Pos::Con(tick, [])])`**. It does not take the wildcard branch that
allocates an Effect variable and stack facts. Absent argument Effect lowers to
the empty negative Row (`signature_effect.rs:19–26`); both Value ports are
nullary Unit. Write this concrete operation Function as

`Fping = Fun(Unit−, Row([], Top), Row([tick]), Unit+)`.

The Act operation declaration itself lowers the same positive signature
(`lowering/body/act.rs:112–127,147–195`). Its original scheme therefore adds
the same concrete Function when the queued global use is instantiated. Neither
the early hook nor the subsequent closed operation scheme creates a symbolic
tick tail. They may add duplicate provenance/semantic arms; no second port shape
is introduced by those arms.

### 2.2 Provider's own body has a finite unweighted forwarding graph

`lowering/pattern.rs:109–115` and `lowering/expr/constraints.rs:73–91` constrain
the unit formal both below and above by Unit. The unannotated-lambda defaults at
`lowering/expr/lambda.rs:1244–1265` use `Neg::Bot` for argument Effect, with no
annotation predicate or call upper. The global ping reference is not a local
parameter call (`lowering/expr/tail.rs:690–705`). Its application at :535–628
creates result Value r, call Effect c and expression Effect e, then submits

`Var(q) <: Fun(Unit-argument+, pure-argument-Effect+, NegVar(c), NegVar(r))`.

This is a complete Function demand, including the argument Effect and both
result ports. The Function comparison owner at
`constraints/machine/propagate.rs:212–271` produces `Row([tick]) <: c` and
`Unit+ <: r`. The argument-Effect comparison is against Fping's empty negative
Row and contributes no tick. The callee evaluation Effect is exact-pure.
`:615–624` forwards that evaluation Effect and c to e. The body wrapper at
`lambda.rs:797–808` forwards e to the fresh skeleton body Effect B and r to
the fresh skeleton body Value Y, then uses B/Y in the exported Function at
`:954–975`; `lowering/expr/mod.rs:309–341` connects its Value to public root R.

The internal skeleton is distinct from the public Function. In this unannotated
unit-formal definition, `lowering/local.rs:133–145` makes
KnownBeforeBody.connects_empty_predicate false. Thus the annotation-enabled
Y↔layer-output and B→layer-output links from direct's earlier construction
are **not** imported into provider. The body forwarding e→B and r→Y is still
unconditional. There is no self reference linking the internal skeleton back
to the public output. The same observation applies to observed_direct.

Every alias on the concrete tick path `c → e → B` is unweighted. Its targets
are ordinary definition/body levels; extrusion lowers levels, preserves the
concrete Row/Function endpoints, and introduces no fresh result-Effect port
(`constraints/machine/bounds.rs:4523–4592`). The only negative Effect Rows in
provider's graph are empty checks of pure evaluation Effects. No alias on this
path has a nonempty negative Row or subtract fact.

### 2.3 Admission, replay, projection and simplification of that graph

The Function→q root is nontrivial and reaches add_lower_bound through
`machine/entry.rs:493–499,1092–1116,1349–1428` and
`machine/propagate.rs:150–163`. `machine/bounds.rs:630–733` inserts it, admits
its projection index, and schedules replay. Alias-cycle subsumption requires
a variable lower; it cannot remove this Function or the concrete Row lower.

The q→application-Function upper and c→e/e→B uppers are fresh native roots.
Their producer has no qualified parents, so the upper-claim constructor at
`bounds.rs:965–1033` supplies Direct claims. These are uncovered: the live
row-coverage owner is `constraints/row_effect.rs:490–525`, and its reduction
entry at :236–254 refuses an empty prefix. A Function upper or variable upper
cannot enter that nonempty-row reduction. Pure Effect checks have empty prefixes.

Whichever endpoint is admitted first, lower replay at
`bounds.rs:3406–3512` or upper replay at :3582–3645 enumerates the relevant pair.
`constraints/proof/mod.rs:9441–9530` requires generic pair replay for uncovered
upper roots. `bounds.rs:3832–3892` enqueues the consequence and installs its
actual parents. Function→Function and concrete Row→variable consequences are
not the evidence-only variable-to-variable case at :3814–3830. A canonical
duplicate points to the same already admitted semantic consequence; it cannot
replace the concrete Row by a fresh tail.

For projection, the q Function root has an independent root-origin support (or
the unclaimed case) at `bounds.rs:2600–2717` and
`proof/mod.rs:10014–10020`. Every forwarded concrete Row has the actual unary
structural or binary replay clause: its premises are the preceding included
Function/Row consequence and an uncovered upper. The constructors are
`bounds.rs:1188–1207,2476–2565`; the evaluator is
`proof/mod.rs:11648–11765,11883–11914`. Induction over the finite path above
therefore gives IncludedExact at c, e and B under normal validated query
completion. This uses the emitted/native parent incidence, not just the
existence of a stored lower. No nonempty row-coverage state occurs anywhere
in this induction that could exclude its upper premise.

`compact/collect/mod.rs:848–918` consequently collects the concrete Row at B.
The complete provider public root contains one merged Function: argument Unit,
argument Effect Never, result Value Unit and result Effect tick Row. Its other
components are positive-only root/body/evaluation/value aliases and a
negative-only unit formal alias. There is no alias shared across opposite
public ports, recursive bound, role, invariant interval, subtract fact or
neutral constructor argument. The internal self skeleton is not reachable
from this root. The generalization prepasses add no role/interval/cast work
to this root, and alias expansion only adds eligible aliases to these same
ports, not a new constructor or polarity (`analysis/session/generalize.rs:13–180,476–515`;
`generalize/mod.rs:662–699`).

The actual simplification boundary is root.child with empty non_generic.
All these native coordinates are at or above it. The polar constructor at
`compact/analysis/mod.rs:39–60,506–514` removes the positive-only and
negative-only aliases, retaining their concrete constructors. Both fixed
points therefore have no variable candidate left; no stack-cleanup or
quantifier step can synthesize a tail. Finalization at
`compact/finalize.rs:412–421,542–548,627–698` exports the concrete tick Row.
`generalize/mod.rs:177–238` selects no type/stack quantifiers;
`generalize/finalize.rs:3–29` and `analysis/session/instantiate.rs:14–83`
install the ordinary top-level scheme. Its relevant predicate is exactly

`Fprovider = Fun(Unit−, Bot−, Row([tick]), Unit+)`.

This derives the installed predicate from provider's actual operation hook
and body graph. It is not a premise imported from a displayed surface scheme.

## 3. The actual provider use and the selected row branch

The dependency graph has provider→ping and observed_direct→direct/provider,
with no return edges. `scc.rs:266–313,328–356` emits QuantifyComponent before
InstantiateUse for these incoming acyclic edges. `analysis/session/selection.rs:1041–1117`
routes those events, so observed's compatibility constraints cannot mutate
the original provider/direct scheme coordinates before their quantification.

Consume the accepted direct-use image:

| Actual direct-use component | Constructor |
| --- | --- |
| negative callback N_u | `Fun(Unit+, Bot+, Row([tick], NegVar(x_u)), Unit−)` |
| returned callback A_u | `Fun(Unit−, Row([], Top), Stack(PosVar(x_u), PUSH α_u), Unit+)` |
| root activation Q_u | `POP α_u` with count `u32::MAX` |

The two occurrences of x_u and α_u use the same instantiator maps. The result
Value's nullary Unit wrapper does not supply another Effect coordinate.
Instantiation of Fprovider has no quantified coordinates or stack entries to
rename. `analysis/session/instantiate.rs:488–520,717–725` selects its plain
Function direct-lower route. `machine/entry.rs:734–752` admits Fprovider at the
actual provider-use Value p with an independent Origin support, then merges
scheme provenance and drains. This is actual admission, not a premise that
scheme witness completeness alone implies replay.

The first application admits the complete demand D1 at direct-use Value d.
Q_u is normalized onto its lower-side weight (`machine/propagate.rs:11–24`).
The Function→Function comparison's argument rule at :228–235 swaps weights,
so the actual compatibility consequence is

`PosVar(p) <: N_u`, with weights `(left=empty, right=Q_u)`.

That Function upper has uncovered original/inherited roots: it descends from
D1's Direct Function demand, not a nonempty Row reduction at p. Admission of
Fprovider before or after this upper thus triggers the real generic pair
by the two replay owners in §2.3. All four ports are compared. Unit→Unit is
nullary; the Bot argument-Effect lower is trivial, including the provider
NegBot passthrough case. The substantive provider Effect comparison is

`PosRow([PosCon(tick, [])]) <: NegRow([NegCon(tick, [])], NegVar(x_u))`,
with that same `(empty, Q_u)` weight.

`machine/propagate.rs:330–335,708–830` selects enqueue_row_items. The singleton
item is nonvariable and matches the same resolved path in the upper prefix
at :726–737. It is removed from remaining_upper_items. No item is placed in
variable_items, row_tail_items or direct_tail_items. The matching constructor
at :925–990 compares invariant payload arguments; the argument vector has
length zero, hence it emits zero subtype consequences. The final inverse-tail
helpers at :1044–1100 receive empty vectors, and their constructors at
:1102–1132 return None. Therefore there is no forward or inverse tail edge
at x_u, no lower of tick at x_u, and no payload-induced x_u relation.
This conclusion holds for the actual Q_u weight; it does not require erasing it.

The scalar Con branch at :1007–1042 has the same zero-payload conclusion,
but it is not needed to change Fprovider's actual Row constructor.
The weighted-variable residual owner `constraints/row_effect.rs:88–234`
requires PosVar(source) as the lower of a nonempty negative Row. Its γ uses
the correlated source/retained-families/residual-weight cache key at :174–202
and links that same γ to the original tail at :221–233. No such source endpoint
exists in the concrete Fprovider return-Effect comparison. Nor is the
unweighted variable-row reduction at :236–347 selected here. Consequently
there is **no actual same-use residual alternative** to the prefix match in
this fragment. Adding a symbolic provider return tail would select another
source construction and cannot serve as this use's missing witness.

## 4. Returned callback activation and complete output projection

The first comparison also submits A_u to its fresh result Value r1 through
the FunctionReturn rule. The outer application has already submitted its
complete demand D2 at r1: unit Value argument, exact-pure argument Effect,
fresh call Effect c2 and result Value r2. This source is an ExprApp, not a
local callback binder, so no local-call projection/predicate replaces those
ports (`lowering/expr/tail.rs:535–628,690–755`). D2 is a Direct Function upper
with no live Row coverage. A_u's Function lower therefore replays against it
under normal drain completion, by the same actual admitted-pair mechanism.
It cannot be suppressed by the variable-to-variable evidence-only shortcut.

This establishes the activation premise that was conditional in the
direct-use note §5. Consume that note's already derived weight arithmetic:
at the returned result-Effect port, PUSH α_u followed by Q_u leaves a directed
POP count `u32::MAX−1`, with no active PUSH or tick budget at α_u. The actual
Effect consequence has source `PosVar(x_u)` and target c2. It is not a
concrete provider tick lower. The other three D2 ports are also consumed:
Unit Value comparisons have zero payload constraints, and the pure argument
Effect is checked against A_u's empty negative Row. No Function argument or
result-Value rule connects provider's tick to x_u.

For the complete expression output, first-call Effect e1 receives direct's
pure enclosing return Effect and its pure argument/callee evaluation Effects.
The first Function's NegBot argument-Effect passthrough uses
`weights.both_from_right()` at `machine/propagate.rs:236–253`; the first
direct comparison has right=empty, so this contributes only the actual pure
provider-expression evaluation Effect. It does not invoke provider.
The outer e2 receives e1 and c2 at `tail.rs:615–624`; its exact-pure unit
argument adds no tick. The unannotated observed wrapper forwards e2 to its
own B and r2 to Y at `lambda.rs:797–808`, exporting those exact coordinates.

The closed incidence census for x_u consists of its declaration/fresh-copy
facts, the negative callback Row tail (which emits no bound by §3), its
positive returned callback occurrence, and outgoing Effect aliases from
the activated callback. Subtract fact registration is not a positive type
lower. There is no operation constructor with x_u as target, no second
provider Function, no symbolic residual γ, and no independent native lower
of x_u. The only concrete tick in this use graph is nested in Fprovider at p;
after its prefix comparison it has no effect-forwarding edge to c2/e2/B.
Thus even allowing all ordinary/evidence aliases, native replay closure
cannot copy a concrete tick into the observed output component.

Output queries use the projection selector, not a raw scan. As in §2.3,
the Direct Function/alias roots on this output graph are uncovered; the
qualified structural/replay consequences have included premises. A weighted
variable alias may be stored as evidence by :3814–3830, but
`constraints/mod.rs:2664–2672` and `compact/collect/mod.rs:848–918` enumerate
evidence records as well. Hence storage disposition is not an assumed lost
tick witness. Inclusion can preserve x_u/alias occurrences; it cannot create
a tick constructor absent from every output lower endpoint.

Collecting observed's public Function visits the unit formal negatively,
the Unit result positively, and B positively. It does not follow p's
negative callback upper from B. Secondary alias collection at
`compact/collect/mod.rs:1102–1159` and positive alias expansion at
`generalize/mod.rs:662–699` add variables in the same output port, not
arbitrary Function-demand parents. All output Effect aliases, including
x_u if retained in that port, therefore occur only positively in this root.
The direct-use allocator starts x_u at TypeLevel.secondary
(`analysis/session/instantiate.rs:448–455`; `instantiate.rs:732–738`);
`constraints/mod.rs:409–417` makes that `u32::MAX`. Extrusion ages it through
ordinary use/definition coordinates, all at depth at least one. No bound in
this source graph has a root-depth-zero target. Thus the actual root.child
simplification boundary admits all these aliases; empty non_generic supplies
no exception. No role, neutral payload or recursive bound adds a negative
x_u occurrence to observed's public root.

The first polar pass removes these positive-only Effect occurrences together
with their POP-only weights. The compact result Effect is empty. Neither
fixed point, stack cleanup, type/stack quantifier selection nor ancestor-free
export introduces a constructor into an empty port. Specifically,
`compact/finalize.rs:542–548,711–722` sends an empty Effect through ordinary
positive-type finalization, and :136–169,785–799 exports it as `Pos::Bot`.
The installed observed_direct Function therefore has a pure result Effect.
This covers the actual application evaluation/call/output forwarding ports;
the result is not inferred from cancellation alone or a printed scheme.

## 5. Parent mapping, residual scope and checks

| Lemma established in this note | Parent seam discharged | Owner |
| --- | --- | --- |
| actual operation hook and provider installed concrete Row predicate | provider predicate premise in direct-use §5 | block_local/signature/body/generalize |
| admission of Fprovider at its actual use and generic uncovered replay | provider comparison activation premise | session instantiate / machine entry,bounds / proof route |
| prefix consumes nullary concrete tick with no x_u consequence | actual prefix-versus-residual lineage decision | propagate enqueue_row_items; row_effect branch exclusion |
| A_u admitted at r1 and compared with D2 | outer activation premise | tail full demand; FunctionReturn; bound replay |
| complete output incidence, levels and simplification | inferred observed output projection seam | tail forwarding; lambda body roots; compact collect/simplify/finalize |

R closes this bounded static inference/export seam under the stated normal
completion hypotheses. It supplies no numeric record IDs, event counts or
authenticated successful-run admission/disposition dump. A claim about an
earlier particular execution still needs that execution's record, not R's
symbolic finite construction. No extra conditional tail witness remains in R.

The original H gate remains OPEN. Turning the bounded pure inferred Effect
into an H counterexample or closure requires the original complete Call and
independent-contribution correspondence: the exact source/runtime route that
returns the provider Value through cb and invokes that same provider, and
the authentic origin/attachment classification of its ping contribution for
the original annotation occurrence. The next owner is the original H
source-to-operational/attachment lane; substituting another marginal residual
or recasting the unchanged cancellation arithmetic does not establish it.
R does not assert soundness, principality, general provider completeness,
all successful programs, or abnormal-path nonpublication.

Static checks: inspected every owning constructor/consumer listed above;
read the governing sections and frozen direct-use §5; verified both pinned
HEADs and dependency hashes; checked this Markdown's links and absence of
trailing whitespace. No Oracle run, build, test, probe, Git mutation, code or
shared-record edit. One leaf, no spawned jobs; no benchmark/process measurement.
Requested runtime Sol/high; observed model/effort metadata unavailable (unknown).
The bounded allowance is 40 minutes; only static file reads and this leased
write were used. Producer output requires fresh independent review.

## Dependency fingerprints and commit packet

The Oracle source identity is the pinned repository SHA above. Accepted
dependency SHA-256 values at freeze:

| Dependency | SHA-256 |
| --- | --- |
| direct-use discharge | `b9b2552ff6a681b04eab443a251e500138586a727e83b6ca542f1fd74ed74c80` |
| P | `0799b609879e52de59fdd58b8b71bc8035eca6b1d953f3c4c4ae0743e465afa7` |
| S | `affb7a0fe174c755877fe09bc2633c488b53bc0281ba6cd2082bb7a85aac0535` |
| K | `f87f09b54ee64e1be6a22fffd059f0cae4aeb2e340d7dbcca1809280947a8cd5` |
| hygiene integration | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| top-level principles | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |

Exact changed path: `notes/theory/2026-10-12-oracle-provider-row-replay-proof.md`.
Baseline: `148db454b6417890572a577ce4ea1c9618b59b52`. No changed dependency
hashes. Review status: producer derivation, independent review pending; no
self-certification or shared status promotion. Checks are those listed above.
Proposed checkpoint message: `research: derive Oracle provider row replay and output projection`.
Shared-record deltas left to primary/curator: record the bounded provider
predicate, prefix/no-tail branch and outer activation/output result; keep H
OPEN with the original operational independence/attachment owner and scope.
