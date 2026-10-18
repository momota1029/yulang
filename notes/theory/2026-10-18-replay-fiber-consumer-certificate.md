# Replay fiber and Function consumer certificate: source refinement

Status: source-audited conditional candidate; independent review NOT RUN.
Constructor equations below are derived from the pinned source; their
application to two concrete fixture routes is conditional on the absent
runtime coordinate rows and successful checks. No concrete two-use
certificate or consumer execution is asserted. Author
`/root/replay_fiber_consumer_proof`; descendants 0; requested Sol/high,
observed model/effort UNKNOWN/UNKNOWN. Sprint
`npair-replay-fiber-consumer-certificate-20261018`, rev1, contract SHA-256
`fce2f48df81227bfc427503fb785541835865f4c0970dbc27a514ff9f8cbb565`;
supplied baseline `f56022c19`. All source statements below refer to the pinned
baseline bytes, not concurrently edited implementation bytes.

## Parent and result boundary

`CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN. Its original
accepted domain, same original contribution `c`, providers, observations,
assignments, worlds, contexts, occurrences, typed positions, guards,
continuations, interactions, Call demands and futures are unchanged. F1 and
FK1 remain independent. Adopted NPAIR P3 requires every reached contribution,
including future lowers and alternative routes; P4 requires the complete
dependent presentation through capture, generalization, extrusion and
qualifying Value-SCC intrusion. This fixture supplies a diagnostic subroute,
not the original receive/choose source or its fixed-c judgment.

Reuse the CLEAN conditional criterion
`2026-10-18-replay-ancestry-authentication.md` at SHA-256
`00603a98b9f66eb71c61c0fe80e8812ff059c6cde54abd2d91e02036674381f6`.
The new result is its constructor/API refinement with separate copied-bound,
Replay and consumer coordinates, exact endpoint/transformer equations, and
an explicit list of missing fixture observations. It rejects the previous
implementation's conflation. It does not rename that conditional criterion
as a completed concrete experiment. Original conditions closed: **0**.

## Exact two-use evidence schedule

The public graph fixture at the baseline is exactly:

```yu
my invoke f = f 1
my id x = x
my first = invoke id
my second = invoke id
```

Its original demand owner is the Apply `f 1` inside `invoke`; `first` and
`second` name the two distinct caller occurrences. Select an actual retained
Replay dependency first. The requested route is then tied to the corresponding
source use occurrence, never chosen by a matching tuple afterward. For a
module route its owner is `GraphState.routes[j].use_id` and the matching
`DefinitionUse` occurrence. For a local route it is
`GraphState.local_routes[j].occurrence` and the matching Local owner. Use a
tagged route address; indices in these two vectors are separate namespaces.
`instantiate_candidate_graph` retains module maps in `FreshRoute`;
`commit_local_use` retains local maps in `LocalFreshRoute`. Baseline
`authenticate_demand_transport` visits only the latter, so its applicability
to the public fixture's actual route kind is not established.

Here is the concrete extraction table. Subscript 1 means the `first` use,
subscript 2 the `second` use. Every expression is an address in that inference
State, not a proposed numeric ID. Both numeric observation columns are
**MISSING**: the previous closeout records no execution of this two-use
fixture. The old single-use `q=61,l=58,h=35` row is not transferable.

| Coordinate | `first` use | `second` use | Exact owner/check |
| --- | --- | --- | --- |
| source demand | `k,t0` | same `k,t0` | source Call for `invoke`'s `f 1`, actual introduction/native demand |
| selected Replay | `e1=(q1,l1,h1,L1,H1)` | `e2=(q2,l2,h2,L2,H2)` | exact `State.dependencies` entry, including kind |
| source route/map | `r1,u1,M1` | `r2,u2,M2` | tagged route and its `retained.context_use`, `terms`, `scope_remap` |
| captured bound/source | `b1,p1src,B1src` | `b2,p2src,B2src` | `r.graph.bounds[b]`, `relation=Some(psrc)`, full `source_bound` |
| captured snapshot | `S1=graph.bound_evidence[b1.evidence]` | `S2=graph.bound_evidence[b2.evidence]` | complete snapshot value, including heads and coverage |
| imported antecedent | `a1=M1.evidence_remap[b1.evidence]` | `a2=M2.evidence_remap[b2.evidence]` | `State.evidence.snapshots[a]=S`, full equality |
| copied bound relation | `p1copy,B1copy,w1` | `p2copy,B2copy,w2` | actual FreshUse Transport, restored admission/emission/fiber |
| first spine | `p1copy → h1` | `p2copy → h2` | explicit checked demand-bearing edges; zero steps checks ID equality |
| Replay/recipe | `l1,h1 → q1` | `l2,h2 → q2` | membership in `L/H`, exact recipe dependency, ordered task pair |
| second spine | `q1 → C1` | `q2 → C2` | separate checked demand-bearing edges; zero steps checks ID equality |
| consumer whole pair | `F1+ <: G1-` | `F2+ <: G2-` | actual typed pair at C and both Function term views |
| four ports | `A1,AE1,RE1,R1` | `A2,AE2,RE2,R2` | actual FunctionPort dependencies, ordered field/pair/operation/flow |

`p1src` and `p1copy` in this table denote distinct roles; the latter is the
contract's `p1`. They must not be silently replaced by `q1`. Likewise retain
`h` and `C` as separate coordinates even when an actual zero-step equality
holds. Sharing the source relation or a nongeneric term between uses is
allowed; distinct use IDs, owned input/scope copies and owning maps are
checked where the fixture claims them. No global inequality between every
pair of relation IDs is assumed.

The baseline helper test uses a different literal:
`my outer z = { my local h x = h z; local }; my first = outer 0; my second = outer 1`.
It addresses LocalFreshRoutes and cannot instantiate the public fixture's
table. Its acceptance, zero-step cases and positive certificates are also
unobserved here. Preserve its separate source identity if retained as a test.

## Captured fiber to copied bound

`Capture::bound` enumerates the actual source bound's retained relation fiber.
For each bound it retains `relation`, `source_bound`, the structural graph
indices, side and kind, and an interned snapshot. The snapshot records the
admission and physical-emission prefix at capture time. Recompute neither
prefix from the later live group: later admissions may legitimately change
its heads. `prepare_candidate_fresh_use` imports each captured snapshot by
`import_evidence` and retains the resulting per-graph evidence map. Consequently
the verifier can compare the full saved snapshot with its imported antecedent.
Equality of `source_bound` and `relation` alone is insufficient.

For the selected graph bound, reconstruct both endpoints using its actual
retained terms/effect operands, original side and kind. For side Positive the
owner is the upper endpoint; for side Negative the owner is the lower. Check
the actual canonical destination B, not a polarity-free pair. With `p=psrc`
and `p1=pcopy`, require all of:

1. `S.relation=Some(p)` and `S.source_bound=b.source_bound`.
2. Actual `Transport{parent:p,child:p1,use_origin:u,witness:Some(w)}`,
   `w=(from:b.source_bound,to:B,reason:FreshUse)` and `u!=0`.
3. `pair(p)=bound_pair(w.from)`, `pair(p1)=bound_pair(B)`, and `p1` is in B's
   actual retained fiber. Pair equality alone is not membership.
4. Actual destination admission with `bound=B`, `relation=Some(p1)`, and cause
   `FreshUse{antecedent:a,use_origin:u,source_bound:w.from,mapped_relation:Some(p1)}`.
   Link its physical emission to that admission and bound; validate its
   `PhysicalBoundSlot` against the actual row/lane/index. Missing emission
   evidence remains missing even if the relation is attached.

The owners are `begin_candidate_fresh_bound`,
`candidate_context_fresh_transport_scoped`,
`candidate_context_reuse_fresh_relation`,
`candidate_bound_origin_with_evidence`, and
`candidate_insert_bound_with_evidence`. They retain these separate facts.
The old verifier checks none of the full snapshot/admission/emission chain.
FreshUse itself does not produce the later general `FiberTransform` record:
its direct witness, imported antecedent and FreshUse admission are its proper
evidence; requiring an unrelated general transform would reject this constructor.

Coverage gaps are preserved. In particular ordinary seed authentication,
processing antecedents and Replay-use antecedent coverage can be incomplete
despite exact direct snapshot/import/fiber association. This certificate
establishes the checked direct construction path only, not complete semantic
antecedent coverage or an original contribution derivation.

## Scoped equations and the two separate spines

Write source demand `D0=(k,v0,t0,s0,i0)`. Check it against the actual source
Call/introduction and captured relation flow. `candidate_context_seed` creates
the initial demand at local slot 0 with `v0=0`, `root=introduction.demand`,
`s0=computation_scopes[occurrence]`, `i0=InputRouteId(k)`. A later captured
relation may be a descendant; an asserted seed-to-capture route requires its
actual dependency evidence, never a guessed origin from a Function shape.

For retained map M of use u, let `j=graph.negative_functions[t0]`, and let
the actual negative Function node's children be `[ja,jae,jre,jr]`. Require
all five retained term entries. Structural reconstruction gives

```
t1 = M.terms[j] = Fun-(M.terms[ja],M.terms[jae],M.terms[jre],M.terms[jr])
D1 = (k,u,t1, M.scopes.get(s0).unwrap_or(s0), M.inputs.get(i0).unwrap_or(i0))
```

The use equation requires `M.inputs.contains_key(i0)`; borrowed inputs retain
their previous use in the constructor. Check the actual mapped flow stored
in `M.scoped_relations[p]`, including the transformer remap, then `flow(p1)`.
For this conservative zero-transformer fixture require both transformers 0.
Check `pair(p1).upper=NegativeFunction(t1)` after canonicalization. Canonical
endpoint reconstruction does not itself update the mapped demand root.

The first spine starts at p1 and ends at the selected Replay upper h. The
second starts at that Replay child q and ends at the actual Function comparison
C. Validate each as a finite explicit edge list. An empty first list requires
`p1=h`; an empty second list requires `q=C`. Root equality, shared tuples and
endpoint equality cannot replace either ID equality. The prior single-use
runtime proves neither zero-step equation.

For each supported Derived step x→y check actual edge, Value kinds, zero
transformers, demands at both ends, unchanged call/use/scope/input, and
`x.upper=NegativeFunction(Dx.root)`, `y.upper=NegativeFunction(Dy.root)`.
An unchanged upper requires unchanged root. This is the diagnostic root
equation of `candidate_context_value_rewrite`; the Derived tag does not certify
the semantic extrusion operation. For a supported non-FreshUse Transport,
also check full from/to fibers, retained constructor evidence and the literal
`transported_scoped` equation: inspect owner endpoints, then item endpoints;
the first endpoint equal to the old negative Function root supplies the new
negative Function root, otherwise the root stays. Unsupported kinds or a new
unauthenticated FreshUse reject. Preserve individual dependency identity;
reject cycles, ambiguity and unsupported competing demand ancestry under the
CLEAN criterion. Unrelated outgoing branches are not competing incoming
ancestry. A port's auxiliary Derived edge consumes demand and is not a spine.

Keep mapped root t1, Replay root th and consumer root tC separately. Along
these checked spines only root may change; k/u/s/i stay. Requiring t1=th
without checking a zero-change spine excludes legitimate rewrites. Reporting
th as the original copied root hides the same missing evidence.

## Replay recipe and actual consumer

For the already selected dependency `Replay{child:q,lower:l,upper:h,
lower_input:L,upper_input:H}`, check actual fiber membership, whole BoundKeys,
opposite polarity at the same owner, typed pairs, and the actual ordered
task pair. In a Value Replay the task endpoints must be the lower item and
upper item in that order. Require `recipe_keys[e]` to address an actual recipe
whose dependency is exactly e. The recipe has coverage gaps; retaining it
does not certify unavailable higher semantic antecedents.

`candidate_context_begin_replay` enumerates these fiber pairs, rejects a
lower demand, composes scope transformers lower then upper, and copies only
the upper demand. Thus check `flow(l).demand=None`,
`flow(q).demand=flow(h).demand`, and actual lower-then-upper transformer
composition. For this fixture both input transformers and resulting transformer
must be identity, so composition is checked without treating an arbitrary
nonzero ID as identity. This is an explicit strict subset of the CLEAN criterion.

At C require whole pair `PositiveFunction(F) <: NegativeFunction(G)`, actual
positive/negative Function views, `G=tC`, zero parent transformer, and demand
`(k,u,tC,s,i)`. Derive both sides' children from their actual views. For each
field require the following exact typed pair, operation and consumed flow:

| Canonical field order | Actual child pair | Operation | Transformer; child demand |
| --- | --- | --- | --- |
| Argument | `value_endpoint(G.a,+) <: value_endpoint(F.a,-)` | Swap | identity; None |
| ArgumentEffect | `effect_endpoint(G.ae,+) <: effect_endpoint(F.ae,-)` | Swap | `stamp_input(i)`; None |
| ResultEffect | `effect_endpoint(F.re,+) <: effect_endpoint(G.re,-)` | Preserve | `protect_body(s,i)`; None |
| Result | `value_endpoint(F.r,+) <: value_endpoint(G.r,-)` | Preserve | identity; None |

Every child has an actual `FunctionPort{parent:C,child,field,operation}` edge;
compare both typed endpoints, not only Value/Effect kind or the four G terms.
Use the owning endpoint conversion/canonicalization operation on the actual
whole pair. `lib.rs` supplies these four pairs and Function dispatch;
`candidate_function_port_admit` checks root and parent transformer, consumes
the demand, records the operation, and supplies exactly these transforms.
Compare nonzero transforms structurally using the canonical transformer owner:
`ScopeTransformer` has Eq. `stamp_input(i)` is precisely the singleton stamped
input and no scope entries; `protect_body(s,i)` has no stamped input and one
scope entry `(s,keep_initial=true,add=Missing({i}))`. Checking evaluation on one
empty state is insufficient for extensional equality. Transformer ID 0 is
canonical identity. No extra stamp, scope or release is allowed.

This table orders fields, not creation times. The Function drain admits its
children in reverse array order; a verifier must reconcile by exact field,
operation and edge identity. Never search FunctionPorts under h merely because
h carries the demand: h may be a row bound, while q/C is the whole Function
comparison. Port admission and later effect execution remain separate claims.
No retained dependency alone supplies a later consumer execution receipt.

## Derivation, falsifiers and parent application

The constructor proof is compositional: exact snapshot/import/admission and
FreshUse map equations give the selected p1 anchor; finite induction on the
first spine gives Dh; the actual Replay recipe gives Dq=Dh; finite induction
on the second gives DC; substitute DC into the real four FunctionPort
constructors. Direct zero-step ID checks are the base cases. Therefore a
successful verifier supplies the CLEAN criterion's local diagnostic result.
It cannot establish its own premise that both concrete fixture verifications
actually succeed. That observation is the present first missing evidence.

Required independent falsifiers operate on real retained evidence in a private
test State, with the unmodified positive control first: change a captured
snapshot head/coverage while keeping its call/use; replace an addressed edge's
dependency kind; remove the selected source/destination relation from its
actual fiber or alter its admission/recipe; change one actual port endpoint
while retaining field and operation; change an intermediate actual scoped flow
with unchanged route IDs. Each must reject for that check. Restoring bytes
between mutations prevents one earlier failure from masking another. A call-ID
change is not a snapshot test; a supplied observed-port swap is not an actual
port-endpoint mutation. The corrected two-position swap lemma remains useful:
only the swapped positions need fail, and their all-port conjunction rejects.
Endpoint falsifiers must select replacements that differ after the owning
canonical conversion; replacing an endpoint by its equal representative is
not an endpoint counterexample.

For local P3, this gives a checked route address on which separately proved
`At(D,c,delta)` could be transported. For local P4 it verifies the demand and
Function-field portion only. Neither constructs the original c, complete
provider/witness/residual presentation, future-lower association, or all
capture/generalization/extrusion/intrusion cases. P3/P4, fixed-c formation,
R/W/Z/domain, F1/FK1, N-Transport, complete Call, soundness, principality,
termination and production remain OPEN.

Mutual TODO `NPAIR-FIBER-CONSUMER-OBSERVE-20261018`: leased implementation
and primary runtime owners must fill both rows of the table from the exact
source-owned route kind, authenticate positive and independent mutated
evidence, expose zero/nonzero spine lengths and exact coordinates, and retain
`native_root_matches=false`. First falsifier: either normal route lacks an
exact captured/imported/restored/Replayed/consumed identity or a changed
evidence item still authenticates. No generic ancestry search or solver
semantic change is needed to state this test.

Original TODO `NPAIR-P3P4-DEPENDENT-TRANSPORT` stays with Operation/Call and
capture/generalization/extrusion/intrusion/effect consumer owners: derive the
same original c and full At at the accepted incidence, then preserve that
dependent judgment on all ordinary paths. This diagnostic experiment does not
reduce that original condition by itself.

## Pinned evidence and checks

Contract source pins and prior closeout hashes were checked byte-for-byte before
the concurrent implementation edits. Additional directly read owner pins:

| Path under `crates/yu-solver/src/` | SHA-256 |
| --- | --- |
| `lib.rs` | `ddd1395877d4a76e27a1dcf32af90c6fcb0e58c739610a0115c03955628350e1` |
| `candidate_effect.rs` | `9ea9498692bdff12c2a7ebd8546ca2b443a095c0700f3e87ad6c956cc690e212` |
| `candidate_extrusion.rs` | `2c535e0906a9cf6221fa4746ae815dc45ce18cf37f19a8e811f996d8422b7f6b` |
| `candidate_source.rs` | `1a65c7afb02a4afd538a34c34086108959579e06aafe8fbcab8ad6a6b3a65f3e` |
| `candidate_scope.rs` | `9fdb36b4bbd66d702fbd3fcfaf593bfbc5dce0c52ff3252442aeb998bbb52c2a` |

Parent scope: adopted negative-formal-pair proposal §§2–4/P3–P4 SHA-256
`0a73aaf7016e86dd5babbdd5482b05a793764418bc003607207ef0375ee46006`;
adoption receipt `d94e24656854fd2d67ed0f600619349c728dfafa26ca6e312f1faa6d3f3532fa`;
inference principles `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`.
Constructor proof reused at its premises:
`426b1bf969eb9628b73f5bcddec38b2f169d41341479dda4019965b34fad1244`.
No Cargo, tests, executable probe, Git, source edit, external contact, descendants
or scratch files. Fresh independent review and exact runtime release belong to
Luna. Resource and frozen artifact hashes are in the one assignment handoff.
