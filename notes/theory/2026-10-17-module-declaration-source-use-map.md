# Module declaration publication and the complete source-use map

Date: 2026-10-17
Status: frozen producer construction; independent review pending
Author: `/root/module_declaration_source_use_map_proof`
Sprint: `module-use-source-map-and-provisional-observer-20261017`, revision 2
Contract SHA-256: `e575fed444457c34bc229c5f10ca6510d8fb85d9e4ecc3f582f485d72952ec6e`
Baseline: `26ccc56f1`; assignment freeze commit: `adfabe718`
Claim classes: actual source/native structural evidence; conditional source
interpretation and unadopted formation extension
Original conditions discharged: **0**
Source: exactly `my id x = x; my answer = id 0`
Semantic adoption / compiler modification / production authority: none

## 1. Parent application and result

The target is the publication/use step of
[ordinary Call generation](2026-10-17-ordinary-call-original-generation.md)
§7.2, step 2, at its original `B,X,xi,Delta_c,d_id,u_id` indices. The
declaration root, source-use root, candidate definition row, candidate Name
row and proposed registered contract root are distinct objects.

There are two concrete results. First, the current compiler constructs an
authentic declaration-to-module-use route, including a definition terminal
link, publication before external use, original use identity and a common
freshening map. Second, §§4–6 construct a complete source-use interpretation
from the source-rule program, without taking a binding certificate as input.
The construction supplies the whole typed substitution, including logical
and event binders, instead of only fresh type endpoints.

The missing identification is precise: the original module-reference
formation family must identify this syntax-directed publication/instance
annotation with its own actual source event and complete operand telescope.
The Rust route does not supply that identification: its row map is not a
map of all source-rule binder classes. Thus this note fills the mathematical
construction requested by §7.2 conditionally but does not substitute an
authentic original `mu_id` or `b_use` into that step. Original-family root
embedding and complete Call applicability remain separate downstream work.

The all-source parent, A/B requirements, F1/FK1 quantifiers, N-Transport,
soundness, principality and termination are unchanged. No failure to construct
a certificate is interpreted as rejection of this ordinary source.

## 2. Inputs and the declaration actually selected

Write `d_id,L_id,d_x,u_x,u_id,a_0,c,d_answer` as in the parent note §2.
These are symbolic names for original occurrences; no numerical ID is
invented. In particular `Resolve(u_x,d_x)` and `Resolve(u_id,d_id)` have
different targets. The fixed source contains no annotation, conversion,
capture, recursive reference or common-formation node in `id`'s RHS.

The selected Source Generalize definition adopts its construction §§3–5.
Those sections supply Parameter/Name/Result/Lambda, typed owning records,
FinalRoot, publication-indexed closure and finite-use allocation. The local
semantic premises L1–L5 remain their original premises. This note constructs
open programs; it does not assume their satisfaction, an admitted runtime
binding, successful inference, or a complete native descriptor interpretation.

Expanding `Build(L_id)` introduces `A_x` once at the Parameter type scope.
The body Name references that declaration, Result retains the same returned
provider, and Lambda keeps entry, Force, Return/rebind, body and complete
invocation ports. Let the resulting **whole** scoped program be `P_id` and
its complete synthesis root be `r_syn`. These names denote the constructor
outputs, not the abbreviated displayed type `A_x -> A_x`. All original
clauses, alternatives, guards and primitive operands remain in `P_id`.

FinalRoot has a determinate branch here: no written/final annotation or
actual common formation exists, so `r_id := r_syn`. This is an application
of the selected FinalRoot rule to this syntax. It is not the theorem that
the candidate row's graph denotes `r_id`, nor the assertion that
`r_id = VP(I,A_x,A_x,IF)`. The earlier `id` descriptor bridge proves only
its stated skeleton/conditional interpretation and cannot supply that equality.

## 3. Actual compiler route, at the frozen source bytes

The following are structural source facts on the candidate source route.
They are not semantic typing certificates or runtime measurements.

| Actual owner | Construction for this source | Exact limit |
| --- | --- | --- |
| `candidate_source.rs`, `emit_candidate_source`, definition terminal branch, lines 1140–1160 | With no annotation, emits `Action::Link` from the actual RHS endpoint to the definition root component and stores the definition schedule. | A native link, not a complete FinalRoot derivation. |
| `candidate_source.rs`, ModuleDef Name arm, lines 962–964 | Emits the original occurrence, resolved `d_id` target and parent, plus `Action::Module(u_id)`. | No formal `d_x` is registered for this module Name. |
| `lib.rs`, pending-use endpoint pass, lines 1320–1390 | Resolves the actual target in the complete definition table; stores `DefinitionUseId`, cause, parent, target, original Name occurrence, use level, use component and target-root component. | Source/provenance incidence; neither semantic provider nor binding-validity evidence is invented. |
| `candidate_scheme.rs`, `execute_candidate_graph_plan` | Runs member schedules, captures each definition graph at boundary 0, stages all member graphs, publishes them, then clears the live component's roots/uses. Uses dependency-first SCC order. | Publication of candidate graphs, not the `Published(p,Sigma_p)` source constructor. |
| `candidate_source.rs`, `Action::Module`, lines 1370–1374 | Routes an active internal use through `route_candidate_open_use`; otherwise through `route_incoming`. | Both alternatives remain. External use is not inferred merely from source order. |
| `candidate_scheme.rs`, `route_candidate_graph` | Reads the published target's actual live root/boundary/frontier, recaptures it, and instantiates the captured graph for that actual use. | No inference that a native row denotes every complete semantic field. |
| `candidate_scheme.rs`, `prepare_candidate_fresh_use`, row loop | Uses one canonical-row map. Freshens a local row only above capture boundary and when not nongeneric; otherwise shares it. Repeated canonical source rows reuse the same image. | Native eligibility test, not automatically SRC's provenance-based eligible set. |

For the fixed dependency graph `answer` refers to `id`, while `id` only
refers to its formal. They therefore have no recursive dependency cycle.
The existing dependency-first plan puts the target component before the
consumer; `u_id` is external to `id`'s component, so its Module action takes
the published-graph route. This uses the existing plan invariant documented
in the pinned module-expression construction §§5,10.4; it does not establish
a new all-source SCC theorem. The latter note's old line numbers/hashes are
historical. The owner facts above were checked against this sprint's current
pins, and the changed `candidate_scheme.rs` was read directly.

The selected use remains separate from the target root even when constraints
later identify representatives. The route has no reason to create a second
initialization of the closure. This is compatible with fixed provider
semantics, but compatibility is weaker than the original provider certificate.

## 4. Minimal proposed interpretation, with no circular certificate input

Define an unadopted annotation constructor `ModulePubUse*` for this fixed
resolved source. Its inputs are the original source/binder graph and the
actual local rule signature `Sig` used by `Build`; `Sig` has its full operand
telescopes, arm identities and original local laws. No input is `b_use`,
`ModuleTyped(id)`, `GenCall`, `P_id` satisfaction or a solved type.

The constructor performs these operations in producer order:

1. Build the declaration program of §2. Retain its actual source origins and
   its local rule derivations. Select `r_id` by FinalRoot.
2. Mark the immutable declaration boundary with static publication label
   `p*=(d_id, publication)` and validating component `C*={d_id}`. This label
   is proposed formation metadata, not a claim that an initialization ran.
   The source has no mutual member, so no member relation is discarded.
3. Apply the selected SRC §5.1 two-mode walk to the **entire** `P_id` and
   root. This computes fixed anchors `K`, retained graph `N`, and eligible
   ordinary declarations `Q`. Do not use free-variable spelling or the
   candidate row-level rule to calculate `Q`. Keep all constraints incident
   to fixed fields. Set `G*=ScopedClosure(p*,C*,T,K,Q,N,r_id)`.
4. At the actual resolved occurrence `u_id`, introduce the proposed static
   instance label `i*=(p*,u_id)` and annotate that occurrence with the
   existing client form `new(p*,i*,d_id)`. There is exactly one such use in
   this source. This is a proposal for the missing module-to-client
   annotation; calling it existing syntax does not prove that the original
   module rule emits it. It adds no executable operation.
5. Apply SRC §5.2's existing `new` allocation to that complete frame. Retain
   the source handle, target resolution, every mapped clause and binder,
   and the final-root incidence in the output `b_use*`. Its root-reference
   field is `r_use* := mu*(r_id)`. Store the constructor derivation that
   produced these fields; no binding certificate is a premise of this step.

This is a concrete construction, rather than an existentially chosen map.
The complete original catalogues stay parameterized where L1–L5 require
them. No extra successful primitive or local admission law is supplied.
If an authentic owning rule introduces a dependency into `K`, it is followed
even when it makes `A_x` fixed. The construction does not guess an exhaustive
descriptor telescope from the displayed identity type. In the explicit
Parameter/Name/Result/Lambda records, the own closure's raw provider is fixed
and its inferred relation is Internal; that fixed provider alone therefore
does not fix `A_x`. Any further fixing requires an actual dependent field,
not a reinterpretation of Internal as Established.

An already monomorphic source handle would instead require SRC's alias
route. No rule in this note converts it to `new`; the proposed step 4 is
only for this module reference. Its equivalence with the original source
module classification is precisely an outstanding embedding premise.

## 5. The map on every field and its scope proof

`mu*` is a map of typed presentations, not a function on endpoint values
alone. Let `q` range over declarations of `N`, `sigma(q)` be their original
scope, and `deps(q)` their original typed dependency incidences. Construct
the translated scope tree by SRC allocation first. Define declaration
images as follows, then extend through all original term constructors,
clause operands, root addresses, guards and reference argument lists.

| Original field/class | Image and sharing |
| --- | --- |
| Source occurrences, `d_id,d_x,u_x,u_id`, resolution target, primitive declaration/arm identity | The same original identity; the source edge `u_id -> d_id` is retained separately from the image root. |
| Provider, allocation/world/lifetime, Intrinsic, Established, OneShot | The same original field or same scoped base binder, with its complete dependent tuple. No new provider is allocated. |
| Shared | One original base binder. Every reference uses it, including references from the new description frame. |
| Eligible `Desc(C*,q,sort,sigma,Delta)` | `(i*,q)` at translated `sigma`; dependencies are `mu*(Delta)`. One image per declaration, including all repeated occurrences. |
| Ineligible/fixed ordinary Desc | Its existing field or binder, with its dependencies. Eligibility is never reversed by a later Internal edge. |
| Internal component references | References into this one mapped complete component frame, including all background conjuncts and original equation arguments. |
| ViewLogic | One `(i*,q)` binder in its translated description region, below its description dependencies and above its challenges. |
| Event / EventField | Original event origin and actual-parent/occurrence key at the owning event telescope; the source runtime operand is shared for that event. A new description frame does not create a runtime event. |
| EventProof | `(i*,actual-event-key,q,proof-region)` under that event with the mapped description dependencies and the same runtime operands. |
| Rigid opening / inference existential | Retain its own original binder kind, guard and dependencies. It is not eligible merely because it occurs in this frame. |
| Check / Specialize | The original finite local proof grammar, owning scope and premises, with one coherent operand map; no delayed specialization is invented. |
| Published / Family imported bound parameters, if required by an actual local operand | Retain the closed family and its own binders; traverse actual free anchors. No second family instantiation is inserted. |
| Root, all constraints and witnesses, every allowed alternative/guard | Homomorphic image using the same map and binder incidences. Nothing is projected to a successful arm or single literal challenge. |

For bound event fields this describes a dependent schema: under each actual
event substitution the existing source event key is used. It is not a
compile-time choice of an execution history. Raw operational identity and
description-owned proof witnesses remain different fields even when both
have existential syntax.

**Well-scope lemma.** Every image has its translated original type, and
every dependency edge has the image of its original source and target.
Proof: induct over the original binder tree. Base anchors and Shared keep
their original preceding telescope. A template is placed at its old type
scope and its dependencies have already been translated. A ViewLogic binder
is placed only after those dependencies. Challenge and event binders keep
their nesting, and EventProof is introduced only below its actual event.
All clause/reference operands use this same induction environment. At a
registered recursive edge, map its stored argument tuple and refer to the
registered image node; do not unfold or reorder it. Type dependencies are
scoped even when the relation graph is cyclic. This proves the claim for
each finite graph presentation and all its finite developments.

**Whole-tuple lemma.** Shared source incidences remain shared, distinct
instance-owned declarations are distinct in their proper classes, and
every original conjunct, alternative and guard is incident to the mapped
whole tuple. Proof: allocation memoizes by the owning class and full
scope/event key, never by printed endpoint or family name. Each clause is
copied with exactly its original arity, binder position and argument list.
Simultaneous substitution preserves repeated arguments, conjunction, union,
constructor images and registered references. It creates no new choice of
the actual provider or any fixed witness. This is SRC allocation applied
to the explicit frame, not an additional F1/FK1 foreign-continuation lemma.

## 6. Introduction, inversion and exact conservation statement

Let `E_mod(S)` be the proposed module annotation from §4, interpreted by
the already selected SRC Build/ScopedClosure/allocation operations. Define
`G_mod(S,Sig)` to be that resulting open scoped program, with the annotated
use partition. This reduct is fully specified; it is **not** identified
with an unprovided original module emitter or with the Rust row graph.

**Introduction.** For genuine applicable local `Sig`, `ModulePubUse*`
constructs its canonical retained record before constraint satisfaction.
Build supplies the declaration children and owning records; FinalRoot
selects its root; finite dependency closure supplies `K,Q,N`; allocation
supplies every image in §5. Each field of `b_use*` is an output of those
operations. This proves a formation statement. Runtime membership follows
only with the original local semantic premises and satisfaction required by
SRC/GS, not merely from having constructed the record.

**Inversion.** Eliminate the canonical constructor and its retained
children. This recovers the exact declaration boundary, resolved source
edge, complete `P_id`, FinalRoot branch, two-mode closure, full map and
mapped-root reference. The reconstruction cannot yield `d_x` as the module
target or a body-only root. It also cannot recover an independently
registered original contract root: none was constructed here.

**Conservation relative to the stated reduct.** Let `erase` remove only
the added retention fields and `retain` attach these fields to a canonical
derivation of `G_mod(S,Sig)`. Then, up to a single coherent binder-label
convention, `erase(retain(g))=g` and `retain(erase(g*))=g*` for canonical
generated `g*`. Proof is induction over the just-listed constructors;
the map and binder incidence table are the same at each step. Erasure
drops no constraint, guard, witness, event, alternative or executable
operand. Therefore the open program has exactly the same scoped strategies
and public observation fibers as this reduct, including when unsatisfiable.
For an arbitrary legal substitution, apply it to all retained derivations
and source-use coordinates simultaneously; constructor induction proves
that erasure commutes with that action. No independent fieldwise choice of
a witness or provider is allowed.

This does not prove that an earlier original module semantics is this
reduct. In particular, source admission is not proved unchanged merely by
calling step 4 administrative. Establishing that comparison is the explicit
next embedding task. No adopted semantics or successful ordinary inference
is redefined by this research proposal.

## 7. Field-by-field comparison with native evidence

The native route supplies the original occurrence/target/parent identities,
separate definition and use components, source level, capture boundary,
candidate graph and coherent canonical-row map. It preserves the map's
repeated-row incidences and restores captured bounds before route publication.
The local-use retention correspondence is reusable only for its actual
retained data at its valid projection cut; it explicitly leaves semantic
`At(D,w,delta)` authentication and whole-presentation transport open.

Neither inspected route emits `Desc`/`Shared`/`ViewLogic`/`EventProof` owning
records or a derivation relating its row eligibility test to SRC's fix walk.
Nor does a definition root component identify a complete source final root,
an immutable binding provider and its certificate by itself. Native scope
remapping, source levels and semantic binder scopes have different types;
equality of their indices is not a bridge. A source origin attached to a
graph node must also be shown to preserve the dependencies and witnesses
of each semantic coordinate represented by that node.

A useful falsifier is supplied by SRC's own Shared/ViewLogic distinction:
two independent frames requiring `s=0` and `s=1` are inconsistent for one
Shared `s`, and can be consistent for two ViewLogic binders. Endpoint
freshening alone cannot decide which judgment applies. This is a logical
separation test for a prospective bridge, **not** a counterexample from the
fixed one-use source or an assertion that the compiler confuses those cases.
The native bridge must produce the owning classification, rather than assume
that all logical witnesses copy like type rows.

## 8. Substitution into the parent and the remaining owner obligations

In parent §7.2 step 2 the proposed record can now be written explicitly as

```text
Decl* = retained Build(L_id) plus its actual FinalRoot derivation
G*    = ScopedClosure(p*,C*,T,K,Q,N,r_id)
mu*   = the complete allocation map of §5
b_use*= ModulePubUse*(S,Sig).use_record
R_f*  = ModuleContractRoot*(Decl*,b_use*,mu*)
```

This removes any need for an additional *assumed binding certificate* inside
that proposed constructor. It does not erase the asterisks. To obtain the
original step, the owner must establish the following precise bridges:

1. **Module source embedding.** From this actual immutable declaration and
   resolved module Name, derive the original publication/use rule instance
   with this exact new/alias partition, final-root selection, provider/base
   anchors and complete telescope. Show that its rule program is
   `G_mod(S,Sig)` at the original `B,X,xi,Delta_c` indices. The proposed
   static event tags must map to the actual source registration; nominal
   equality of tags is insufficient. Owner: module declaration/reference
   formation, using selected SRC §§3–5.
2. **Native interpretation, for the compiler claim.** Construct the
   original semantic coordinate interpretation of the declaration capture
   and actual `FreshUse`, proving the commuting equation for the whole
   tuple and all scopes, including fixed witnesses and dependent clauses.
   Owner: source generation plus capture/fresh-use transport. The current
   source/native route in §3 supplies its real structural inputs. This
   obligation is not silently inserted into a purely source theorem, but
   is required before claiming that the compiler emits that theorem's map.
3. **Original root registration and Call formation.** Embed `R_f*` into the
   original registered root family, validate the complete generic Call
   operand telescope and literal argument case, then embed the resulting
   occurrence into original `Gen-Call-0`. Owner: original module contract
   root/Application formation. `r_use*` is a field of `R_f*`, not a cast
   from synthesis roots to registered contract roots.

Only after the needed original source embeddings does the parent's O0
theorem apply to an authentic `e_c`; Code-Call retains its other independent
premises. No O0 calculation is repeated here. The three bridges are
evidence requirements within existing parent obligations, not three newly
closed gates or newly imposed restrictions on source admission.

The smallest next discriminating step is to define and review the original
module source embedding in item 1 against the actual original root family,
using this fully constructed map. If that comparison reveals a materially
different source new/alias rule, provider, final root or observable behavior,
return that difference to Luna. A new constructor name alone is not such a
difference. If the comparison is conservative, the user's standing permission
allows it to proceed through independent review/adoption without another
ceremonial permission request.

## 9. Construction costs, verification and freeze

The proof annotation can use a finite explicit graph walk. Let `n` count
retained graph nodes, binder/field records and dependency incidences,
including operand-list storage. A deliberately simple implementation using
linear membership lookup for visited `(mode,node)` pairs and image keys
takes `O(n^2)` time and `O(n)` retained/working storage for this single use,
using compact graph-node identifiers and fixed-arity parent/key records
rather than repeatedly comparing expanded scope paths;
each edge is processed a bounded number of times after lookup. The two-mode
closure is monotone; Internal cycles terminate through visited pairs.
The original scoped graph, tags, map and derivation references are retained;
trees are not unfolded. This bound concerns the annotation construction on a
finite applicable rule presentation, not constraint solving, catalogue
enumeration, global inference or semantic proof search. With `k` independently
allocated clients, explicitly copied frame storage can be `O(kn)`; this
packet has one incoming module use. No optimized bound is needed for the
proof, and none is claimed for the current Rust implementation.

If implemented later, allocation should occur in private construction state
with checked sizing; incomplete annotations must not be published. A resource
failure may abort that attempt. This proposes no new source rejection limit,
rollback guarantee or algorithmic retry. The user's complexity permission
allows the conservative walk; it does not prove global termination or lift
this assignment's time cap.

For a subsequent implementation packet the minimal evidence TODO is to
retain the owning source-rule field classification alongside capture and
the corresponding full image incidence at use. Reconstructing such a sidecar
from authenticated retained source is also a possible, more costly route;
the absence of named SRC tags in Rust does not prove that reconstruction is
impossible. The falsifier is a copied coordinate whose original fixed/shared
binder or dependent witness has no corresponding image, or an image that
changes the source new/alias partition. Neither an observer returning the
module target nor a test of a native row map discharges this TODO. This is a
request for a later exact lease, not permission to enlarge the concurrent
candidate observer slice.

Only read-only source/document/hash inspection and proof construction were
performed. No tests, Cargo/builds, probes, execution experiments, compiler
edits, Git or descendants. Only this note and its exact handoff were written.
Requested model/effort: `gpt-6-astra` / medium; observed model/effort: UNKNOWN.
The handoff records the frozen artifact hash, input hashes and resource receipt.
