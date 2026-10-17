# Adopted module exposure at the exact `id` occurrence

Date: 2026-10-17
Revision: 1
Status: candidate local derivation under adopted authority; fresh review pending
Author: `/root/adopted_module_application_proof`; no descendants
Sprint: `module-reference-materialization-20261017`, revision 2
Contract SHA-256: `64c89cb6566de76cfaca4cf483ae278d16720962358db1ec6a2d016d9e11aa77`
Baseline supplied by Luna: `2b563076a0ac2c4f0b66a277c1b557dac8134313`; no Git inspection
Original global theorem conditions closed by this author: 0

## 1. Claim, authority and scope

The parent is the unchanged original Yulang inference/execution theorem. Its
local target here is `HINTRO-OWNER-u_id`, the publication/use operand in
[original-generation §7.2(2)](2026-10-17-ordinary-call-original-generation.md),
for exactly `my id x = x; my answer = id 0`. Fix the original
`B,X,xi=(nu,K,D),Delta_c,d_id,u_id`; do not specialize them to a solved world,
a printed identity type, a Call demand or one successful strategy.

The [adopted definition](../design/2026-10-17-module-environment-exposure-definition.md)
selects the exact formation/elimination of the frozen materialization rev2.
The result below applies that definition and the original Published
Name/Instance and SRC allocation rules. The user decision is formation
authority; this note supplies the local application derivation. This author
neither independently certifies it nor closes a gate pending fresh review.

Precisely, for the fixed source and the genuine local signatures and L1–L5
premises already required by the parent, the adopted formation constructs the
Published entry at this exact binding incidence, its expression-use owner,
and the complete open `b_use,mu_id` below, before satisfaction. It supplies no
registered Application contract root. It does not prove equivalence with the
previously unspecified module admission/observation relation.

## 2. Prior publication and exposure: no handle premise assumed

Keep the actual source graph:

```text
d_id = module id; L_id = its Lambda; d_x = L_id's formal; u_x = its body Name
u_id = answer's callee Name; a_0 = Integer(0); c = Apply(u_id,a_0)
Resolve(u_x,d_x); Resolve(u_id,d_id)
C_id = {d_id}; C_answer = {d_answer}; dependency C_answer -> C_id
```

There is no return dependency. The two components are distinct and `C_id` is
dependency-prior. This is a calculation for this finite source graph, not an
all-source SCC or runtime initialization theorem.

Reuse [source-family §§2–3](2026-10-17-module-source-family-embedding.md) at
its genuine local-signature premises: expand Parameter, body Name, Result
and Lambda at `(d_id,L_id,d_x,u_x)` to obtain the complete open `P_id` and
inert closure anchor `a_id` with the actual empty capture. Parameter's one
`A_x` is shared by the body Name. The module binding is `d_id`, not `d_x`.
FinalRoot selects the complete synthesis root `r_id`; it includes the
original invocation and latent interfaces and is not replaced by `Int -> Int`,
VP or Echo. SRC §§5,5.1,5.3 give

```text
(K_id,Q_id,N_id) = FixRetain(p_id,C_id,T,P_id,r_id,a_id)
G_id = ScopedClosure(p_id,C_id,T,K_id,Q_id,N_id,r_id)
D_pub : original publication derivation installing Published(p_id,G_id) at d_id.
```

`D_pub` retains the independent local source derivation required by SRC
§3.4, at its actual scopes and actual binding, as well as the complete
publication construction. It is not merely a computed closure or a Build
success token. At formation, its local obligations remain open; the
independent source derivation at a satisfying assignment is read using the
original local rules/SRC, not assumed as a successful whole-source input.
No successful initialization, constraint solution or runtime membership is
used to form this publication.

Instantiate `ModuleEnv-Expose*` for `C_answer`. Its prior entry is the actual
output of `D_pub`; its incidence set contains the actual `u_id -> d_id`
edge. Its registration is `C_answer`'s original registration, and its ambient
scope map is the identity on the common original module telescope. Take the
dependency-closed restriction, retaining all free anchors and the entire
closed binder graph of `G_id`. The formal `d_x` remains inside that graph;
identity transport does not hoist its binder into the module environment.
Therefore the conclusion, rather than an input hypothesis, is

```text
Gamma_answer*(d_id at its actual binding occurrence/scope)
  = Pub(d_id,p_id,G_id,D_pub).
```

Exact resolution lookup at `u_id` selects that same node. Its composed
ambient map is the identity. This derivation uses the direct Published
projection expressly adopted for this dependency. No intervening Mono,
Alias, capture, conversion or rebind constructor occurs in this derivation.
It does not prove that an unspecified older admission judgment excludes such
constructors. No tag is inferred from provider equality, DefId equality,
Function shape, AST absence or a native route.

## 3. Published elimination and every use-map field

Apply the original Published Name/Instance to this selected entry and its
retained independent definition derivation. Let `i_id*` be the static
Instance-introduction origin at `u_id`, chosen before assignments, challenges
and histories. The coordinates are

```text
Instance(p_id,i_id*,d_id)
U_id = new(p_id,i_id*,d_id)
G_id; U_id; E_original |- allocate mu_id : J_mu(U_id,W).
```

The publication coordinate is `p_id`; `u_id` is separately retained use
provenance. `E_original` is the original finite local checking/elaboration
proof grammar with its original binders and unsolved clauses. Allocation
accepts that syntax before validity; it does not receive a valid-client
certificate. `W` is any well-scoped client predicate at its original scope,
including correlations to other incoming frames and aliases. Allocation
appends it unchanged and shares its incidences; no new successful checking
alternative is selected for this use.

Here is the complete dependent record, with its intensional graph payload
spelled out rather than replaced by endpoint types:

```text
b_use = (
  original_indices = (B,X,xi=(nu,K,D),Delta_c),
  declaration = d_id, occurrence = u_id, resolution = Resolve(u_id,d_id),
  binding_incidence = the exact d_id binding occurrence/scope,
  publication = p_id, publication_derivation = D_pub,
  exposure = the C_answer ModuleEnv-Expose* derivation of §2,
  scope_transport = identity on the common module base, with dependency closure,
  lookup = elimination at the actual Resolve(u_id,d_id) incidence,
  selected_entry = Pub(d_id,p_id,G_id,D_pub),
  instance = Instance(p_id,i_id*,d_id), client_handle = new(p_id,i_id*,d_id),
  source_anchor = a_id, component = C_id, original_tree = T,
  fixed = K_id, templates = Q_id, retained_program = N_id,
  source_closure = G_id, original_final_root = r_id,
  proof_grammar = E_original, allocation_derivation = SRC-Allocate at U_id,
  whole_map = mu_id, complete_open_image = J_mu,
  source_reference_root = mu_id(r_id),
  dependent_payload = the image graph defined below).
```

The dependent payload is the entire finite typed presentation of `N_id` and
`E_original`: every declaration and sort; binder/scope node; ordered typed
dependency edge; primitive/source rule and arm identity; every guard,
constraint, alternative and witness operand; all root addresses; and every
registered equation/reference with its full ordered argument tuple. The
map includes the handle map, declaration map, original/shared incidences,
event routing, proof-grammar nodes and final-root incidences. An opaque
original primitive retains its full declaration reference and argument
telescope; opacity never deletes a field. This is an exact graph-defined
record at the parent’s original symbolic signatures, not an enumeration
pretending that the displayed identity type exhausts those signatures.

Instantiate SRC §5.2 and [source-use-map §5](2026-10-17-module-declaration-source-use-map.md)
with `p=p_id,i=i_id*,r=d_id`:

| Original field class | Actual `mu_id` action |
| --- | --- |
| Source occurrences, declarations, resolution, primitive/arm identities | Identity, with original incidence; `u_id` remains separate from the root image. |
| Provider/allocation/world/lifetime, Intrinsic, Established, OneShot | Original fixed field or base binder with its complete dependencies; no new provider. |
| Shared | One original base binder across the complete joined client, with its original dependencies. |
| Eligible own `Desc(C_id,q,sort,sigma,Delta)` | One `(i_id*,q)` at translated `sigma`, with dependencies `mu_id(Delta)` and the original sort. |
| Fixed/ineligible Desc and foreign monomorphic free fields | Their original fields/binders; Internal traversal never reverses fixing. |
| Internal | One complete component frame with every member/background conjunct and original equation argument. |
| ViewLogic | `(i_id*,q,original description-region path)`, below mapped type dependencies and before its challenges; one binder per frame. |
| Event/EventField | Original event origin, actual parent-event path and occurrence key at the original event telescope; shared actual runtime operands. Fixed initializer events remain in the base. |
| EventProof | `(i_id*,actual event key,q,original proof-region path)`, below that event and its mapped dependencies, sharing runtime EventFields. |
| Rigid opening/inference existential | Original binder kind, scope, guard and dependencies; no automatic template eligibility. |
| Check/Specialize | Whole original finite local grammar at its actual check/authorized scope, with all local premises and operands. |
| Imported Published/Family bound parameters | Existing closed family and original bound parameters; traverse only actual free anchors, with no extra instantiation. |
| Roots, clauses, guards, alternatives, witnesses, reference operands | Simultaneous homomorphic image under this one map, with original arities and argument order. |
| join/bind and arbitrary `W` | Same joint context, actual Return/rebind/world or request/response/pending suffix incidence; `W` at its original scope. |

No independent field choices are joined after the fact. The allocation's
existing scope and whole-tuple lemmas apply because the entry and new-origin
premises have now been constructed. Dependencies precede their users;
ViewLogic remains pre-challenge; EventProof stays below its actual event.
A recursive reference targets the registered image with the mapped argument
tuple; it is not unfolded. Deterministic unfolding-path keys act uniformly
on every finite development without copying Shared binders or inventing
runtime events. This uses the existing allocation proof at its actual
premises and does not reprove or enlarge it.

## 4. Literal parent substitution, quantifiers and exact stop

In original-generation §7.2(2), make exactly the following substitution:

```text
Decl* := retained original (D_pub,P_id,r_id), including (d_id,L_id,d_x,u_x)
b_use* := b_use of §3
mu_id := the single SRC-Allocate map of §3
source-reference leg := mu_id(r_id)
R_f* := ModuleContractRoot*(Decl*,b_use*,mu_id)  [NO CONSTRUCTOR SUPPLIED]
```

This discharges the former handle-owner premise for this derivation under
adopted formation authority, subject to fresh application review. The first
next unavailable output is the typed registered `R_f*`, with its actual
registration derivation relating the source-reference leg to the complete
Application contract. `mu_id(r_id)` is a source-reference field; it cannot
be cast to `R_f*`. Stop here. In particular, this application does not yet
produce the complete parent `q_f` registered interface or `e_c`.

All unsupplied original operands downstream are retained explicitly:
registered `R_f*` and its original-family embedding; complete source `Sig`
Call applicability/telescope; callee `q_f` and `Comp(E_f,A_id_use)` at that
registered interface; Call-owned `q_0,o_arg,J_0`, Delay/Reify and whole carrier
registration (the Literal/Result child schema alone is available);
`F_c` with every receiver/result/future and dependency field; the full
VIncl/WholeArgCompatible/image/result clauses and `O_value,O_arg,O_result`;
checking occurrence `u`, `beta*=(d_id,R_f*)`, `p0*`, `p_out(c)` and genuine
Function-elimination/ElimOrigin; authentic `e_c` and original formation
embedding. No original formal seed is supplied or needed by this module
branch. The complete native `Phi_u` and the source/native interpretation of
every field also remain unsupplied. These are named missing outputs, not
new premises silently assumed in this local result.

The substitution holds at the same arbitrary original `B,X,xi,Delta_c`, not
one selected assignment. Its syntax and fresh-label schema are fixed before
public assignments, challenges, histories or `W` satisfaction. For every
original ambient assignment and every original joint scoped strategy,
retain the same original guards, independently admitted domains and event
transitions. If that strategy satisfies the allocated clauses plus arbitrary
well-scoped `W`, SRC-J gives the independent joined source derivation at
those same indices; no satisfiability assertion is made when it does not.
Conversely, for every finite independent joint proof grammar `d_U` with `W`
at these actual Published incidences, GC supplies its finite allocation
schema before assignments/histories, preserving its whole solution and
observation fiber. GC retains its quantifier order:

```text
forall finite independent joint d_U and well-scoped W,
  exists finite allocation schema m_d, before assignments/histories,
    Fiber_independent(d_U,W) = Fiber_clauses(J_m_d(U,W)).
```

This is reuse of SRC-J/GC on the classified source derivations, including
empty fibers, not a proof that arbitrary raw-source admission has those
derivations. It does not identify the one displayed `mu_id` with every
checking grammar's independently constructed `m_d`, nor exchange their
existential/universal order. No original foreign continuation, compatible
context, finite history or future has been narrowed to this local frame.
F1/FK1's independent quantifiers, N-Transport, soundness, principality,
termination and the global theorem remain OPEN. A single local map action
proves none of those independent claims.

## 5. Source/native evidence and next owner requests

Read-only source evidence at the pinned bytes:
`candidate_source.rs:962` emits `PendingDefinitionUse { parent,target,occurrence }`
and `Action::Module`; its action consumer at 1370 routes active internal
uses through `route_candidate_open_use`, otherwise `route_incoming`.
`candidate_call.rs:295` exposes the actual ModuleDef through
`module_callee_target`; its `suppliers` at 388 retains
`OriginalGenCall0`, `ModuleNameSourceTypingAndAdmission` and
`ModuleUseReceivingExportCorrespondence`. Those records establish source
routing only. They do not emit the semantic exposure derivation, full
`b_use`, registered root or total `Phi_u`. No test of assumed transitions
was used as evidence of actual semantic emission.

The frozen FreshUse retention proof is reused only for its actual retained
native-map ownership through route removal or GraphState/frozen-result
lifetime. It does not classify Published or interpret the complete source
field graph. Actual native correspondence, levels, extrusion, qualifying
intrusion, generation/accumulation/propagation and generalization are not
changed by this document.

TODO `MODULE-REGISTERED-ROOT-u_id` (Luna / source Application-registration
owner): input the frozen `D_pub,b_use,mu_id` plus the genuine original Call
registration declaration; produce the typed registered-root construction and
its original-family embedding, with full dependency telescope. Falsifier:
the output is only a root equality/cast, lacks a required original operand,
or chooses a narrower public/function root than the actual source contract.
This is the first next mathematical condition; no new rule is authorized.

TODO `MODULE-NATIVE-FIELD-MAP` (Luna's source/native contract lane, then a
separately leased implementation owner): identify entry creation, occurrence
lookup, complete dependency incidences, lifetime/invalidation and every native
image. Required output is a total field correspondence at the frozen source
operands. Falsifier: a purported Published tag comes only from target/provider
identity or routing, any mapped source field has no coherent native image,
or a retained map outlives its semantic owner. No compiler edit is leased by
this TODO; if implementation evidence is needed, return a minimal provisional
slice with that falsifier to Luna before writing code.

TODO `ADMISSION-EQUIVALENCE` (Luna / original module source-judgment owner):
compare the adopted formation with the older whole-source admission and
observation relation at all original scopes and client correlations. The
metadata-erasure lemma for already classified derivations cannot erase the
new exposure inference. A missing old owner or any additional admitted
source derivation defeats a claim of established equality. This independent
question remains open and does not invalidate the new local derivation under
the explicit user-adopted authority.

Prior work reused at actual premises: source-family declaration/publication;
SRC §§3.4,5.2; complete source-use-map field/scope lemmas; retention only on
already classified derivations; native retention only for ownership. The
historical conditional Published result lacked an occurrence owner; adoption
and §§2–3 now fill that local premise rather than renaming it. Rejected
shortcuts remain GC inversion from untyped input, same-provider/DefId
classification, AST exclusion of Mono, native-route authentication,
final-root/registered-root casts and foreign-continuation closure from local
naturality. No withdrawn bypass or lineage identification is restored.

## 6. Freeze and resources

Four substantive stages: governing inputs/pins; publication/exposure;
Published whole-map and parent substitution; source seam/quantifier audit and
freeze. Cap 240 seconds, no descendants, code/tests/Git or external contact.
Exact launch time and elapsed active duration were not exposed to this
worker: UNKNOWN; conservatively charge the whole 240-second grant. Requested
model/effort: `gpt-6-sol` / high. Effective observed model/effort: UNKNOWN.
A clock read during work was 2026-10-17 13:47:14 UTC; this is not a launch or
elapsed-duration measurement. Contract pin correction was received before
reading contract bytes; the obsolete dispatch/current-state pin
`6e81912a...` was not used as authority for a written result. The corrected
contract and all direct inputs matched the frozen hashes in the handoff.

Checks were document/source inspection, constructor/scope/quantifier audit,
SHA-256 validation and final readback. No executable semantic probe, build,
test, compiler edit, Git, nested CLI or extra/scratch path. Exactly the two
leased files are written. This is a candidate local mathematical derivation
awaiting independent application review, with zero global theorem conditions
claimed closed. Writer STOPs after freezing the one handoff; no waiting work
or descendant lease remains.
