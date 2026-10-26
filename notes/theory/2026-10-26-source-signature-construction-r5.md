# Source signature construction: registered support and origin routes

Date: 2026-10-26. Baseline supplied by primary: `977883577`, `yulang3`.
Author: `/root/source_semantics_route_r5`.
Status: **constructive static source-frame slice; independent review pending**.
The full original inference soundness theorem remains OPEN.

## 1. Outcome and exact boundary

`YulangClosure/SourceSignatureConstruction.lean` constructs a finite registered
port-frame graph, its complete support catalogue and its finite original
provenance developments. It gives separate original edge/development grammars
and a constructor-directed compiled representation, then proves their exact
correspondence. A real Call builder allocates all six original regions and
every registered arm before constructing the Call node. It derives the static
source-frame component associated with the original `sourceCallIncidence`
atom from that construction.

This removes an actual structural task: the caller no longer supplies an
arbitrary global origin/placement relation, successful source typing, a legal
source tree, or a promised correspondence theorem for the represented graph.
The compiler constructs the edges from the source constructor and the proof
recovers every finite origin/support development at the same indices.

It does **not** interpret the entire original Kernel atom as this smaller
static relation. The new relation is explicitly `StaticCallIncidence`.
Original field-schema authentication, source/environment registration,
semantic descriptor/phase/C0 laws and the complete original admission domain
still have their original owners. The file does not define a concrete
`OriginalSource.Kernel` or `SourceProblem` instance. It contains no native
success-to-source-judgment theorem and no production change.

## 2. Original sources and scope

The selected authority is
`notes/design/2026-10-08-native-signature-formation-definition.md` §§2–4,
which selects the source-signature-incidence construction's §§2–6 and their
reviewed scoped consequences. The construction uses:

| Original source | Constructed part |
| --- | --- |
| `2026-10-08-source-signature-incidence-construction.md` §3.2 | Concrete operand, root-insertion, reference, scope and renaming routes |
| Same, §3.4 | Origin occurrence families, separate owner/receiver indices, complete alternative and conjunction schemas, finite registered reference developments |
| Same, §§4.1 and 5 | Support independent of license inhabitation; constructor-directed certificate graph |
| Same, §7 | Original/compiled finite edge, support and provenance correspondence |
| `2026-10-08-call-source-interface-construction.md` §§3–6 | Complete Call's callee, whole carrier, CalRet, receiver, result, dependent future and arm slots |
| `2026-10-08-call-source-interface-definition.md` §§2–3 | Static slot incidence is distinct from semantic membership or live authority |
| `2026-10-08-source-generalize-definition-and-proof.md` §§3–6 | The source-directed App atom and the unchanged genuine L1–L5 boundary |

This is a first slice of the adopted signature construction, not a claim to
have formalized every declaration/license/attachment/whole-transform rule of
Theorem SIG. In particular no arbitrary `LegacyLicense` or unspecified
composite applicability predicate appears as a purported solved leaf.

The raw source reference is the actual imported `OriginalSourceSyntax.lean`.
Call nodes retain the raw resolved callee and argument, full source context,
mark/annotation metadata and all original operand sites. Generic image nodes
retain their original `Rule` tag. Compiled nodes retain the entire source
node literally, in addition to computed fields and edges.

## 3. Constructed representation

`Catalogue Joint` contains an arbitrary port index type, each complete
dependent packet type `Packet whole port`, its original binder scope and its
registered slot-sharing action. Port families and packets need not be finite
or inhabited. A finite registered graph is not a finite enumeration of
worlds, providers, semantic witnesses or future demands.

`Introduction Joint` contains the actual owning source identity, introduction
occurrence, origin kind, whole catalogue and independent primitive/local
license fiber. These are genuine original leaf inputs. Static construction
does not prove the fiber inhabited or authenticate a fabricated primitive.

`Node` has separate constructors for primitive introduction, alternative,
conjunction, operator image, Call, reference, scope, renaming, root insertion
and annotation. Reference, scope, insertion and annotation nodes introduce
no new local owner. Operator/Call nodes retain only their supplied genuine
local introductions alongside every antecedent region. This separation is
the adopted primitive/local boundary; authentic local operator laws remain
required at their owner.

The graph carrier is total on supplied data. This slice does not prove that
every arbitrary graph is an authentic source registration or that every
reference is allocated. Original finite support/provenance developments check
the actual node lookup at every traversed edge and at their endpoint. The
Call builder proves allocation and retention of its immediate region nodes;
global source graph formation remains part of the authentic input bridge.

`SourceEdge` is an independent constructor grammar. `Node.edges` calculates
the compiler's concrete edge list. `source_edge_exact` proves both directions
for every constructor, including every indexed Call arm and image operand.
There is no incidence predicate argument in this theorem.

`PortProv` describes finite original provenance developments that end at a
genuine introducing record. `Developed` describes finite developments in the
compiled graph. `provenance_iff` proves that compilation preserves and reflects
the same original introduction and the entire actual contextual route.
Registration cycles remain graph edges; a finite origin development must
still terminate at a genuine introduction.

`Occurrence` keeps the introducing object and whole route as data. Its owner
is read from that introduction. Its import classification is computed from
the route. It is not recomputed by comparing owner and receiver IDs.
Insertion constructs a distinct `Placement` receiver and extends the route;
it preserves the original introduction and import history.

## 4. Complete support and dependent packets

`Support` and `ContextualSupport` contain an actual catalogue port and an
original finite source path. They require no primitive license or selected
alternative. `BuiltSupport` and `BuiltContextualSupport` are independently
represented compiler objects. Their construction preserves the complete
packet type, actual registered slot-sharing action and original route.

`support_path_iff` gives exact original/compiled contextual path correspondence.
`compile_contextual_packet` retains the literal complete dependent packet
type at the same transported whole tuple. No body is run and no latent
provider/future contract is selected afresh by this equation.

Original reference and rename actions are explicit whole-row functions
retained at their registered substitution identities. `routeAction` applies
each actual action once, in the actual outside-to-inside route order.
`reference_action_once` and `route_action_append` give their exact equations.
They assume neither commutativity nor idempotence. The local actions' genuine
original legality is still an input of the selected interface construction;
this file does not claim to infer it from a numeric substitution handle.

`LeafLicensedField` preserves a primitive/local packet and its actual license
witness at one retained origin. Insertion has a left inverse and is injective
on this whole record, so two distinct license records cannot be merged by
placing them at the same receiving slot. This is deliberately **not** the
whole `DeclContribution` judgment. An enclosing alternative's selected-branch
evidence and an operator's actual governed-license-field correspondence are
still needed before that leaf is a licensed projection of a whole
contribution. Neither the support grammar nor this record manufactures such
an applicability witness for an unselected or empty branch.

## 5. Actual Call construction

`CallRegions` retains complete callee, whole-argument, CalRet, receiver,
returned-result and dependent-future nodes, plus every registered arm node.
`installCall` appends these exact objects and then appends the raw Call node
with its computed addresses. It does not search for a node with an equal
endpoint, inspect a successful comparison or discard an arm with an empty
fiber.

The useful construction result is:

```lean
raw_call_static_incidence
  (graph : Graph Joint) (context : OriginalSource.Context)
  (mark : OriginalSource.Mark)
  (callee argument : OriginalSource.Source .expression)
  (regions : CallRegions Joint)
  (locals : List (Introduction Joint)) (result : Catalogue Joint) :
  StaticCallIncidence
    (installCall graph context mark callee argument regions locals result)
    (callAtom context mark callee argument)
```

The source atom has exactly the App inventory's original site/context and
ordered `[callee.site, argument.site]` operands. No already registered Call
or complete Call certificate is supplied to this theorem.

`installed_region_node` returns the exact child object at its freshly
constructed address. `installed_call_arm` and `installed_arm_support` do the
same for every original indexed arm and every port of its full catalogue.
`installed_old_node` preserves every old allocated node. Existing
registration and whole-substitution tables remain the same objects.

These are static interface constructors. A CalRet slot is a dependent schema;
it is not a value that has already returned. A future slot is the original
provider-dependent interface, not a call made during compilation. All
semantic cases still need their original actual field interpretation.

## 6. Decisive owner/receiver issue

The repaired source requires more than preserving a scalar owner label.
`reference_stays_inherited_at_equal_owner` proves that an occurrence moved
through an actual reference remains inherited after root insertion even when
its original owner literally equals the receiving registration. Equality of
IDs therefore cannot justify a fresh local or direct-upper interpretation.

`conjunction_occurrences_distinct` proves that the two conjunction origins
remain different occurrences even when all their original owner and
introduction data coincide: their actual left/right routes distinguish them.
This preserves multi-origin and repeated-use information before applicability.

`no_introductions_no_provenance` proves that a graph with no genuine
introductions has no finite origin development, including cyclic reference
graphs. `no_new_origin` transfers that fact to the compiled graph. A support
schema can still exist there. This is a static constructor theorem, not a
source-program rejection policy or a semantic recursion counterexample.

## 7. What is ready for the seven original Kernel fields

The original Kernel fields are in
`OriginalSourceGeneration.lean`, `Kernel`. Their original independent meanings
remain necessary; naming a relation after an atom is insufficient.

| Kernel field | Exact constructor direction | Remaining original input |
| --- | --- | --- |
| `atom` | Constructor-by-constructor original local relations; the current slice supplies static Call-frame/support/provenance components | Authentic source/environment-to-frame registration, full dependent field identification, semantic local Call/C0 and all other atom cases |
| `admitted` | Original typed telescope records at each description/shared/view/event binder; invocation challenges retain the complete independent domain | Full original context/history/world/annotation interpretation; do not define admission by body acceptance |
| `primitiveCheck` | Authentic primitive declaration and its independent local whole-tuple checking law | Actual primitive catalogue and its original law; no whole-source axiom |
| `structuralShape` | Exact record/union/intersection/top/constructor and complete operand incidence, with recursively checked children | Original descriptor membership and scope/field schema identification |
| `functionShape` | Same-callable checked-domain/source-observation shape with original challenge and retargeted observation indices | Genuine domain/observation derivations and full independent contextual domain; recovered interpretation already proves the selected same-provider operator theorem |
| `boundaryTag` | Original source-normalization/annotation rule and actual Value/Computation entry tag | Authentic written annotation syntax and its selected original interpretation; latent endpoint shape cannot supply the tag |
| `conversion` | One actual admitted source-boundary adapter with its complete code/effects/input/output/evidence tuple | The independent local adapter law and its actual boundary realization; no direct-boundary transitivity |

No contradiction in these original sources was found. There is a genuine
definition/correspondence boundary: the selected contextual Function source
explicitly leaves its complete independent context and descriptor
admission/observation interpretation as inputs. The recovered
`OriginalSourceInterpretation.lean` already supplies the positive four-component
operator and its fixed point; duplicating it does not instantiate those inputs.
The proposed exhaustive `TypedCallCert_Dec` declaration in
`2026-10-26-original-call-evidence-construction.md` is expressly unadopted.
This packet does not adopt it by changing a Lean name.

## 8. Parent application and next construction

The immediate parent application is to replace supplied static source
placement/provenance premises inside the adopted IF/signature route with the
actual builder and the original/compiled correspondence above. The resulting
static component can be used by a faithful original `Kernel.atom` clause once
its source-owned typed schema and environment identification have been supplied.
It cannot by itself turn scalar native success into `Satisfies kernel`.

The next related construction should formalize `DeclContribution` with its
actual selected alternative, paired same-row evidence and original local
operator license-field projections, then the independent L/A introduction
grammars and their compiler/readback maps. The current leaf-license record
must not be substituted for that whole judgment. Genuine primitive/C0 and
annotation evidence stays at its owner.

A complementary concrete packet is the actual LocalSource-to-OriginalSource
registration map, retaining written annotation syntax, binder identity,
source scopes, whole-instance event and every original Call input. The Rust
`candidate_call.rs::PendingCallSupplier` list contains unresolved producer
requests; it is not a semantic certificate that can fill that map.

The later native-success seam remains: construct one original shared
`nu,K,D`/event witness, interpret every generated local clause by its genuine
owner law, and prove the native completed constraint/evidence object satisfies
that full source formula. Existing `generated_constraints_imply_source_judgment`
then applies. Assuming that satisfaction or original soundness in a newly
named interface would not be progress on that seam.

## 9. Verification

The exact final checks, root signatures, all originating declarations and
axiom sets are recorded in the assignment handoff. The isolated scratch tree
is `/workspace/scratch/c10e953a5453/source-route-r5/`. The pinned runtime is
Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, with one thread,
Lean memory limit 1 GiB and each focused checker bounded to 120 seconds.

No source form was removed, no original context domain was narrowed, and no
whole-language inference theorem is claimed. Independent review, integration
and all Git operations belong to the primary.
