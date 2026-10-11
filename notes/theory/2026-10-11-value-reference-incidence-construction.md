# Value-reference incidence construction and polar transport

Status: frozen research-only construction and conditional source bridge; unreviewed
Parent all-source/all-history/retained-Value-pair theorem: OPEN
Baseline: `d8c097e1f810fb26a8cf1936aa97059f6948bf32`, `research/simple-sub-intrusion`
Exclusive lease: this file; leaf, no delegation

## 1. Frozen objective and evidence classes

For every supported source program `P`, every actual native inference history
`h` of `P`, and every retained distinct Value extrusion pair `(c,p)`, the
original obligation is to construct the actual Value-reference graph, show
that its qualifying mutual reachability is the relation used by the intrusion
consumer, and justify the selected equality with required typing safety and
principality through subsequent inference and generalization. An edge `u→v`
means an actual reference in the value represented/owned by `u` targets `v`.
The endpoints must be actual Value rows of the same history. Original binders,
scopes, shared captures, independent uses and distinct copies are retained.
References across levels and family branches are allowed. No comparison,
storage side, lexical containment or parent metadata supplies an edge.
Effects remain separate; complete Call and effect hygiene are not projected
away. No supported source is restricted and no parent gate is weakened.

This packet constructs incidence evidence without a total assignment of owned
syntax to every row. Its **bounded established construction facts** identify
joint original source coordinates and actual native port/remap coordinates.
Its **conditional derivation** describes transport once a source incidence is
matched to the corresponding native port context. Its **proposed invariant**
extends that interpretation to source references outside the visited typing
interface. That invariant is not established. There is no executable probe,
complete native graph theorem, source-qualified counterexample, or proof of
semantic impossibility here.

Authority: `notes/design/2026-10-10-parent-copy-scc-intrusion.md`, **Selected
operation and compiler responsibility**, **Value-reference SCC clarification**,
**Retained boundary**; `notes/design/2026-10-11-yulang-inference-top-level-principles.md`
§§1–5 and **Evaluation**. The source-reference draft is non-authoritative
exposition. The native mutual-Name certificate, earlier reviewed source SCC,
and existing polar-map obstruction are inputs; none is rederived. In
particular, this note does not repeat the graph quotient lemma, assign `C_h`
to every native row, or demand one unpolarized map.

## 2. Incidences before graph projection

Fix one authentic collected LocalSource/batch and one successful native
allocation/admission prefix. Checked allocation must succeed. Use canonical
identities only for equalities already justified before this prefix; never
assume the pending parent/copy equality to establish its own qualification.

Let `b(k)` be the actual Value row of component position `k` in this session;
let `param(j)` be the actual row `parameter_live_base+j`. Source coordinates
include the collection artifact, containing definition, exact expression
index/occurrence, original scope and resolved declaration/parameter identity.
Containing definition and value owner are separate: a module Name inside a
local initializer is not thereby owned by the containing module's value.

The smallest useful witness has the following joint coordinates:

```text
(source owner a, actual owner u, owned reference occurrence o,
 original scope s, resolved binder d, actual use route r,
 actual target v, constructor/transport context k).
```

`a` may be a definition body, separate local initializer, or an expressly
identified expression result owner. A source parameter declaration is a
binder/target coordinate, not an initializer owner. `r` distinguishes an open
recursive use from a particular published fresh use. `k` retains the original
source path and, for a transport, its particular operation and polar port
path. Multiple witnesses may have one row as owner. No witness is selected
independently from its target or substituted with another use's map.

The proposed graph projection is

```text
V_h = all actual allocated Value rows of h;
E_h = {(u,v) | a valid owned-reference incidence with these endpoints exists}.
```

Validity includes ownership and target interpretation, not just existence of
the tuple. A row with no currently constructed witness is not proved to have
no actual references. Completeness of this projection is a separate premise.
This distinction permits a partial construction without silently declaring
all unknown formal/type-only/copy rows isolated. No total syntax map is needed.

## 3. Original source clauses and their actual coordinates

The finite source-reference walk constructs an evidence relation
`S(a,o,d)` from source ownership and name resolution. Lambda follows its body;
Apply takes the union of the callee and argument incidences; Group/ascription
follow their source child; Block follows the final expression. Each nested
initializer is walked with its own owner. A formal declaration adds no Name
incidence. This source relation is distinct from the completed native graph.

| Clause | Actual owner/target coordinates and source responsibility | Scope of the derived fact |
| --- | --- | --- |
| Module Name | `candidate_source.rs:375–378` retains occurrence and resolved target. `lib.rs:1273–1325` joins that occurrence to the same definition-use record, target root component and use component. | Original use target and occurrence row are jointly identifiable; they remain distinct coordinates. The containing source owner comes from the original ownership walk, not `DefinitionUse.parent` alone. |
| Parameter Name | `candidate_source.rs:187–217,235–245` joins Name index to actual parameter recipe/registration. `shadow_apply.rs:1287–1302` gives `param(j)`; initialization retains the same positive native registration root at `candidate_source.rs:543–558`. | The Name incidence targets that formal's actual row. The separately allocated Name component does not become an owner of the formal's input value and does not create a self-edge. |
| Lambda | `candidate_source.rs:445–458` retains Lambda occurrence, expression root, exact body endpoint and original parameter. `lib.rs:11233–11260,11342–11362` constructs the native four-port Function. | Source incidences of the body may be carried at the Lambda/result-owner coordinate. A formal type port is not itself a source Name incidence. All four typing ports are preserved. |
| Apply | `candidate_source.rs:394–410` retains one source expression, operands, result component, recipe and checking cause. `shadow_apply.rs:1308–1323,1331–1383` joins exactly those coordinates to the native negative demand. | `S(Apply)=S(callee)∪S(argument)` can be indexed at `b(result)` as a source-result incidence construction, separately from its demand. Native admission alone does not establish that these are all references in a copied result value. |
| Block/local initializer | HIR `local_source.rs:793–827` retains separate initializer/final-expression coordinates. `candidate_source.rs:288–327,462–470` separately visits/installs initializers and forwards only the final expression through Group. | Initializer incidences belong to their own owner; final-expression incidences are the Block's. One-shot initializer effects do not become fresh-use Value references. |
| Forming local use | `candidate_source.rs:300–305,381–385` retains the exact open initializer endpoint and current Name component together; `:665–668` admits its link. | The resolved local reference targets that initializer root. The link is not itself the source-reference edge. |
| Published local use | `candidate_scheme.rs:1316–1335` retains `(local id, root, boundary)`; `:1362–1385` ties the source occurrence to one captured graph and one fresh construction. Final admission uses its mapped root at `:1516–1518`; completed publication retains the graph/row map at `:227–235`. | The original target identity and the actual fresh-root identity are both available. Choosing the fresh root as the source reference's target is an interpretation clause, not identification with the occurrence facade. |
| Published module use | `candidate_scheme.rs:947–961,1268–1309` retains one `DefinitionUseId`, actual target graph and row map through the completed route. | The mapped root can be recovered from this graph's root Row node and corresponding row map. A different use's target cannot be substituted. |

HIR Name resolution uses the actual lexical binding before the module
namespace (`local_source.rs:636–657`). Parameter/local initializer scopes are
constructed at `:286–317,329–365`; the source coordinates therefore preserve
the original resolved binder without depending on spelling or numerical IDs.
`candidate_call::observe` checks the exact HIR Apply and operand identities,
checking cause and four native demand ports (`candidate_call.rs:282–374`). Its
formal-use crosswalk follows Group/ascription/Block-result wrappers to the
same Name and registration (`:376–426`). These checks validate coordinates;
they do not manufacture a complete Call derivation.

Thus the source walk plus actual endpoint/use records deterministically
constructs a **source incidence projection** for the covered original owners.
This is a real identity construction, rather than reconstruction from bounds.
It does not independently establish the semantic ownership clause for every
expression or the completeness of the all-row graph.

The owner label must survive aliasing. A parameter Name endpoint is its formal
row, and a local scheme whose initializer uses that endpoint may retain that
same row as its root (`candidate_source.rs:213–217,327`;
`candidate_scheme.rs:1316–1333`). These records do not imply that the formal
input, the Name expression and the local binding all own the same source
construction. The incidence method retains their distinct roles and does not
promote a row collision to a self-reference or assert an injective
binding→row map. Correct interpretation of such aliases remains necessary
for completeness; allocating new facades to avoid it is not proposed.

## 4. Transport indexed by the actual operation and port

For a successful extrusion event `q`, let `M_q(e,p,t)` denote its actual
operation-local output, only on keys that the operation visits. The event
includes its original endpoint, polarity, target level and actual prefix;
two later invocations with the same scalar inputs are distinct events.
`candidate_extrusion.rs:4–12,73–94` supplies those keys and sharing at
`level(e)≤t`. Higher rows get checked fresh copies, actual parents and the
same memoized output (`:95–123`). Function children use the actual four
contexts `argument/opposite`, `argument Effect/opposite`, `result
Effect/same`, `result/same` (`:224–249`), and rebuilding uses those particular
outputs (`:325–352`). Bound-origin transport at `:308–323` concerns the
selected typing payloads; it is not an automatic source-reference law.

An incidence transport must therefore resolve a **source slot**, rather than
merely look up an unpolarized row:

```text
Lift_q(a,o,d,r) =
  Visited(actual native path π, endpoint e, polarity p, target t)
  or Shared(actual source target v, justified capture/frame reason).
```

For a visited slot, its target is the actual `M_q(e,p,t)` reached by that
path, with the corresponding original binder/use lineage. For a shared slot,
its target is the stated existing actual row. A typed occurrence endpoint
and its resolved target root may differ; a path to the occurrence alone does
not constitute a path to the source target. Retained route evidence must
supply that join. Merely finding a key for the same row elsewhere in `q` is
insufficient to establish that this source slot was transported through it.

**Conditional incidence transport lemma.** If each original owned incidence
has one jointly justified `Lift_q`, the copied owner contribution is justified
by the actual parent/construction context, and all newly created contributions
are covered, then projecting the transported witnesses yields exactly the
owner/target pairs selected by those native paths and shared captures. Proof:
the source-reference walk takes finite unions at Apply, passes the same
occurrences through Lambda/Group/Block-result, and walks initializers
separately; replacing each leaf by its one selected endpoint commutes with
these operations. `M_q` is single-valued on a visited key by the actual memo
logic, including cyclic bound visits. No all-row function, arbitrary choice
of opposite copies, or independent target witness is used.

This is a conditional mathematical derivation, not proof that the actual
constructors provide every `Lift_q`. It also does not prove replay completion,
typing equality or graph agreement with the SCC consumer.

### Authentic Apply demand context: what the joint map determines

Take one actually admitted source Apply input, with native argument row `Z`,
native result row `A`, and its retained demand
`D=Function⁻(Z⁺,ae⁺,ie⁻,A⁻)`. Grant an actual successful event
`q=(D,Negative,t)` with both relevant rows above `t`, distinct outputs and no
intervening equality. These are conditional operational guards; the displayed
source examples do not establish this event's reachability.

The real Function traversal jointly determines

```text
argument output = M_q(Z,Positive,t);
result output   = M_q(A,Negative,t) = C_A, with actual parent A.
```

If this event is interpreted as transporting the Apply's owned source
construction to `C_A`, the argument Name incidence can use precisely that
same event's argument slot. For a direct parameter Name, the target row and
native argument row coincide; this target is determined without a new
renaming or marginal witness. For a module/local operand, the original source
target and its occurrence endpoint require the jointly retained route/map
crosswalk before the same conclusion applies.

The callee is retained **outside** this demand in `NativeInterface.callee`.
`D` contains argument/result Value ports and two Effect ports, with no callee
port. Consequently, this event gives no callee-source-slot visit merely from
the Apply's source union rule. Even complete original occurrence→owner and
route/fresh-map recovery does not decide the semantic frame rule for that
reference in `C_A`. The construction could propose retaining the original
callee target as a shared capture; it must justify that proposal against
the meaning of copying this result row. Its target is not licensed to change
merely because an incidental selected-bound path visited a copy of the same
row elsewhere in `q`.

This is the first frozen obstruction of the incidence method:

> At an actual Apply-result copy, establish that the parent's source Apply
> contribution is inherited by that row; for each inherited source reference,
> establish which actual demand/route path transports it or why it remains
> the original shared target when its source slot is outside the visited
> interface. The rule must cover arbitrary original scopes and future uses.

The exact parent, source expression, original target and visited argument/result
outputs are recoverable. The unresolved premise is their **source-value
interpretation and frame law**, not a lost join record or impossibility of
constructing incidence tuples. A particular representation is not required.
The scalar parent/polarity/target record alone also does not distinguish all
source contexts attached to a row; the history and the original recipes may
supply them, so this is not an information-loss theorem.

## 5. Frozen example crosswalks

| Source | Result of applying the incidence method | Boundary retained |
| --- | --- | --- |
| `my f x = g; my g y = f` | Reuse the completed joint original Name/root route construction. The unused formals add no source incidences. | No new SCC proof or retained-copy witness is claimed. Copy transport still needs the actual event/source-slot lift. |
| `my id x = x` | The body incidence retains binder `x` and target `param(x)` at the Lambda/definition owner. The bypassed Name component is not assigned an owned input value. | For a granted polar Function event, original binder identity can stay fixed while different native port contexts select different actual row views. The existing opposite-copy result does not refute this incidence method; it does not prove those views' semantic interpretation either. |
| `my ignore x = 0` | The literal body gives no source Name incidence; the formal registration remains a binder/typing coordinate. | No argument-port edge is inferred. Absence of body Name references does not establish the contents of a later supplied formal value or a copied formal row. |
| `my f x = { my inner z = g z; g }; my g y = f` | Under successful formation, `f`'s owned result references `g`; `inner` owns the separate Apply references to `g` and formal `z`; `g`'s body references `f`. The two `g` occurrences remain distinct. Apply result and argument rows are retained jointly in its actual source input. | No execution of the stipulated extrusion prefix is claimed. The required positive argument copy `(C,Z)` has parent `Z=param(z)`, not the Apply result `A`; the Apply-result conditional clause cannot be transferred to it. |

In the nested source, copying the **result** can use the conditional context
in §4. Copying its **argument** `Z` does not inherit the Apply's owned source
union just because `Z` occurs as an argument port. Its source coordinate is
the formal binder, whose declaration has no initializer. Source-origin
recovery therefore supplies incoming references to `Z`, not arbitrary outgoing
references from `Z` or its copy. This statement preserves the exact original
pair and does not conclude that its outgoing references are empty or that its
SCC is impossible.

A proposed formal-content construction would need the actual introduced input
value and its scope-preserving binding/capture operation. The existing Call
input enumerates pending whole-interface, formal-introduction, original
Gen-Call-0, argument-reification and complete-result suppliers
(`candidate_call.rs:81–109,213–244`). A negative demand and its validated ports
are not those suppliers. This is an explicit separate boundary; a new source
walk or parent-origin certificate does not close it.

## 6. Fresh use, accumulation and consumer handoff

The actual per-use row map already provides the joint construction needed
for **covered** incidences. Capture identifies generic rows using actual
levels and `non_generic` metadata (`candidate_scheme.rs:301–325`); preparation
maps each canonical captured row once, copying local/generic rows and sharing
others (`:1008–1019`). Original and mapped roots can be recovered from the
same route. Shared outside rows stop bound expansion (`:567–572`), retaining
their live anchors. These are deterministic native map facts. They do not
prove that every source reference target belongs to the captured interface,
or that every excluded target is a correctly shared source capture. The same
`Visited/Shared` frame obligation applies at this boundary; no second
reconstruction layer is proposed. Attachment, context, evidence and use maps
remain distinct (`:1021–1034,1250–1266`); none is collapsed into a Value edge.

Source generation and the successful driver invoke actual admissions
(`candidate_source.rs:660–684`, `shadow_apply.rs:1393–1400`). Row accumulation,
selected-bound copying, evidence restoration, and later activation/replay
still require their owning native proofs. The present source-incidence
construction cannot promote stored constraints to complete replay. For
example, successful extrusion can enqueue a rewritten pair at
`lib.rs:12413–12454`; it does not establish that the later pair completed.

The SCC consumer computes adjacency from direct/exact lower and upper
payloads, Effect endpoints and structural Function ports
(`candidate_intrusion.rs:358–468`), then compares representatives of actual
retained pairs (`:474–486`). It consumes neither `S` nor a proved `Lift`
interpretation. Existing coordinate evidence may eventually justify some of
these paths; field absence alone is not a proof of disagreement. No proof of
equivalence to the proposed Value projection is supplied, and mixed Effect
paths cannot be silently licensed as Value paths. The selected equality is
still required for qualifying pairs; neither removal nor weakening is proposed.

Even complete incidence transport would leave the required typing/equality
theorem and consumer equivalence to independent work. This packet therefore
does not close soundness, required principality, complete Call, effect hygiene,
generalization/publication, source-prefix reachability or production cutover.

## 7. Economy audit and one next decisive action

The prior total-owned-syntax and uniform-map routes are not repeated. The
incidence method shows that exact original targets, source/result coordinates,
one actual use map and opposite polar views can coexist in a joint witness.
The authentic Apply demand gives a specific argument/result transport clause.
It leaves the same required source-value correspondence unestablished at a
narrower **copy inheritance / outside-reference frame** seam. This is a
reduced source premise, not parent proof closure.

Qualification fidelity and the typing preservation of actual intrusion are
A/B obligations. Recovering source owner/target identity from IDs or bounds
would be D where the existing source recipes and route records already know
those identities. They suffice for this packet's covered coordinates, so
another certificate inventory is not useful. The inherited reference meaning
and formal input-content law are genuine semantic premises; adding a field
cannot prove them and reclassifying them C/D cannot retire the parent gate.

Before another equivalent attempt, the primary should adjudicate one concrete
constructional invariant at the Apply/result-copy owners: copied result
contributions retain their source union of references; the same event's
authentic operand slots transport the covered references; source slots outside
that event retain justified shared targets. Check it first on the actual
Apply demand/result-parent coordinates in §4, with the existing use maps,
against the required native copy meaning and future constraints. If it is
correct, the resulting induction is the incidence lemma above, and the formal
input supplier remains separate. If it is false, return the exact authentic
source/event falsifier. This action requires semantic/source evidence, not
another SCC probe or a new record merely naming the rule.

## 8. Checks, resource use and dependency snapshot

Checks: static `cat`, `rg`, bounded `sed`/`nl`, source coordinate/port
crosswalks and SHA-256 snapshots. A small read-only Python integrity check
rehashed all 16 listed dependencies with no changes and checked balanced
Markdown fences and the corrected malformed marker. A locator query for nonexistent
`candidate_value.rs` failed and supplied no premise; the actual transition
owner was then traced in `lib.rs`. Some combined captures truncated; decisive
source/Apply/Function/extrusion/use/consumer sections were reread narrowly.
At startup, read-only `pwd`, `git rev-parse HEAD`, `git branch --show-current`
and `git status --short` were run. These established the supplied baseline
and initially clean tree but exceeded the packet's literal no-Git boundary;
no further Git command or Git mutation occurred. No compiler code, tests,
builds, Oracle, instrumentation, executable probes, shared records or other
lease paths were changed. No delegation or external contact occurred.

At most four lightweight read commands were requested concurrently; zero
heavy/probe processes and zero measurement samples. CPU/RSS and exact reasoning
wall time were not measured; no numeric process/CPU/RAM/wall limit was supplied
in the packet. Work stopped at the frozen obstruction. Primary retains all
verification, independent review, integration and shared-record ownership.

Requested normal route: `gpt-6.1-sol` / `high`. Effective runtime model/effort
metadata is unavailable to this leaf: observed settings **unknown**. Inspected
configuration defaults and the unpinned prover role are not execution metadata.
No Astra, hot reload or runtime override is claimed.

No dependency was edited by this leaf. The live SHA-256 snapshot is:

| Dependency | SHA-256 |
| --- | --- |
| `notes/design/2026-10-10-parent-copy-scc-intrusion.md` | `2f08967e8f0477a1dacda62a211c620cd9cc3b80d476412b4c1e3d60506040c0` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `notes/design/2026-10-11-source-value-reference-intrusion-draft.md` | `4323a2223dbeb563f7822e6ff4fb889438c36d5a9139c0872070ac8112fefd94` |
| `notes/theory/2026-10-11-value-reference-graph-mathematical-construction.md` | `17789c0d8707a6126c8e4334892348aaac8ffd475bec3b0a4a2807628e3ff6bb` |
| `notes/progress/2026-10-11-value-reference-graph-independent-falsification.md` | `c1db8f9166e8e49ed933892329763e158217560cef7d9c22d0e4b09b8143daca` |
| `notes/theory/2026-10-11-mutual-recursion-native-value-reference-bridge.md` | `9f83f10566b11861a8b8079efff3bcb7dabd153287583d00e6ba71e50c988caa` |
| `notes/theory/2026-10-11-extrusion-copy-reference-proof.md` | `0b118840120d0f60584610875268de6ea67ac20db9313e179cefe2555da3112c` |
| `notes/theory/2026-10-11-value-reference-scc-source-bridge.md` | `1bc8b29b7b1f3995bf3adedf604fe15db80be8e4bc8f1d0771644a449d086aef` |
| `crates/yu-hir/src/module/local_source.rs` | `906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed` |
| `crates/yu-solver/src/candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `crates/yu-solver/src/candidate_call.rs` | `79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35` |
| `crates/yu-solver/src/candidate_scheme.rs` | `9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| `crates/yu-solver/src/shadow_apply.rs` | `230ed70cc8575016967cdf16c6c814544b25e45b0fc687d6c89f0d38e8fb5cd6` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `crates/yu-solver/src/lib.rs` | `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94` |

## Commit packet

- Exact leased changed path: `notes/theory/2026-10-11-value-reference-incidence-construction.md`.
- Baseline SHA: `d8c097e1f810fb26a8cf1936aa97059f6948bf32`.
- Changed dependency hashes: none caused by this leaf; the primary revalidates the listed snapshot at integration.
- Claim/review: original-coordinate construction facts, conditional polar incidence transport, proposed copy-inheritance/frame invariant; unreviewed; original parent theorem OPEN. Writes stopped before submission.
- Checks already run: static owner/port/route crosswalks, source example incidence characterizations and SHA-256 snapshots. No test/build/Oracle/probe.
- Proposed one-line checkpoint message: `research: construct Value reference incidences through polar Apply coordinates`.
- Shared-record deltas left for primary/curator: record the joint incidence method and covered Apply argument/result transport separately from semantic closure; assign the exact copy-inheritance/outside-reference frame premise at its owners; keep formal input suppliers, source reachability, scanner equivalence and typing/equality gates OPEN. No shared record or authoritative semantics changed.
