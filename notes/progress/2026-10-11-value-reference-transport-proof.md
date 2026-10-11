# Value-content identity transport: source-qualified obstruction

Date: 2026-10-11
Status: frozen unreviewed research; bounded source derivations and semantic underdetermination, not intrusion theorem closure
Baseline: `3fa72e768c5a31e12ff44061d119102efca9aef3`, `research/simple-sub-intrusion`
Exclusive lease: this file; leaf, no further delegation

## 1. Frozen obligation and authority

For every supported source program, every lawful finite source-construction and
inference/use history at its **original** binder and event scopes, and every
actual retained Value extrusion pair `(c,p)`, establish the following candidate
law from its owning constructors:

1. Genuine Value-content reference incidences have joint coordinates
   `(owner row, source occurrence, resolved binder, scope/use, target row)`.
   These are separate from structural type positions, comparisons, bound
   storage and retained parents.
2. An extrusion event has its actual polar type map `M`. Its copied owned
   content has an independently grounded, construction/use-indexed identity
   map `N`; determine whether targets remain the original binding identities
   or become specific copied description identities. Account for references
   absent from `M`'s domain and for one binder appearing at opposite polarities.
3. A scheme use jointly maps every eligible generic owner/target in the same
   source-description frame, preserves nongeneric anchors and monomorphic
   aliases, and does not rerun an initializer or choose another runtime object.
4. The resulting graph is the actual-reference graph used by intrusion. When
   `(c,p)` lies in one SCC, equality must preserve one jointly shared source
   typing, complete Call and effect evidence, later constraints and the
   required principal scheme. SCC membership alone is not that preservation.

No source restrictions, eager per-constraint solving, provider substitutions,
independent marginal witnesses, new graph interpretation, or weakening of
ordinary Simple-sub is permitted. All original complete/pending Call arms,
effect hygiene, attachment and residual lineage remain in scope for the parent
obligation. The bounded derivations below do not establish their general laws.

Exact governing sources are the parent-copy decision's **Selected operation
and compiler responsibility**, **Value-reference SCC clarification**, and
**Retained boundary**; top-level inference principles §§1–5 and **Evaluation**;
contextual Function membership §§2–3; complete Call contributions §§2–4;
source Generalize §§2–4. The original reference is commit
`9bae772624c23b52a93c1b226157e16898b4d9db`, `Typer.scala:48–224`; paper
§§3.2.1–3.2.2, §3.5, Figures 6–9 (PDF pages 9–11 and 17–21).

The primary additionally supplied direct user clarification: `host→outer`
comes from a Name of the local `outer` in `host`'s body; `g→g` comes from
self-reference; containment does not create `outer→g`. This is accepted
lexical-reference evidence, supplied through the primary, with no independent
timestamp or transcript verification by this leaf. It rules out interpreting
those closure edges as only currently allocated runtime capture objects.
It does not specify the content of every native Apply result row.

The primary-owned interpretation draft is a hypothesis, not authority. Its
route-only transport is a previously refuted route, not a premise used here.

## 2. What original Simple-sub actually constructs

`typeTerm` gives Name the instantiated context **type**; Lambda constructs
`Function(param,body_ty)`; Apply allocates result type variable `r` and
constrains `f_ty <: Function(a_ty,r)`; selection constrains the receiver
against only the requested field (`Typer.scala:59–84`). Recursive let uses
one monomorphic variable during its initializer, then a level-based scheme
(`:48–55`). None of these records defines a Value-content graph.

Ordinary constraint propagation installs the new bound before activating
opposite bounds (`:115–126`; paper §3.2.2). A level violation calls extrusion;
the memo is indexed by `(variable,polarity)`. Function arguments reverse
polarity and results preserve it. Copies carry one selected bound side and
the directed approximation link (`:131–158`; paper Figure 7). This operation
copies a type and its selected reachable bound subgraph. It does not copy a
source lexical environment or rebind a source Name.

`freshenAbove` uses one nonpolar memo for the reachable generic type/bound
graph, keeps older identities unchanged, and visits both bound sides of a
fresh variable (`:166–188`). The scheme invocation is at `:201–202`.
Thus ordinary within-use sharing and cross-use type independence are real
construction facts. Extending this memo to all source-content targets is an
additional domain/interpretation rule, not a consequence of these loops.

These facts establish a type transport `M` and a reachable type freshening
map. They establish neither `Own(row,content)` nor `N` for genuine content
references. Retaining `N` is feasible as a proposed representation once its
meaning is fixed; merely naming an explicit map does not determine it.

## 3. Two source-qualified discriminators

### 3.1 Projection loses a lexical reference from the exported type

Consider `λx. ({keep=0,drop=g}).keep`, with the resolved external binder `g`
assigned a monomorphic variable `gamma` with empty bounds. The original
source constructors, at one chosen level, generate:

```text
param(x) = alpha
record type = {keep:Int, drop:gamma}
selection result = beta
{keep:Int, drop:gamma} <: {keep:beta}
therefore Int <: beta
Lambda type = Function(alpha,beta)
```

Record comparison checks the demanded `keep` field only. `gamma` is absent
from this Lambda type and the bound graph reachable from `alpha,beta`.
The original Lambda fragment still contains the resolved Name of `g`.
This derivation uses width subtyping, not dead-code removal or a change to
evaluation. The closed nesting `λg. λx. ({keep=0,drop=g}).keep` supplies that
same binder as an enclosing formal; `g` is still absent from the inner
Lambda's type, although present in the enclosing Function's domain.

Consequently, a law assigning every such lexical reference a visited route
in the **particular extruded type** is false. Looking elsewhere in the
source/typing context can retain `g`, but that is exactly the separate
content-constructor law sought here. If `g` is already nongeneric, fixing its
target is a possible frame law; its correctness is not supplied by finding
an absent route. With a polymorphic `g`, the type instance created for the
discarded field can likewise be absent from the exported type graph: whether
the content target is the binding identity or that use's description instance
must be specified before deciding its freshening eligibility.

This is a source-qualified refutation of route totality. It is not a
source-qualified refutation of the approved SCC equality.

### 3.2 One source Name produces two genuine polar type copies

Use the original grammar term, inferred from level zero:

```text
let outer = λh. let y = h (λx.x) in y in outer
```

Freeze the prefix inside `y`'s initializer, before `outer`'s publication.
`h` has monomorphic type variable `eta` at level 1. `y`'s initializer and
the inner formal `alpha=param(x)` are at level 2. The one body Name `x`
returns precisely `alpha`. Apply allocates `rho` at level 2 and generates

```text
eta <: Function(Function(alpha,alpha),rho).
```

The right type exceeds `eta`'s level. The actual negative extrusion flips
once for the outer argument and once for the inner argument, producing

```text
Function(Function(c_minus,c_plus),r_minus) at level 1
M(alpha,negative)=c_minus
M(alpha,positive)=c_plus
M(rho,negative)=r_minus
```

`c_minus` and `c_plus` are distinct fresh variables: their memo keys differ.
In the actual reference traversal order, negative `alpha` first places
`c_minus` in `alpha.lowerBounds`; positive `alpha` then places `c_plus` in
`alpha.upperBounds` and copies the existing lower to `c_plus.lowerBounds`.
Thus the recorded type approximation includes `c_minus <: alpha <: c_plus`
and `c_minus <: c_plus`. Those judgments are not Value-reference edges.

This is a real source-generated extrusion in original Simple-sub, obtained
directly from its let levels and constructors. No arbitrary initial store
or manually injected constraint is used. It is not an executed Yulang trace.
The subsequent body Name `y` and final Name `outer` use the ordinary scheme
constructors; they do not retroactively make the two polar keys identical.

There is only one resolved Name occurrence `x` and one original formal
binder. A polarity-free function agreeing with **both** visited type images
would require `N(alpha)=c_minus=c_plus`, which is false. Separate content
identity transport avoids that demand, but at least these different choices
remain unselected by the type algorithm: retain the original lexical formal
identity; or open a copied formal-description frame, target its parameter
identity and check the body against the result approximation. The latter
uses the one joint frame and the recorded subtype approximation; it cannot
choose a fresh target independently at each polar occurrence. These are
candidate description interpretations, not proved all-source laws.

## 4. Native construction/consumer bridge

The current Yulang candidate retains enough coordinates to locate the seam:

| Owner | Actual inspected construction | Evidence limit |
| --- | --- | --- |
| Name/formal | `candidate_source.rs:187–217,375–389`; `shadow_apply.rs:1287–1302` retain resolved formals, module/local use and actual native endpoints. | A parameter Name aliases its formal type row. This does not make the formal input Value own the Name expression or a self-reference. |
| Lambda | `candidate_source.rs:445–459`; `lib.rs:11233–11260,11342–11362` join root, actual formal and body endpoints, construct all four Function ports, and admit the positive Function at the Lambda root. | This is generated type payload and provenance. A complete owned-content interpretation through root/Name aliases is additional. Domain overrides follow their actual endpoint. |
| Apply | `candidate_source.rs:394–411`; `candidate_call.rs:29–58`; `shadow_apply.rs:1331–1383` join source operands, result row and four-port demand. | `result` is the native result port, not an equation with callee code, argument code or returned-provider content. |
| Apply validation/propagation | `candidate_call::observe` at `:282–374` checks source/port identity; `lib.rs:12493–12536` emits argument/result and both Effect comparisons. | These are real active constructors/consumers. Port covariance does not create content edges. |
| Extrusion | `candidate_extrusion.rs:77–160,224–249,325–352`; `lib.rs:12412–12454` visits polar keys, retains real parents, rebuilds ports and enqueues rewritten comparison. | The map covers selected typing payloads. No Name/content constructor is invoked by these inspected extrusion branches. |
| Fresh use | `candidate_scheme.rs:310–325,458–513,567–595,981–1019` captures the reachable typed graph, stops at nongeneric anchors and maps each canonical generic row once. | This establishes the actual typed map and sharing, not its completeness for off-type content targets. |
| Intrusion | `candidate_intrusion.rs:358–488,513–604` scans bounds and structural ports, checks retained parent/copy component equality, merges canonical rows, transfers bounds/origins and replays. | Its present dependency adjacency includes both bound sides, Function ports and Effect dependencies. No proved equivalence with the selected Value-reference graph is supplied by the scan. |

The needed bridge is therefore a constructor-owned interpretation of each
native Value row's **content**, plus the exact resolved target identities
through aliasing, use and extrusion. It must reach the actual SCC consumer.
Copying type slots, keeping a parent or validating result ports cannot supply
this premise by themselves. No claim is made that current implementation
fields make a history-based construction impossible.

## 5. Genuine remaining semantic choice

Accept the direct lexical closure-body examples, including `host→outer` and
`g→g`, with separate ownership for nested initializers. They exclude a
capture-object-only graph. They still leave this smallest native case open:

```text
konst x = 0
out = konst g
```

Fix one admitted Value-entry Call whose argument Force completes. The adopted
Call/Return laws give the literal output `(0,p_0)` while retaining callee,
argument entry, effects and the entire Call witness. Consider these two
**possible completions of the missing native row-content definition**:

| Completion | Content assigned to Apply's result row `R` | References in this example |
| --- | --- | --- |
| Source fragment | `R` owns the static `konst g` fragment, with the actual resolved operand Names; computed output stays in complete Call. | `R→K` and `R→G`, at the particular construction/use targets. |
| Returned Value image | `R` owns the actual output Value's symbolic content; the operand code and ordered execution evidence stay in complete Call and enclosing closure code. | `R` owns literal `0`, so neither edge above exists. |

Both keep the Lambda's lexical body references, self-reference and the supplied
`host` example unchanged; neither obtains containment edges. Both keep the
same complete Call, actual provider, Force effects and result tuple. No
inspected original type rule or adopted source rule equates `R`'s content
with either proposed object. Hence the **native result-content meaning is
semantically underdetermined relative to the supplied clauses**, not uniquely
recoverable by proving a transport lemma. This is a concrete definition choice,
not just missing storage evidence for an already identified object.

These are not two certified implementations or globally proved models of
the intrusion/soundness/principality contract. Their local agreement with all
supplied reference observations and source/type clauses establishes the
unselected constructor case. It does not prove that both can meet the final
all-source equality theorem. No differing intrusion decision or accepted
program is invented from this local graph divergence.

The remaining requested cases separate accordingly:

| Source case | Established source fact / discriminator |
| --- | --- |
| `id x=x` | Its body Name refers to the original formal. A completed Value-entry Call returns the same argument/provider. Source-fragment result content would retain operand Names; returned-image content would retain the argument Value's own content. These identities must not be substituted for one another. |
| `konst x=0` | Its body has no formal Name; the formal type port remains present. Argument entry still executes. Literal output does not erase complete Call evidence, but neither that evidence nor the output determines the missing native content convention. |
| `f x=g; g y=f` | The supplied lexical closure interpretation gives the cross references, and the adopted positive immutable pair/Generalize keeps a simultaneous relation. It does not by itself produce an extrusion pair or determine copied reference targets. Original Simple-sub's single recursive let is not evidence for an unprovided simultaneous-let constructor. |
| `invoke f=f 1`, pending | The enclosing Lambda code has its Name of `f`. Apply has a native result endpoint and delayed type constraints before a concrete provider is known. Source-fragment content has a reference to `f`; returned-image content is a correlated pending output, with no fabricated Return. |
| Same-typed providers with different refs | Let `a,b` be distinct immutable Int bindings and `makeA z=λx.a`, `makeB z=λx.b`. Their ordinary types agree up to fresh variable names. `invoke makeA` and `invoke makeB` return distinct closure providers with lexical targets `a` and `b`. Source-fragment Apply content instead retains its own operands. The type cannot determine the returned closure's lexical target. Each completed Call uses its actual provider; no same-type provider substitution is allowed. |
| Opposite routes / projection | §3 supplies actual original source derivations. Typed routes either split one binder or omit a lexical target. A separate map is needed if source content is selected, but these derivations do not select that map. |

For returned-image content, arbitrary providers and pending arms require a
joint symbolic output description; a union of possible provider edges is not
an actual-reference graph. For source-fragment content, reference lookup must
say whether `G` is a fixed binding row or the particular opened description
row. Source Generalize §2 preserves actual binding objects while allowing
fresh descriptions; it does not identify these two kinds of identity.

## 6. Audit, status and next minimal obligation

Two distinct routes have now left the native content premise untouched:
extracting content transport from typed routes fails §3; retaining a separate
identity map removes that extraction demand but still does not define its
domain, targets or owned result object. A third equivalent graph-copy lemma
would assume the same missing premise.

Under the proof-obligation-economy audit, correct SCC qualification and
equality preservation are A/B obligations. Reconstructing resolved occurrences
and use maps later is D: Name/Apply/Lambda constructors already know those
coordinates. Retaining them can remove that reconstruction debt. However,
choosing what Apply's result row owns is a semantic constructor premise,
not recoverable evidence, and retention cannot settle it. General graph
copy/isomorphism facts would be C/conditional mathematics here; they do not
close the A/B gate. No parent gate is reclassified or weakened.

**Result:** the proposed separation of `M` and `N` is not intrinsically
contradictory, but neither its full law nor SCC equality preservation follows
from the inspected sources. The route-only law is source-refuted. The exact
result-content definition and binder-versus-description target transport remain
unselected. No source-qualified counterexample to the approved intrusion
operation, soundness proof or principality proof has been constructed.

**One next action:** the primary resolves the native Apply-result content
constructor (source fragment versus returned Value image, with explicit
Name/formal target identity through extrusion and use) under the existing
design-authority process. Supply that exact law before another equality proof
or dependent implementation. Preserve complete Call/effect witnesses and all
ordinary source behavior. Then the source/consumer bridge and the qualifying
equality theorem remain separate obligations.

## 7. Checks, resources and frozen dependencies

Only bounded reads (`cat`, `rg`, `nl`/`sed`, `pdftotext` to stdout), read-only
baseline/status queries, SHA-256 capture, and this leased note write were used.
Original source and paper derivations are hand-derived, not executed tests.
No compiler/test/expectation/shared-record edit, Git mutation, Scala execution,
build, Oracle, executable probe, benchmark, delegation or external contact.
Some initial combined captures truncated; the decisive rule and constructor
windows were reread narrowly. No whole-repository negative-existence theorem
is claimed. The primary remains the single verification/integration owner.

The packet permits 90 minutes; this leaf stops at the exact obstruction.
At most four lightweight read commands were requested in a batch; zero heavy
processes, test processes, probes, samples or random/enumerated ranges. CPU/RSS
and exact reasoning wall time are unmeasured. Requested normal policy route:
`gpt-6.1-sol` / `high`; native launch arguments and effective runtime metadata
are unavailable to this leaf, so observed model/effort are **unknown**. The
configured defaults and unpinned prover role were inspected; neither proves
runtime routing. No Astra override or hot reload is claimed.

Final read-only integrity check found 331 lines before this check-result
addition, zero trailing-whitespace lines and ten balanced fence markers.
All 15 direct dependency hashes below were unchanged at freeze. The external
reference's read-only HEAD query matched the supplied commit. These are
artifact/dependency checks, not implementation tests or independent review.

SHA-256 direct dependency snapshot:

| Dependency | Hash |
| --- | --- |
| parent-copy decision | `2f08967e8f0477a1dacda62a211c620cd9cc3b80d476412b4c1e3d60506040c0` |
| inference principles | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| contextual membership definition | `0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0` |
| complete Call contribution definition | `4c83a095dce3636ada842bfc32c18cf0ef598db0e361861fb8e659745b74411e` |
| source Generalize definition | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| Call semantic input realization | `fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a` |
| candidate_source.rs | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| candidate_extrusion.rs | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| candidate_scheme.rs | `9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1` |
| candidate_intrusion.rs | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| candidate_call.rs | `79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35` |
| shadow_apply.rs | `230ed70cc8575016967cdf16c6c814544b25e45b0fc687d6c89f0d38e8fb5cd6` |
| solver lib.rs | `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94` |
| original Typer.scala | `f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9` |
| original paper PDF | `5ab2bd4122caee17c20134e4cbe8dc8a4848c142de1e576b5fd178aed8787698` |

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-11-value-reference-transport-proof.md`.
- Baseline SHA: `3fa72e768c5a31e12ff44061d119102efca9aef3`; external reference commit: `9bae772624c23b52a93c1b226157e16898b4d9db`, primary supplied.
- Changed dependency hashes: none caused by this leaf; listed inputs are rechecked at freeze. Direct `host` clarification is primary-supplied conversation evidence, with no file hash.
- Claim/review status: bounded original source derivations and native-content underdetermination; unreviewed research, no theorem/implementation/cutover closure. Writes stop before review.
- Checks already run: exact original paper/reference and native owner/consumer reads, baseline/status queries and dependency hashes; no tests/builds/probes.
- Proposed checkpoint message: `research: isolate Value-content transport and Apply ownership decision`.
- Shared-record deltas left to primary/curator: record the route-totality source refutation and genuine polar extrusion witness; preserve accepted lexical closure refs; distinguish unselected Apply content/target definition from missing retention; keep source/consumer correspondence, SCC equality, complete Call, hygiene and principality OPEN. No shared record was edited.
