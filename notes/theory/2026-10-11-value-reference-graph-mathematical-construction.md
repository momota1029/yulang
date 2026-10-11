# Value-reference graph: contraction and the shared-Function transport obstruction

Status: frozen research construction and conditional derivation; unreviewed
Parent all-source/all-history/retained-parent-copy theorem: OPEN
Baseline: `0af7aa73f17841d01df0cff0b13e42b2eef6a114`
Branch: `research/simple-sub-intrusion`
Exclusive output lease: this file; leaf, no delegation

## 1. Frozen objective, quantifiers and exclusions

For every supported source program `P`, every actual native inference history
`h` for `P`, and every actual retained distinct Value extrusion pair `(c,p)`,
construct the owned-value reference graph on the actual allocated Value
variables of that history. An edge `u -> v` exists exactly when the value
owned by `u` references `v`. Immediately before an intrusion equality, `(c,p)`
qualifies exactly when both directed reachabilities hold in this graph.
The selected equality must preserve the owned-reference interpretation,
typing safety and required natural inference/principality, including subsequent
constraints and generalization. This is the original parent claim, not the
claim established by the local graph lemma below.

Scopes, resolved binders, distinct polarity copies, shared references,
non-generic captures and independence between generic uses are retained.
Cross-level and uncle/nephew references are allowed. Parent metadata,
comparisons, bound sides, physical storage direction and lexical containment
are not reference edges. A singleton self-loop is cyclic but is not a
nontrivial SCC. Effects remain a separate relation; they are not intermediate
vertices of the Value graph. Complete four-port Call, effect hygiene,
soundness, principality and production/cutover remain required and OPEN.

Authority is the user-selected **Selected operation and compiler
responsibility**, **Value-reference SCC clarification**, and **Retained
boundary** in `notes/design/2026-10-10-parent-copy-scc-intrusion.md`, together
with §§1–5 and **Evaluation** of
`notes/design/2026-10-11-yulang-inference-top-level-principles.md`.
`rules/compiler-engineering.md`, **Natural compiler behavior and
proof-obligation economy** and **Deterministic Simple-sub inference**, govern
the method. No new meaning of “owned value” is adopted here.

Frozen dependencies are
`2026-10-11-value-owner-introduction-proof.md` and
`2026-10-11-mutual-recursion-native-value-reference-bridge.md` under
`notes/theory/`. Reuse their established joint original-root/occurrence
certificate and native route retention. Their missing semantic Name/Lambda
owner law is not silently assumed. The present contribution is a direct
mathematical contraction argument, an actual native obstruction to one
transport method, and the minimum remaining construction/typing laws.
There are no implementation changes, executable probes, tests or builds.

## 2. Mathematical relation before any scanner

Let `V_h` be the actual allocated Value identities, before the equality under
consideration. Distinguish a raw allocated identity from its current canonical
representative. Let an *owned reference witness* name all of:

```text
(owner u, owned construction a, reference occurrence o,
 original scope s, resolved binder/definition b, actual target v,
 construction/transport event k).
```

This tuple is proof notation for evidence from the owning phase, not a request
for a new runtime record. A witness must establish that `a` belongs to `u`,
that `o` is a reference in `a`, and that its resolved actual target in this
history is `v`. Source and transport components are chosen jointly. A marginal
owner witness and an independently selected target witness do not suffice.

Define `W_h(u,v)` to be the set of such valid witnesses. Then define directly

```text
E_h = { (u,v) in V_h x V_h | W_h(u,v) is nonempty }.
G_h = (V_h,E_h).
u ~_h v  iff  u ->*_h v and v ->*_h u.
eligible_h(c,p) iff (c,p) is an actual retained Value pair,
                       c != p, and c ~_h p.
```

`->*` includes the length-zero path. Distinct-pair eligibility therefore
requires paths in both directions. No tree/level ordering enters the
definition. Unreferenced allocated rows can be isolated vertices; no invented
reference is needed merely because a row exists.

On original source constructions, the reference walk follows the actual
expression constructors: a resolved Name contributes its actual target;
a Lambda follows its owned body with the original binder; an Apply follows
its callee and argument constructions; a grouping follows its child.
Separately installed local initializers have their own owners, rather than
automatically becoming part of the enclosing block's value. This is the
source walk already delimited by the frozen owner-introduction note.
Formal declarations alone are not references. This source walk does not
assert that an Apply result's native row owns its source syntax, that a
Function domain is a reference, or that a propagated bound is an owned value.
Those are precisely owner-introduction questions.

For source roots of `my f x = g; my g y = f`, the frozen joint certificate
already supplies `Rf -> Rg` and `Rg -> Rf`; it supplies a genuine nontrivial
SCC, with no extrusion pair. We do not derive that result again or insert
the occurrence rows as artificial intermediary vertices.

### Graph contraction lemma

For any finite directed graph `G=(V,E)`, let `c != p` lie in the same SCC.
Let `q:V -> V'` identify only `c` and `p`. Define the quotient edges by

```text
E' = { (q(u),q(v)) | (u,v) in E }.
```

Then, for every `x,y in V`,

```text
x ->*_G y  iff  q(x) ->*_(G/q) q(y).
```

Proof. Mapping each edge gives the forward implication. For a quotient path,
choose the original edge witnessing each quotient edge. Consecutive chosen
edges either meet at the same original vertex or meet at the identified
class `{c,p}`. In the second case insert the existing directed path from the
first endpoint to the second, since `c` and `p` are mutually reachable.
Do the same at the starting and ending class if necessary. This produces an
original path from `x` to `y`. For a zero-length quotient path with distinct
original endpoints, those endpoints are `c,p` and the required path already
exists. This proves the reverse implication.

Consequences: SCCs after contraction are exactly the images of the original
SCCs; no distinct original SCCs become connected by new mutual reachability.
Eligibility of other retained distinct pairs is preserved, except that a
previously distinct pair may already be equal after contraction. Multiple
qualified contractions from one frozen graph can be applied in any order
for this graph property, because every contracted class stays inside its
original SCC. This statement concerns a fixed graph; inference events that
introduce new owned references require a fresh graph/state argument.

The quotient preserves edges *as images* and preserves reachability. It
does not preserve the raw number or identity of vertices. Even contraction
of a two-cycle yields a singleton self-loop. Claiming literal graph identity
or preserving “nontrivial SCC” cardinality would be false.

### Ownership transport required by the quotient

The quotient edge definition follows from actual ownership only if every
old witness remains valid after joint substitution of owner and target:

```text
(u,a,o,s,b,v,k)  becomes
(q(u),q(a),o,s,b,q(v), quotient-of-k).
```

Original occurrence, scope, binder and provenance remain identifiable. If
several distinct construction witnesses acquire one canonical owner, keep
all witnesses; do not choose one arbitrarily. This is a semantic preservation
condition, not a proved native behavior. It need not require literal tuples
in the implementation.

If the required owned-value interpretation permits only one construction
per canonical row, the owner must additionally show that the constructions
being merged are compatible in that interpretation. Mere SCC membership
does not show compatibility. If ownership naturally permits several
contributing constructions, union of their witnesses yields the displayed
quotient graph, but that interpretation must itself follow from the owning
inference semantics. We do not adopt either interpretation to close the gate.

## 3. Graph preservation does not imply typing equality

The graph lemma uses only reference witnesses. It uses no typing hypotheses
and consequently supplies no theorem about equating the represented types.
For illustration, in an ordinary structural recursive Function type algebra,
mutually referring closures can have the equations

```text
Tp = Int -> Tc
Tc = Unit -> Tp.
```

These are finite rational type trees with different domain constructors;
their owned references form a two-cycle, but `Tp = Tc` does not follow.
This is a counterexample to a general implication from reference SCC to
type equality. It is not a source-qualified retained-extrusion-pair
counterexample and does not refute the selected parent/copy operation.
The actual parent/copy origin could provide an additional theorem unavailable
for arbitrary mutually referring values. That theorem remains necessary.

For a retained pair the minimum typing claim is therefore specific:

> The actual extrusion construction and subsequent source-native history,
> together with mutual reachability in the actual owned-reference graph,
> justify the selected equality of that parent and copy, preserving accepted
> typings and the required principal/natural result under future constraints
> and generalization.

Soundness alone would not discharge required principality: a new equality
can preserve some acceptable typings while losing ordinary inferred freedom.
The direct operation is selected by the user; this note neither removes it
nor substitutes a per-constraint satisfiability check.

## 4. Actual native Function transport: one renaming fails

There is a bounded, concrete obstruction to the following proposed route:

> Extrusion transports the owned-value graph and its typing interpretation by
> one unpolarized renaming `rho` of actual Value vertices, and the native
> Function ports commute with that same `rho`.

This is a counterexample to that transport lemma only. It is not proof that
no owned-value graph can coexist with inference variables.

### Original constructor with one shared variable

For an identity Lambda, the actual parameter registration retains its
`HirParameterId` (`candidate_source.rs:189–203`). Parameter Name resolution
selects `CandidateEndpoint::Parameter` (`:209–217`), so the body endpoint and
formal endpoint have the same actual Value row `alpha`. The actual Lambda
admission reads the formal negatively and the body positively
(`lib.rs:11233–11260`) and constructs the complete positive Function
(`:11342`):

```text
F+ = Function+(alpha-, entry-, return+, alpha+).
```

Here `alpha-` and `alpha+` denote the two polarized terms of the *same original
row*, not distinct rows. The entry and return terms are Effect ports, not
Value references. The source binder and its body Name have one original
resolved identity. The Parameter Name's allocated occurrence component need
not be its computation endpoint; assigning every Name syntax to its endpoint would
already require the unproved owner law identified in the frozen inputs.

### Exact extrusion that creates both copies

Consider a successful native extrusion of this structural Function to a
target level `ell < level(alpha)`, with initially empty operation-local
copy memo and without an intervening equality. This is an operational guard,
not a claim that every identity Lambda executes that extrusion. The actual
structural-to-row Value transition invokes `candidate_extrude` at the
receiving row's level (`lib.rs:12414–12442`).

`candidate_extrusion.rs:5` defines the memo key
`Key(ExtrusionEndpoint, Polarity, u32)`. Its Function visit constructs the
following four child keys (`:214–249`):

```text
argument Value:     (alpha, opposite(p), ell)
argument Effect:    (entry, opposite(p), ell)
result Effect:      (return, p, ell)
result Value:       (alpha, p, ell).
```

At either wrong-level Value-row visit, `:84–125` allocates a fresh Value
row at `ell`, calls `retain_extrusion_parent`, memoizes the row, adds the
one-sided type link and schedules the selected bounds. Since the two Value
keys differ in polarity, their fresh allocation outputs are distinct:

```text
alpha_neg != alpha_pos
parent(alpha_neg) = alpha, polarity Negative, target ell
parent(alpha_pos) = alpha, polarity Positive, target ell.
```

The retained parents are creation provenance, not reference edges
(`candidate_intrusion.rs:191–218`). Function reconstruction uses those exact
child results and all four ports (`candidate_extrusion.rs:325–353`):

```text
extrude+(F+) = Function+(alpha_neg-, entry_copy-,
                        return_copy+, alpha_pos+).
```

Thus portwise commutation with one unpolarized `rho` would require both
`rho(alpha)=alpha_neg` and `rho(alpha)=alpha_pos`, contradicting their distinct
fresh identities. Function is the first failing structural constructor of
this route: one row visit at one polarity admits a renaming; a Function that
uses the row in argument and result exposes both polarities. No bound-edge
orientation is used to derive this obstruction.

The actual Function comparison also confirms the variance independently:
`lib.rs:12491–12522` compares the upper domain against the lower domain,
and the lower result against the upper result; the argument Effect reverses
and the result Effect preserves direction. These are four typing obligations,
not four reference edges. Their activation is through the typed-drain
Function dispatch or ordinary enqueue paths (`:12541–12568`), not inferred
merely from the fact that a Function payload is stored.

The independently inspected native Simple-sub reference makes precisely
the same split: `Typer.scala:135–158` keys extrusion by `(Variable,Boolean)`,
flips polarity for the Function domain, and allocates each wrong-level copy
before transporting its selected bounds. Its comment explains that copies
are conservative approximations that admit independent later constraints.
This supports the native mechanism's meaning; it supplies no Yulang
owned-reference theorem and contains no proof of the selected intrusion.

This result does not force the two copies to be equal. It does not create
edges between them or their parent, or establish that either pair is eligible.
One may choose a single target for the source body reference while using
distinct native type projections, but then the single commuting-renaming
premise has been abandoned and the precise relation between that target,
the binder and both native ports must be proved. Treating the choice as
obvious would hide the central bridge.

## 5. Minimum construction/transport law still needed

The native copy map is already a function of `(row,polarity,target level)`;
it need not be redesigned. The missing owned-value law must connect its
incidences to original source identities without converting type positions
into references. At minimum, a valid transport certificate must jointly fix:

```text
original owner and owned construction;
original resolved binder and reference occurrence, with scope;
actual copy event, polarity, target level and retained parent;
native type-port path and its resulting actual row;
post-operation owner, construction and actual reference target;
typing interpretation relating each native port to that owned construction.
```

An incidence-indexed relation can express these facts; it is not yet a
proved invariant or a proposed new compiler representation. For the shared
Function, the known portion is

```text
(alpha, argument path, Negative) -> alpha_neg
(alpha, result path, Positive)   -> alpha_pos.
```

The unknown portion is which actual Value variable owns the copied source
binder's value, which actual target its original body Name references, and
why the two conservative type projections correctly describe that same
construction. A shared source binder cannot be replaced by two independent
binder witnesses. If one source owner has several native views, the law must
retain that correlation while leaving their actual row identities distinct.
It must also show how these owned references supply the SCC consumer.

This is more specific than assuming an arbitrary `C_h` with the desired
properties. It asks for an introduction/transport theorem at the actual
construction events, with the polar shared-row case as a falsifier. It does
not establish that such a theorem exists, or permit extra restrictions on
ordinary source programs.

### Constructor and consumer responsibilities

| Owner/event | Established operational fact | Exact remaining owned-value duty |
| --- | --- | --- |
| HIR Name resolution | Latest lexical binding, then unique module lookup retains resolved identity (`local_source.rs:636–656`) | Connect the resolved occurrence to the actual owned value/target, including local and instantiated uses |
| Module recursive Name route | Frozen inputs establish joint original owner/target/occurrence and completed internal typing admission/provenance | Semantic Name introduction and Lambda/root preservation, already OPEN in those inputs |
| Parameter Name | Actual endpoint aliases the formal row (`candidate_source.rs:209–217`) | Distinguish the Name's construction owner from its computation/type endpoint; preserve the one resolved binder |
| Lambda | Complete four-port positive Function, shared parameter/body row possible (`lib.rs:11233–11370`) | Owned-body reference preservation; type domain is not itself a reference; account for both polar projections |
| Apply | Source callee/argument/result/effects retained jointly (`candidate_source.rs:391–410`); negative Function demand and authentic native Call interface retained (`shadow_apply.rs:1304–1399`) | Prove ownership and forwarding of the result, rather than asserting it owns the demand's argument/result ports; retain all Call/effect duties |
| Level/extrusion | Wrong-level rows copied by polarity/target, parent retained at allocation; selected bounds transported (`candidate_extrusion.rs:77–169,214–249,309–353`) | Actual copied owner/reference construction and shared-binder correlation; no claim that source references follow levels or selected bound sides |
| Local generalization | Install retains actual root and boundary (`candidate_scheme.rs:1316–1333`) | Source-owned references/scopes retained at the boundary; completeness of the owner graph exposed to later uses |
| Fresh use | One canonical-row map per use; fresh only local, above-boundary, generic rows; shared anchors retained (`candidate_scheme.rs:981–1021`); four-port nodes reconstructed (`:1109–1165`) | Reference closure of captured owned constructions, joint target transport, old/shared anchors and independence between uses |
| Bound accumulation/replay | Native admissions store and replay typing evidence; extrusion copies selected sides | Prove how a newly available value construction creates an owned-reference witness, if it does; a stored or replayed comparison alone creates none |
| Canonical equality | Both bound sides transferred, min level/OR non-generic metadata retained, origins transported, lowers replayed (`candidate_intrusion.rs:525–625`) | Justify equality of this actual eligible pair and the quotient ownership law for every retained reference witness; preserve future typing/principality |

Freshening differs from extrusion. In `prepare_candidate_fresh_use`, the key
is the canonical row, so every occurrence of one generic row in that use
gets the same fresh row, independent of its Function port polarity. The
known type map therefore does preserve native shared-row identity within
that use. Rows not freshened remain actual shared anchors. This is source
code evidence for the type map, not an owned-reference transport theorem:
the captured graph contains row/leaf/Effect/Function typing nodes
(`candidate_scheme.rs:36–79`) and captures bounds (`:566–615`). It has not
been proved closed under the selected owned-reference relation. A source
reference may reach a cross-level or uncle/nephew target outside that typed
capture; excluding such targets is forbidden.

The reference implementation's `freshenAbove` also uses one variable map,
preserving shared occurrences and stopping at the boundary
(`Typer.scala:166–188,201–203`). Its bound-level invariant
(`:221–228`) governs types in bounds, not arbitrary source references.
Neither establishes owner-reference closure or a source level ordering.

## 6. Scanner comparison after the relation

The actual scanner `settle_candidate_intrusion`
(`candidate_intrusion.rs:358–507`) constructs a graph from both bound sides,
then descends structural Function ports and Effect views. Its vertices
include structured Value endpoints and Effect endpoints, and its Function
walk visits both Value and Effect ports. It tests retained pairs with that
graph's SCC result. This is an operational dependency graph.

The graph defined in §2 instead has Value-variable vertices and witnessed
references in owned values. Even eliminating structural intermediate nodes
or reversing a lower-bound edge does not supply the missing Name/owner or
polar transport laws. The present comparison does not assert a new concrete
source mismerge or missed merge: the universal construction and pair
eligibility correspondence have not been established. It establishes the
exact consumer bridge still required:

> For every actual retained Value pair in the original quantified histories,
> the consumer's eligibility test agrees with mutual reachability of the
> jointly established owned-value references, and its actual equality
> realizes the justified ownership/typing transformation.

Whether this requires changing the scanner is primary-owned adjudication,
not an implementation conclusion of this note. Effects need their own
invariant. Merely filtering the scanner to Value endpoints would not prove
the missing Value relation or justify deleting any Effect operation.

## 7. Economy audit and minimum residual theorem

The frozen owner-introduction and retained-route methods both reached the
semantic Name/Lambda owner premise. The retained route certificate already
removes target-identity reconstruction debt for original recursive Names.
Another target inventory or payload SCC calculation would not establish
that semantic implication. The present method instead tested the next
constructional transport law and refuted its single-renaming version at the
actual shared Function constructor.

The parent fidelity/typing obligation is A/B. Reconstructing original Name
targets from bounds would be D and is unnecessary for the retained certificate.
The missing polar owner/copy interpretation is a genuine construction/typing
premise; relabeling it C or D would not discharge it. Retaining existing
copy-event and source-occurrence evidence may make its eventual bridge
construction-directed, but inventing a new certificate does not prove its
meaning. No new semantic layer or source restriction is adopted here.

The minimum residual theorem is now localized:

> At original Name/Lambda introduction and every actual polar extrusion,
> give a jointly resolved, scope/binder-preserving owned-value interpretation
> on the actual Value rows, including shared Function rows with opposite
> polar copies. Prove its preservation under Apply forwarding,
> accumulation/replay, boundary capture and fresh use. For every actual
> retained parent/copy pair, prove that mutual reachability in those
> references justifies the selected equality and that the actual consumer
> performs precisely that transformation, preserving required typing and
> principality under future inference.

The graph quotient lemma supplies the reachability part once ownership
transport is established. It supplies none of the missing introduction,
polar interpretation, type equality or consumer correspondence. The parent
remains OPEN. One next action: assign the construction owner the concrete
shared-Function polar owner/copy law above, together with the existing
resolved Name certificate, rather than another single-renaming/SCC probe.

## 8. Checks, resource envelope and dependency snapshot

Checks were static math/source citation consistency only: bounded `cat`,
`rg`, `sed`, read-only `git rev-parse HEAD` / `git branch --show-current` /
lease-path status, and `sha256sum`. HEAD and branch matched the primary's
baseline at inspection. Some broad initial captures truncated; the decisive
constructor, scanner, fresh-map and frozen-input sections were reread narrowly.
No code, tests, builds, Oracle, runtime experiment, Git mutation, delegation,
shared-record edits or user decision occurred. At most five lightweight
read commands were dispatched together; zero probe/heavyweight processes and
zero measurement samples. CPU, RSS and reasoning wall time were not measured.

Requested route: normal Sol/high proof leaf. Effective runtime model/effort
metadata is unavailable to this leaf; observed settings: unknown.
The inspected prover role has no model/effort pins and the configured defaults
are `gpt-6.1-sol` / `high`; those files are not runtime execution evidence.
No Astra escalation or hot-reload claim. No independent review has occurred;
the producer does not certify this artifact.

No dependency was edited by this leaf. The inspected live content hashes are:

| Dependency | SHA-256 |
| --- | --- |
| `notes/design/2026-10-10-parent-copy-scc-intrusion.md` | `2f08967e8f0477a1dacda62a211c620cd9cc3b80d476412b4c1e3d60506040c0` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `notes/theory/2026-10-11-value-owner-introduction-proof.md` | `f9c9d648d2bcfb91e97c2549c06819608860a73e0b59831695347be691946943` |
| `notes/theory/2026-10-11-mutual-recursion-native-value-reference-bridge.md` | `9f83f10566b11861a8b8079efff3bcb7dabd153287583d00e6ba71e50c988caa` |
| `crates/yu-hir/src/module/local_source.rs` | `906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed` |
| `crates/yu-solver/src/lib.rs` | `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94` |
| `crates/yu-solver/src/candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `crates/yu-solver/src/candidate_scheme.rs` | `9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1` |
| `crates/yu-solver/src/shadow_apply.rs` | `230ed70cc8575016967cdf16c6c814544b25e45b0fc687d6c89f0d38e8fb5cd6` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| `/home/momota1029/rust/simple-sub-reference/shared/src/main/scala/simplesub/Typer.scala` | `f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9` |

## Commit packet

Exact leased changed path:
`notes/theory/2026-10-11-value-reference-graph-mathematical-construction.md`.
Baseline: `0af7aa73f17841d01df0cff0b13e42b2eef6a114`.
Changed dependency hashes: none caused by this leaf; integration comparison
remains primary-owned. Claim/review status: abstract graph contraction
derivation, conditional ownership bridge, bounded native counterexample to
single-renaming transport; unreviewed, parent theorem OPEN. Checks already
run: static source/mathematical consistency and dependency hashes; no tests,
builds or executable probes. Proposed one-line checkpoint message:
`research: derive Value SCC contraction and polar Function transport obstruction`.
Shared-record deltas left to primary/curator: retain the original parent gate
and owner; record the graph quotient lemma separately from typing equality;
record the failed single-renaming transport route and exact shared-Function
polar owner/copy premise; preserve existing Name introduction and consumer
bridges as OPEN. No shared records or authoritative semantics changed.
