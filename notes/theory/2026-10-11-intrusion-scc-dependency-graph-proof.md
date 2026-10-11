# Intrusion SCCs: inequality, polarized expansion, and physical ownership

Status: unreviewed research checkpoint; constructive lemmas and counterexamples
Claim boundary: no theorem, production gate, or semantic choice is promoted
Owner: constructive proof leaf; independent review and integration belong to primary
Yulang baseline: `c8c62f473028d7684813e83284cc228b28a09831`
Ordinary reference: `simple-sub-reference` at `9bae772624c23b52a93c1b226157e16898b4d9db`
Exclusive output: this file

## 1. Frozen question and authority

The objective is to determine whether the current SCC adjacency expresses an
intrinsic dependency of type variables or the direction of physical bound
storage, and whether the approved parent/copy operation has a mathematically
justified SCC qualification. This note preserves ordinary Simple-sub generation,
accumulation, propagation, levels, extrusion, and generalization. Graph definitions
below are research definitions, not selected replacement semantics.

Governing sources:

- [Parent-copy intrusion](../design/2026-10-10-parent-copy-scc-intrusion.md),
  **Direct decision** and **Selected operation and compiler responsibility**:
  retain the genuine parent at extrusion; equate copy and parent when they enter
  the same SCC. Equality must affect solving and subsequent uses.
- [Top-level inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md),
  §§1–5: mathematical Simple-sub, proof-derived implementation, efficiency,
  ordinary inference without speculative typing search, and necessary safety.
- [Source Generalize](../design/2026-10-08-source-generalize-definition.md),
  §§2–4, selecting [source construction](2026-10-08-source-generalize-definition-and-proof.md)
  §§3–5; particularly §§5.1–5.3 for typed dependency closure and complete
  simultaneous component frames.
- Local ordinary reference `shared/src/main/scala/simplesub/Typer.scala`,
  `typeTerm`, `constrain`, `extrude`, `freshenAbove`, and `coalesceType`;
  local paper *The Simple Essence of Algebraic Subtyping*, §§3.2.2, 3.3.3,
  3.5.1, Figures 6–7, and §§5.2–5.3. The paper's core soundness argument is
  not a proof of Yulang intrusion or its effects extension.

Freeze the original qualification as follows. For every supported source
construction and every valid inference prefix, let `P` be its original scoped
constraint/evidence program, `T` its original binder tree, `sigma` its bound
state, and `Parents` its genuine extrusion records. For every record
`(c,p,s,d)`, where `c` is the copy, `p` its actual parent, `s` its creation
polarity and `d` its target level, the approved operation is

```text
same_SCC_D(rep(c), rep(p))  ==>  equate(c,p).
```

The requested mathematical bridge must define `D`, establish that actual
constructors/consumers implement it, and justify equality for the original
ordinary source domain while preserving soundness and required principality.
The operation itself is approved. The cited decision does **not** specify an
edge-generating relation `D`: constraint direction, bound containment, signed
expansion, or source dependency. Its statement cannot identify them by itself.

A principality-preserving *sufficient* bridge would show that every legal scoped
solution/strategy of `P` already identifies the pair at its original incidence,
so quotienting adds no restriction. This is not claimed to be the only possible
proof of a complete generalization algorithm: a different argument could
preserve public principal solutions without preserving every internal solution.
That different argument has not been supplied here.

Exclusions: no new source restrictions, eager solving, independent positive/
negative witnesses, moved quantifiers, hidden source roots, collapsed providers,
attachments, residual lineages or event witnesses. No choice of `D` is adopted.
No compiler changes, tests, Git mutations, or independent self-certification.

## 2. Three different graph definitions

Use `L_sigma(x)` and `U_sigma(x)` for lower and upper bound occurrences. Each
occurrence retains kind, owner, side, scope, relation, and admission lineage.
Their meanings are

```text
t in L_sigma(x):  t <= x
u in U_sigma(x):  x <= u.
```

A physical owner/side is an implementation encoding of the comparison, not an
extra subtyping axiom. Keep scope and instance identity in all vertices: fields
in separate incoming frames are not one vertex merely because they originated
from one template declaration.

### 2.1 G_le: directed comparison obligations

For a fixed scoped incidence, take vertices to be actual type/effect terms and
edges to be active comparisons `S <= T`, with direction `S -> T`. Stored lower
bounds contribute `t -> x`; stored upper bounds contribute `x -> u`. Duplicate
encodings of one comparison contribute the same edge. Genuine extrusion
contributes its actual one-sided comparison, not a provenance edge.

For ordinary functions, the operational decomposition obligation is

```text
Function(a,r) <= Function(b,s)  yields  b <= a, r <= s.
```

For the current four-port Yulang constructor, with argument value `a`, argument
effect `ae`, result effect `re`, result value `r`, actual solver children are

```text
F(a,ae,re,r) <= F(b,be,se,s)
  yields b <= a, be <= ae, re <= se, r <= s.
```

These are comparisons between corresponding ports. There is no axiom
`Function(a,r) <= a`, `a <= Function(a,r)`, or `Function(a,r) <= r`.
Constructor-to-child containment is therefore not inserted as a subtype edge.
Effect comparisons require their own actual laws and kinds.

Decomposition/propagation may be described as deterministic generation of
pending obligations; defining this graph does not require solving each newly
emitted constraint. When an edge is claimed as active, its actual owner must
have emitted/activated it. A stored suspended receipt is not proof of replay.

This is intrinsic to the specified comparison program and its activated
consequences. It is not a claim to contain all semantic consequences of the
complete source/Call/effect program. Full converse completeness would require a
separate theorem about that program and its effective consumer.

### 2.2 G_exp: actual polarized expansion duties

This graph records the recursion used by native bound expansion/coalescing.
Vertices include `(x,+)` and `(x,-)` for one underlying variable `x`, and signed
constructor occurrences. Edges are

```text
(x,+) -> (t,+)  for t in L_sigma(x)
(x,-) -> (u,-)  for u in U_sigma(x)
(Function(a,r),s) -> (a,opposite(s)), (r,s).
```

Yulang's four-port extension has signs

```text
(F(a,ae,re,r),s)
  -> (a,opposite(s)), (ae,opposite(s)), (re,s), (r,s).
```

For an admitted Effect view with a retained tail, the expansion step goes to
that tail at the view's actual polarity. The source rule for that view must
supply the meaning of the tail; it cannot be inferred from Value variance.

The two vertices `(x,+)` and `(x,-)` do **not** quantify two independent values.
They refer to the same source variable and assignment, but invoke different
expansion operations: positive expansion follows lowers; negative expansion
follows uppers. Native `PolarVariable`, `coalesceType`, and `extrude` explicitly
use this distinction. Sharing an operand does not make its two operational
states interchangeable. No automatic arc `(x,+) <-> (x,-)` follows from identity.
Adding such arcs is a graph definition change, not a proof step.

`G_exp` is grounded in the actual native expansion algorithm. Because it uses
actual stored sides, it is not claimed to be representation-independent under
arbitrary redistributions of bound storage. It characterizes expansion recursion,
not type equality or the complete source dependency closure.

### 2.3 G_store: current physical adjacency

The actual `settle_candidate_intrusion` graph has vertices

```text
ValueRow(i), EffectRow(j), PositiveFunction(t), NegativeFunction(t),
Allowance(v), Support(v).
```

Representatives canonicalize row identities. Every lower **and** upper bound
of a row contributes `owner -> bound`; the side is erased. Every Function
contributes outward edges to all four children, with endpoint signs chosen by
variance. Row endpoint keys themselves have no sign, so both row views map to
one vertex. Allowance/Support contributes an edge to its tail. Genuine parent
records are consulted after SCC calculation and do not add edges.

`Dependencies::intern` filters out primitive endpoints, contributions, and
`AnnotationMember`; in particular an AnnotationMember's retained tail is not
traversed by this SCC builder. Capture incidence, contextual relation records,
attachment bundles, provider identities, and witness dependencies are not
independently inserted as SCC edges.

Consequently the current edges are physical bound containment plus selected
constructor containment. Their direction is **not** uniformly subtype flow.
`ValueRow` identity being shared does justify calling this a row-dependency
graph if that dependency is separately defined as bound containment. It does
not prove that this graph is the dependency relation intended by the approved
intrusion operation.

## 3. Constructive lemmas and discriminators

The following are unreviewed derivations, with the stated scopes.

### 3.1 Subtype SCCs give a sufficient equality condition

For every model of active comparison edges in `G_le`, every directed path
`u -> ... -> v` entails `u <= v`, by induction on path length and transitivity.
Mutual reachability therefore entails `u <= v` and `v <= u`, i.e. equality
modulo subtype equivalence. A parent/copy pair qualified by this SCC condition
has a direct pointwise equality justification.

For a finite graph consisting solely of atomic variable comparisons interpreted
in arbitrary preorders, the converse also holds. If there is no path `u -> v`,
interpret variables in the preorder whose order is graph reachability (or the
quotient poset of its SCCs). All emitted comparisons hold but `u <= v` does not.
Thus SCC equality exactly characterizes forced equivalence in this restricted
free-preorder theory. This converse is **not** asserted for Function laws,
complete Call, effects, scoped witnesses, or the whole source program.

An implementation quotient additionally needs well-scoped substitution,
kind preservation, complete active replay, and retention of the original
provider/evidence/binder incidences. Pointwise type equivalence does not grant
permission to move a Shared witness into a per-use scope or to merge attachments.

### 3.2 Direct mutual row inequalities

For distinct ordinary rows `x,y` at equal levels, reference `constrain(x,y)`
first stores `y` in `U(x)`; `constrain(y,x)` stores `x` in `U(y)`. Native cache
keys are ordered pairs, so the first pair does not suppress the reverse pair.

- `G_le` has `x -> y -> x`: mutual subtype equivalence is forced.
- `G_store` has the same two row arrows.
- `G_exp` has `(x,-) -> (y,-) -> (x,-)`; both positive states may remain sinks.

For a real extrusion record the same semantic argument applies to a genuine
converse comparison, irrespective of where either comparison is stored. Native
positive extrusion supplies `parent <= copy`; native negative extrusion supplies
`copy <= parent`. In `candidate_intrusion_tests::close_cycle`, restoration uses
`opposite(creation_polarity)` **at the copy**. For positive extrusion this is
`U(copy)=parent`; for negative extrusion it is `L(copy)=parent`. Both are the
converse inequality. The existing owning test therefore demonstrates a genuine
sandwich, not two encodings of one inequality. This note reads that test;
it does not rerun it or promote its source reachability claims.

### 3.3 Function containment cycle: native source witness

Take ordinary reference AST

```text
Lam(f, Lam(g, Rcd(L = App(f,g), R = App(g,f)))).
```

Native `typeTerm` allocates same-level parameter rows `alpha,beta` and result
rows `gamma,delta`, then `App` emits exactly

```text
alpha <= Function(beta,gamma)
beta  <= Function(alpha,delta).
```

There are initially no parameter lower bounds, so constraining stores these
upper bounds without an opposite-bound child comparison. Record construction
retains the two result fields and adds no parameter equality. This is a
source-constructor witness in the reference term language, not an injected
abstract graph and not a claim about a particular Yulang parser spelling.

`G_store` contains

```text
alpha -> Function-(beta,gamma) -> beta
beta  -> Function-(alpha,delta) -> alpha.
```

It therefore places `alpha,beta` in one SCC. The actual signed expansion is

```text
alpha- -> Function- -> beta+, gamma-
beta-  -> Function- -> alpha+, delta-.
```

The displayed positive parameter and result states have no continuing bounds;
there is no expansion cycle in this witness. Identifying row signs creates the
physical cycle. That is exactly where the cycle arises, despite shared source
variable identity. It is not a claim that a graph selected to identify signs
must remain acyclic.

The constraints also do not force `alpha=beta`. A valid subtype assignment is

```text
alpha = Bottom
beta  = Function(Bottom,Int)
gamma = delta = Int.
```

The first constraint holds by bottom; the second is reflexive. `Bottom` and
`Function(Bottom,Int)` are not equivalent in ordinary algebraic subtyping.
Thus physical structural SCC membership neither implies signed recursion nor
forced variable equality in general. The witness contains no extrusion record,
so it does **not** by itself refute parent/copy-qualified intrusion on the
original Yulang source domain. That narrower bridge remains open.

Changing only lower-edge direction cannot repair this distinction: both bounds
in the witness are upper bounds. Even with correctly oriented bound comparisons,
adding bare Function-to-argument arrows would still confuse contravariant
containment with a subtype comparison. Result containment is covariance, but
also is not a standalone subtype inequality to the result.

### 3.4 Real parent plus duplicated encoding: operational falsifier

Create an unbounded genuine parent `p` at level 2 and invoke actual positive
extrusion to level 0, obtaining `c`. Source code retains `(c,p,+,0)` and installs
`c in U(p)`, meaning `p <= c`. Suppose restoration then admits `p in L(c)`.
That restored occurrence means the **same** comparison `p <= c`.

`G_store` sees `p -> c` and `c -> p`, and its actual qualifying loop would
merge the genuine pair. `G_le` has only `p -> c`; `G_exp` has `p- -> c-` and
`c+ -> p+`, without a cycle. The assignment `p=Bottom, c=Int` satisfies both
comparison occurrences and keeps the pair unequal.

`candidate_begin_bound_restoration` can physically admit this state without a
level check, by directly calling `candidate_insert_bound_with_evidence`.
With initially empty copy uppers, there is no opposite-bound product to replay.
This is a constructive operational falsifier for the universal implication
“all genuine extrusion-plus-arbitrary-restoration states make physical SCC
equality entailed.” It was **not executed**. The restoration admission has not
been derived from an actual supported source/fresh-use constructor, so this is
not a source-qualified counterexample to the approved operation. Source
reachability is an explicit missing premise, not an assumption.

The negative extrusion dual is `c in L(p)` plus restoration `p in U(c)`:
both mean `c <= p`, but physical adjacency again cycles. The discriminator
covers upper/lower duality as well as genuine parent provenance.

### 3.5 Polarity-qualified parent SCC: what follows and what does not

A natural *candidate* qualification using `Dep(v,s)=G_exp` compares
`(p,opposite(s))` and `(c,opposite(s))` for a recorded `(c,p,s,d)`.
This is the sign of the source link: positive extrusion emits
`p- -> c-`; negative extrusion emits `p+ -> c+`. Choosing `(p,s),(c,s)`
instead follows the selected copied bounds but does not follow that source
link. The recorded polarity identifies this choice; underlying row identity
alone does not decide it. Neither choice is adopted here.

The exact converse restoration used by the owning sandwich tests closes the
candidate signed SCC as well as the physical one. However, signed SCC
qualification still does not generally entail equality. For positive extrusion,
restore `Function(Int,p)` as an upper bound of `c`. The actual signed path is

```text
p- -> c- -> Function-(Int,p) -> p-.
```

The active comparisons are `p <= c` and `c <= Function(Int,p)`.
`p=Bottom, c=Function(Int,Bottom)` satisfies both and keeps them unequal.
This uses result covariance, so it remains a cycle without identifying row
signs. It is a genuine-parent-plus-restoration constructional discriminator,
not an established supported-source route; the restored structural bound
references the original higher-level parent and needs the same source/level
justification as §3.4. For negative extrusion the dual construction restores
`Function(Int,p)` as a lower bound of `c`, giving
`p+ -> c+ -> Function+(Int,p) -> p+`. The comparisons are
`c <= p` and `Function(Int,p) <= c`; choose
`p=Top, c=Function(Int,Top)`. Again equality is not forced.

Conversely, genuine mutual inequalities need not create a signed SCC under
native one-sided, level-oriented ownership. With `level(p)=2` and
`level(c)=0`, native `constrain(p,c)` stores `U(p)=c`; native
`constrain(c,p)` stores `L(p)=c`. Their semantic meaning is exactly the
mutual inequalities, but their expansion arrows are `p- -> c-` and
`p+ -> c+`; their physical arrows both point `p -> c`. Thus these graphs can
omit an equality that the comparisons entail. The equal-level mutual-row case
in §3.2 and the explicitly restored converse at the copy have different
owning transitions. They cannot be conflated.

Physical owner direction has a valid *interval dependency* interpretation:
both lower and upper expressions restrict the owner's admissible interval,
so both expressions are inputs to that owner's bound description. The native
level rule selects a legal owner and prevents a younger identity escaping into
older bounds. Calling those arrows storage containment does not deny this
semantically meaningful operation. It says that interval dependency, subtype
flow, signed recursive expansion, and permission to equate underlying rows
are separate claims. A new invariant limited to source-reachable genuine
parent/copy pairs might justify an intrusion rule using interval or signed
dependencies, but original Simple-sub's constructors do not prove it merely
by supplying the arrows.

## 4. Levels and the precise restoration seam

### 4.1 Ordinary native level invariant

For the ordinary reference define `level(Function(a,r))=max(level(a),level(r))`
and likewise the maximum over record fields. Variable levels are immutable.
The native invariant is

```text
t in L(x) or U(x)  ==>  level(t) <= level(x).
```

It follows constructively from the actual owning cases:

1. `constrain` checks this inequality before admitting each variable bound.
2. When it would fail, it extrudes the offending type before admission.
3. Extrusion leaves variables at or below the target unchanged; otherwise it
   allocates a memoized polarity copy at the target before visiting its bounds.
   The source link points from the original higher-level owner to the copy.
   Every copied bound is recursively extruded to the target. Function argument
   sign flips and result sign preservation do not change the level maximum.
   Memoization handles finite recursive bound graphs without introducing a
   higher-level target bound.
4. A later propagation child enters the same guarded constraining cases.

Give a physical constructor vertex its maximum child level. Every native
`G_store` edge is then level nonincreasing, both owner-to-bound and
constructor-to-child. Every directed path is nonincreasing. Two vertices in
one SCC must therefore have equal levels.

A newly recorded genuine parent/copy has `level(p)>level(c)`; hence it cannot
qualify in such a physical SCC while this invariant and those levels persist.
This is a conditional exclusion theorem, not a proof that current Yulang
intrusion never fires. Source level initialization, canonical level changes,
restoration, metadata, and Effect constructors require separate checking.

### 4.2 Ordinary freshening versus current candidate restoration

Reference `freshenAbove(boundary,body)` maps quantified rows to one new row
per original row at the use level, copies **both** bound sides, and stops at
older rows. Under `use_level >= boundary`, old shared rows have levels at
most the boundary and copied rows have the use level; the ordinary invariant
is preserved. This proof uses the native level-only eligibility and immutable
levels; it is not a proof about Yulang's `non_generic` metadata.

Current `Capture::row` selects

```text
local = level > boundary && !non_generic.
```

`expand_row` copies both sides only for local rows; older/shared rows retain
their mutable session bounds. `prepare_candidate_fresh_use` recanonicalizes
and rechecks eligibility; it creates eligible rows at `use_level`, otherwise
keeps the actual row. `begin_candidate_fresh_bound` preserves the captured
owner side, then `candidate_begin_bound_restoration` inserts that bound directly
before the saved-count opposite-bound replay. Restoration does **not** rerun
`candidate_extrude` for the admission itself.

The exact level premise needed here is, for every replayed bound `b` under the
actual fresh map `m`,

```text
max_live_level(m(b.item)) <= live_level(m(b.owner)).
```

For shared anchors retained above the boundary through `non_generic`, this
premise does not follow from `use_level >= boundary` alone. Its source
reachability and actual metadata owners are not established here. Structural
terms must use live rows, not a stale historical constructor-level cache.

Equality also lowers the representative's level to the minimum, unions
`non_generic`, imports both bound sides and replays lowers. Preserving the
maximum-level inequality after that import is another owner obligation; it
is not implied by choosing the minimum level. If intrusion legitimately
violates the ordinary reference invariant, a replacement scoped invariant
needs its own proof rather than treating the old theorem as still applicable.

A further caution: freshening can preserve a lower-side encoding chosen under
old levels while later equal-level constraint admission chooses an upper-side
encoding of the same comparison. Intrinsic comparison graphs remain stable
under this duplication; a physical containment graph need not. This is a
constructor-level possibility, not an established supported-source trace.

## 5. Effects and the source Generalize boundary

Effects have separate rows, levels and parent records. Current Function child
production uses opposite sign for argument Effect and the same sign for result
Effect; it is grounded in `lib.rs` Function dispatch, not an inference from
Value semantics. Effect views also carry tails and contextual/attachment
information whose semantic laws require their actual owners.

Current physical adjacency has Value/Function-to-Effect edges, but no
Effect-to-Value edges: Effect rows refer to Effect bounds, and Allowance/Support
refer only to Effect tails. Thus an SCC of that graph cannot contain both a
Value vertex and an Effect vertex. This follows by inspection and path
induction. It does not mean complete Call's Value/Effect coordinates are
independent or that effects can be generalized separately.

A specific coverage seam is `AnnotationMember(view,i)`: capture retains its
actual tail, extrusion visits it, but `Dependencies::intern` omits this endpoint.
A hypothetical Effect lower-bound chain

```text
e+ -> AnnotationMember+(view,i) -> tail+ -> e+
```

is an expansion cycle if the relevant lower bounds actually exist, while the
physical builder drops its first non-row target. This is a bounded graph
coverage discriminator, not a sourced execution or a selected effect law.
Contribution payloads, filter/replay contexts, provider/witness dependencies,
and retained attachments similarly require separate scope/owner analysis.
No Effect theorem follows merely from the Value counterexample.

Source Generalize uses publication-indexed typed `retain`/`fix` traversal.
`Internal(C,r)` retains the whole simultaneous component relation; external
`Established`, `OneShot` and actual free contract dependencies fix their fields.
Shared binders remain once; ViewLogic is per independent frame; actual event
and proof telescopes retain their original scopes. This is not `G_store`
reachability. The source recursive pair keeps both parameter descriptions
eligible without equating them merely because recursion connects the members.

The current capture/fresh-use machinery preserves side, relation reference,
evidence snapshot, source bound, and attachment bundles. Those retained
records are useful owning evidence; this note does not collapse them into one
untyped edge. No correspondence theorem equating `local && !non_generic` with
Source Generalize's eligible declaration constructor has been established here.
That bridge must preserve the original binding root, provider package, full
Call residual and all binder dependencies.

## 6. Owning constructor/consumer bridge

| Owner at pinned baseline | Actual evidence | What it does not establish |
| --- | --- | --- |
| Reference `Typer.scala:59`, `:88`, `:134`, `:166`, `:242` | App comparisons, bounds-before-propagation, polarity copies, freshening, signed coalescing | Yulang Effect laws or intrusion correctness |
| `candidate_extrusion.rs:21`, `:105`, `:137` | Real copies at target; parent retained; original gets one-sided source link | Same-SCC meaning or equality entailment |
| `candidate_intrusion.rs:171`, `:358`, `:620` | Same-kind provenance; physical adjacency; iterative SCC; parent qualification | Intrinsic comparison or complete source dependency graph |
| `candidate_intrusion.rs:511` | Actual representative merge, bound import, capture splice, min level, metadata union, lower replay | Preservation of original scoped solution/principality fiber on every qualifying source route |
| `candidate_scheme.rs:300`, `:424`, `:519`, `:566` | Local selection, four-port/tail capture, oriented bounds with evidence | Semantic eligibility of every retained/generated description |
| `candidate_scheme.rs:965`, `:981`, `:1221` | Fresh-use remap and captured-side restoration with source/attachment lineage | Level premise for every shared anchor or complete replay activation |
| `candidate_extrusion.rs:659`, `:697`, `:808`, `:840` | Restoration directly inserts; saved-count/live-index replay; ordinary row-side selection | Source justification of arbitrary restored cycles |
| `lib.rs:12418`, `:12501`, `:11996`, `:12229` | Structural extrusion, four actual comparison children, intrusion settling during typed drain | General soundness, hygiene, or public principality |
| `candidate_source.rs:532` | Source initialization of Value/Effect/parameter levels | A global invariant after all subsequent transport/restoration |
| Source Generalize construction §§5.1–5.3 | Typed dependencies and full joint frame semantics | Production SCC adjacency equivalence |

Line numbers are locators for this baseline, not separate authority. The
bridge stops before the unsupported universal inference from this table to
source correctness. No stored constraint is credited as activated merely
because it appears in a captured graph.

## 7. Exact open gate and obligation economy

**OPEN-GRAPH:** define the dependency relation meant by the approved phrase
“same SCC,” including row polarity identity, Function variance, Effect
views/tails and contextual/source scope. The present authority selects the
parent retention/equality operation but does not select among the relations
above. `G_store` is the observed implementation relation; native Simple-sub
justifies its containment interpretation, not the required equality bridge.
`G_exp` is the native expansion relation; `G_le` gives a sufficient equality
qualification. Substituting either for the observed/intended SCC is a new
choice until authority resolves this seam.

For any chosen graph, the remaining source/operational premise is exact:
for every source-reachable qualifying genuine parent/copy record, show that
its equality is compatible with the original complete scoped source program
and required principal observations, and that all actual constructors,
transports, restores and consumers preserve that invariant. The direct
sandwich cases discharge a sufficient local premise. The structural and
duplicate-storage discriminators prevent silently generalizing that result.

Two different routes were examined: native signed expansion, and native
level/constraint generation with the actual restoration owner. Neither
identifies an authority-selected SCC relation or supplies the full scoped
parent/copy bridge. Before another equivalent proof attempt, apply the
repository economy audit:

- The required equality soundness/principality and ordinary inference bridge
  is A/B. It remains open; renaming it as characterization does not close it.
- The exact graph choice is owned by the intrusion construction/authority,
  not by a downstream coalescer or prover.
- Reconstructing subtype direction from an erased side is D where the bound
  admission already knew that side. Current bound/evidence records retain it;
  consuming the canonical owner record is preferable to guessing from levels.
- Full arbitrary-model graph characterization beyond the required bridge is
  C unless the governing contract makes it necessary. The atomic-preorder
  converse above does not replace the A/B obligation.

No third equivalent graph/proof variant is attempted. The next action is for
the primary to adjudicate the intended scoped SCC edge relation using this
seam and the independent source mapping, then dispatch its specific missing
parent/copy preservation premise. An Astra escalation cannot supply missing
authority and was neither requested nor launched.

## 8. Checks, resources, frozen dependencies and commit packet

Checks already run: bounded `cat`/`sed`/`rg` source/rule reads; `git rev-parse`
for both repositories; `git status --short`; `sha256sum` of direct dependencies;
`pdftotext -layout ... -` with bounded excerpt capture; final lease/scope and
whitespace inspection. All checks are read-only except writing this exact file.
One exploratory `rg` used a nonexistent reference `src/*` path and returned 2;
locating `shared/src/main/scala/simplesub/Typer.scala` resolved it. No code,
tests, proof checker, Cargo process, runtime experiment, benchmark or Git
mutation was run. The operational falsifier is derived, not executed.

Budget: 45-minute packet; up to four lightweight command launches in early
batched source reads, then sequential source-reading processes; zero heavy
processes, zero descendants, zero timing samples. No aggregate
verification ownership was taken from the primary. Exact peak RAM/CPU were
not measured; commands completed without long-running sessions. Elapsed
wall-time is reported to the primary at handoff.

Runtime: task assigned to a constructive leaf. Configured normal defaults are
`gpt-6.1-sol` / `high`; prover role file has no model/effort pins. Actual requested
launch settings are not visible in the leaf packet and must be reported by the
primary from its launch arguments. The leaf has no tool-backed effective
runtime model/effort metadata: observed settings are **unknown**. No override,
hot reload, or Astra execution is claimed.

Frozen dependency SHA-256:

| Path | SHA-256 |
| --- | --- |
| `notes/design/2026-10-10-parent-copy-scc-intrusion.md` | `8ae4348a93dce6df1852a34b2294ebc5e4e256d8b018c1f6eaad42c502470a8e` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `crates/yu-solver/src/candidate_intrusion_tests.rs` | `61e30f6fc52097ac8a3be3577284d45baa27ab528c4a7f109e3bfcedb405fd46` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| `crates/yu-solver/src/candidate_scheme.rs` | `9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1` |
| `crates/yu-solver/src/candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `crates/yu-solver/src/candidate_effect.rs` | `ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df` |
| `crates/yu-solver/src/lib.rs` | `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94` |
| Reference `shared/src/main/scala/simplesub/Typer.scala` | `f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9` |
| `/home/momota1029/rust/simple-sub-reference-paper.pdf` | `5ab2bd4122caee17c20134e4cbe8dc8a4848c142de1e576b5fd178aed8787698` |

Commit packet:

- Exact leased path: `notes/theory/2026-10-11-intrusion-scc-dependency-graph-proof.md`.
- Baseline SHA: `c8c62f473028d7684813e83284cc228b28a09831`; ordinary reference
  `9bae772624c23b52a93c1b226157e16898b4d9db`. Changed dependency hashes: none
  observed at the final narrow dependency check; table above identifies inputs.
  HEAD moved to `b03e5868d5b5195de8d7ef9762f0cde169554869`; the exact dependency
  path comparison against the pinned baseline was empty. This movement does
  not change the proof's baseline.
- Claim/review: unreviewed constructive comparison, local lemmas and qualified
  counterexamples; OPEN-GRAPH and source-qualified preservation remain open.
  Producer supplies no independent certification or implementation authority.
- Checks: source reads, reference/baseline identity, dependency hashes,
  lease scope and whitespace only; no test/executable coverage claimed.
- Proposed checkpoint message: `research: distinguish intrusion SCC edge semantics`.
- Shared-record deltas left for primary/curator: record OPEN-GRAPH, separate
  physical containment from comparison and signed expansion, link the native
  Function witness and real-parent restoration falsifier with their coverage
  limits, and retain source/effect/principality gates without status promotion.
