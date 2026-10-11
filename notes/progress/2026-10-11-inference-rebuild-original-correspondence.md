# Inference rebuild: correspondence to original Simple-sub

Status: frozen static source crosswalk and bounded discriminators; unreviewed
Yulang redesign baseline supplied by primary: `1e65dd3d2af604bac2bbbc548503ff4edd398957`
Original baseline supplied by primary: `9bae772624c23b52a93c1b226157e16898b4d9db`
Exclusive lease: this file; leaf, no delegation
Prior crosswalk baseline: `d8c097e1f810fb26a8cf1936aa97059f6948bf32`.
Sections 1–3 preserve that ordinary reference characterization; §§4–5 add the
redesign source traces and extension boundaries at the new baseline.

## Objective and evidence boundary

Crosswalk deterministic ordinary generation, bound accumulation and activation,
recursive comparison caching, levels, polar extrusion, and generalization/use
freshening. Attack extra eager decision requirements, erased sharing,
unpolarized copies and subtype-as-reference shortcuts. This is an original
algorithm audit, not a verdict about the current Yulang candidate or a new
design. No previous Value-SCC witness is reused.

Authority: `notes/design/2026-10-11-yulang-inference-top-level-principles.md`
§§1–5, **Evaluation**, **Authority and integration**;
`rules/compiler-engineering.md`, **Natural compiler behavior and proof-obligation
economy**, **Deterministic Simple-sub inference**; `rules/design-authority.md`,
**Authority order** and **Active withdrawal of Simple-sub bypasses**.
Research/write boundaries follow `rules/research-lab.md` and
`rules/git-concurrency.md`. No implementation authority is exercised.

The reviewed import is
`notes/theory/2026-10-11-parreaux-simple-sub-proof-import.md`. Primary sources
were reread directly: Lionel Parreaux, *The Simple Essence of Algebraic
Subtyping*, printed pp.124:9–11,16–21,24–27, in
`/home/momota1029/rust/simple-sub-reference-paper.pdf`; and
`/home/momota1029/rust/simple-sub-reference/shared/src/main/scala/simplesub/Typer.scala`.
All Scala locators below refer to that file unless otherwise stated.
Original source/PDF hashes match the reviewed import's frozen values. Git
identity checks were excluded by this packet; commit pins are primary-supplied.

Claim classes: direct static source characterization; small symbolic
discriminators under explicit premises; imported published theorem statements
with incomplete proof sketches; and OPEN Yulang extension obligations. No
executable experiment, general theorem proof or independent review occurred.

## 1. Mechanism crosswalk

| Mechanism | Paper statement / algorithm | Pinned source behavior | Rebuild correspondence obligation |
| --- | --- | --- | --- |
| Deterministic generation | §3.2.1 and Fig.8: names instantiate the environment; Lambda binds a fresh monomorphic parameter; App introduces a fresh result and an arrow demand; records/projections use their ordinary constructors | :59–84 selects exactly one syntax branch; App types callee then argument, calls `constrain`, returns its result variable; no typing search | Relate actual Yulang source constructors to its selected typing and complete Call; retain the same callable/argument/result incidence rather than select independent witnesses |
| Accumulation | §3.2.2, Fig.9: install a new bound before visiting opposite bounds | :115–120 prepends an upper/lower and immediately visits the current opposite list; ordered variable-variable matching need not store both directions | Preserve generated facts and the insertion-before-activation invariant; any batching/worklist schedule needs its own simulation |
| Opposite-bound activation | pp.10–11: a new bound must become consistent with every opposite bound; §5.3.1 explains temporary inconsistency during recursion | Upper insertion replays existing lowers; lower insertion replays existing uppers. Arrow consumer :106–108 reverses arguments and preserves results; record consumer :109–114 demands every right field | A recorded demand is insufficient without its actual current/future activation consumer, including extended effect/context facts and retained continuation |
| Recursive cache | §3.2.2 caches completed/in-process comparisons; §5.3 needs cache/subtyping-context and temporary-consistency invariants | :88–103 creates a fresh default cache for a root call, returns on object identity, caches only pairs with a variable endpoint before recursion, and shares that cache within recursive calls | Preserve identity and cache lifetime. Persistent caching, different keys or extended recursive objects require a new justification; source comments alone do not prove termination of extensions |
| Levels | §3.5.1, Fig.6: let RHS runs one level higher; higher variables must not escape into lower-level bounds | :48–55 raises RHS level; :209–226 uses immutable variable levels, structural maximum levels, primitive level zero, and states the bound-level invariant | Establish the analogous invariant and scope boundaries on actual Value/Effect constructors; a structural-level shortcut depends on that invariant |
| Polar extrusion | Fig.7, pp.18–19: copy above-target variables, including selected bounds; preserve acceptable-level subtrees; argument reverses polarity | :121–159 uses an operation-local `(Variable,Boolean)` map. It installs a copy before descending; positive copies selected lowers and links original to copy, negative copies selected uppers and links copy to original | Preserve polar distinction and actual shared anchors. Yulang parent retention and SCC-qualified equality are additional obligations, absent from this original algorithm |
| Generalization / freshening | §3.5.1 wraps RHS type with its level boundary; use instantiation copies above-boundary variables. Paper omits the freshening implementation | :166–189 memoizes by variable alone, copies both bound lists jointly, shares below-boundary subtrees; :201–207 instantiates schemes but returns monomorphic types unchanged | Distinguish one fresh map per use from extrusion's polar map. Prove selected Yulang generalization/publication boundaries and outer-capture sharing independently |
| Recursive definition | §3.5.2, Fig.8: recursive RHS uses an open monomorphic expected type, then constrains inferred RHS against it | :48–55 binds one fresh expected variable at the raised level and wraps it only after RHS inference/constraining | Mutual definition SCCs and intrusion are extensions; the original single-recursive-let route does not supply their theorem |

The original interleaves generation with ordinary `constrain`. It is therefore
incorrect to describe it as deferring all propagation until generation ends.
It is equally incorrect to treat each generated demand as requiring an already
known concrete provider, exact solved monotype or chosen typing. The top-level
principles forbid extra special decision rules; the original's ordinary
accumulation/propagation call is the concrete behavior to preserve.

## 2. Small static discriminators

### Eager concrete-provider requirement

Use the original term `Lam(r, Sel(Var(r), a))`, mathematically `λr. r.a`.
Assume ordinary well-scoped source, a current level `L`, fresh empty-bound
variables, canonical constructors, and successful finite allocation.
Lambda introduces `alpha`; the monomorphic Name returns that exact variable;
projection introduces `beta` and calls
`constrain(alpha, Record(a:beta))` (:64–67,75–78,207).
The right structure has level `L`, so :115–117 records it as an upper of
`alpha`. The lower list is empty. The call succeeds and Lambda returns
`Function(alpha,beta)` without any known record lower or selected field value.

Thus a candidate requirement “prove an existing concrete record provider at
projection generation” contradicts this original finite execution. Later
lower arrival is checked against the demand by :118–120; omitting that later
check is also a different algorithm. This is a source-qualified static
derivation for the original term, not a Yulang source acceptance test.

### Erased sharing during scheme instantiation

For original `let id = λx.x in {a=id,b=id}`, let-bound parameter `v` has level
`L+1` and the scheme boundary is `L`. Its body is `Function(v,v)`.
Each use invokes `freshenAbove` with a new map (:62–63,166–174,201–202).
Within one invocation, both ports receive the same fresh identity `v_i`.
Across the two invocations the fresh identities differ. Consequently the two
fields have shapes `Function(v_a,v_a)` and `Function(v_b,v_b)` with
`v_a != v_b`. Per-occurrence cloning erases the first equality; reusing one
fresh map across uses erases the second independence.

For an outer capture, original `λx. let keep = λy.x in keep` keeps outer `x`'s
row at level `L`. `keep`'s formal is above the boundary and freshens; the
captured `x` endpoint is at/below the boundary and remains the same row
(:168,184). A candidate “freshen every reachable variable” loses this anchor.
These are direct source characterizations of the original let implementation,
not applications of the paper's non-let soundness/principality theorem.

### Unpolarized extrusion

A small original source witness is `λk. let z = k (λx.x) in 0`.
Type the outer Lambda at level zero. Its parameter `K` is level zero, while
the let RHS is level one (:48–55). The inner Lambda gives
`Function(v,v)` with `v` at level one; App result `b` is also level one.
The RHS submits `K <: Function(Function(v,v),b)` (:64–72).
The level guard fails, so :121–123 actually extrudes the right demand negatively
to level zero. The outer arrow argument switches to positive; the inner arrow
visits `v` negatively and positively (:143–148).

Both visits allocate distinct fresh level-zero variables keyed by `(v,false)`
and `(v,true)`. The transformed demand contains `Function(v_minus,v_plus)`
inside its argument, with `v_minus != v_plus`. No original intrusion merges
them. The negative visit occurs first and can affect the original bound lists
read by the positive visit; this derivation does not assume two immutable
snapshots or independent bound histories. It needs only the actual separate
keys, fresh allocation and port traversal. A single unpolarized extrusion map
would collapse identities that this source execution keeps distinct.

This differs from freshening's shared unpolarized map because the operations
have different contracts. Freshening is coherent scheme renaming; extrusion
is level-aware approximation with polar bounds. No Value-reference SCC or
Yulang copy reachability conclusion follows from this ordinary source trace.

### Recursive comparison cache

As a state-level discriminator, let same-level distinct variables `a,b` have
`upper(a)=[b]`, `upper(b)=[a]`, and empty lowers. Submit canonical `Int <: a`.
Insertion/replay produces `Int <: b`, then revisits `Int <: a`. The reference
cache returns on that revisited variable-containing pair (:100–102); deleting
the cache yields unbounded alternation and repeated insertion under these
supplied rules. This is a conditional regular-store derivation, not a claim
that this store was generated by a particular source program. No execution
or source-reachability search was performed.

The paper's strengthened invariant is needed to justify accepting cached
recursive obligations; mere pair repetition is not an independent semantic
oracle. No theorem about a session-global cache or arbitrary Yulang recursive
effects is imported from this finite discriminator.

### Subtype comparisons as graph edges

Original `constrain(s,t)` enforces a typing inequality by structural descent,
bound insertion, extrusion and replay. Neither Fig.9 nor :88–159 defines a
source-owned Value-reference graph or intrusion qualification. The paper's
§4.2 discussion of MLsub simplification automata uses separate labelled
subtyping/constructor relationships; it is not the user's SCC definition.
Thus exporting comparison direction as the approved Value-reference edge
relation has no original-source premise. This audit introduces no graph
counterexample or replacement graph: the Yulang constructor/reference and
SCC-consumer correspondence remains an explicit extension obligation.

## 3. What the paper proves or leaves outside its proof scope

The paper §5 restricts its claims to non-let-polymorphic Simple-sub and gives
proof sketches, with complete proofs outside its scope (p.24). Soundness and
principality/completeness are stated at p.26; the imported note retains their
exact quantifiers, scheme order and coalescing interpretations. Lemmas 2/4/5
concern constraining, consistency/preservation, termination and completeness,
but their strengthened cache/context invariants and auxiliary arguments are
not fully provided. Section 5.2 assumes an omitted immutable counterpart.
Let correctness is proposed separately in footnote 15, not discharged there.

The pinned source also has two operational deltas from the paper pseudocode:
Fig.9 caches all comparisons, while :100–103 caches variable-containing pairs;
Fig.9 accepts equal primitive names, while the pinned source relies on object
identity (:93; `package.scala:12`) for its canonical primitives (:20–25).
An arbitrary API input with separately allocated equal-name primitive objects
is outside a claimed exact source/pseudocode equivalence until bridged.
These known deltas do not justify rejecting ordinary canonical constructor
paths or inventing special generation rules in the rebuild.

Yulang extension obligations remain OPEN: complete four-port Call and effect
meaning; protection/hygiene and joint provider/attachment/residual lineage;
extended replay and recursive-cache invariants; successful suspension and
meaningful recovery; reference-preserving extrusion, selected parent/copy SCC
intrusion; recursive-component/generalized scheme publication; soundness,
required principality and ordinary source completeness. Original theory/source
provide a base, not proof of those additions. Full internal failure restoration
is not imported as a general requirement; inconsistent publication remains
forbidden by the governing principles.

## 4. Redesign: direct lambda, application and recursive-function traces

These are finite hand derivations from the pinned `Typer.scala`, not new
experiments or universal theorem proofs. Hypotheses: well-scoped reference
terms, initially empty bounds, distinct fresh identities, canonical `IntType`,
finite successful allocation, current level `L >= 0`, and the actual ordered
constrain/freshening branches. No Yulang Value-owner interpretation is assumed.
`F(s,t)` denotes the reference's two-port `Function(s,t)`; `lb` and `ub` denote
its physical bound lists. Source identifiers, inferred type identities and
semantic Value variables remain distinct objects until a bridge supplies them.

### Lambda: `lambda x. x`

At :64–67 allocate `a` at level `L`; extend the environment with the
monomorphic binding `x -> a`. Name lookup at :62–63 returns `a` itself via
:207. The root is `F(a,a)` with no constraints and no nonempty bounds.
Ordinary coalescing is `a -> a`: the argument and result share one free type
identity. If this is a nonrecursive let RHS, `a` instead has level `L+1` and
the scheme boundary is `L`. Each Name use produces `F(a_i,a_i)`, with one
map within a use and distinct fresh identities across uses (:166–189).

The corresponding unused-parameter term `lambda x. 0` constructs `F(a,Int)`
with the same formal type port although the body has no source Name use of
`x`. This establishes an exact distinction between Name occurrence and type
port occurrence; it does not select either occurrence relation as Yulang's
Value-reference graph. No new SCC witness is claimed.

### Higher-order application: `lambda f. lambda x. f x`

Allocate lambda parameters `a,b` and App result `c`, all at level `L`.
The two Names return `a,b`. App submits `a <: F(b,c)` (:68–72).
The level guard succeeds; :115–117 installs `ub(a)=[F(b,c)]` and visits an
empty lower list. The root is `F(a,F(b,c))`; every other list is empty.
Thus this ordinary application can be inferred before a concrete provider
exists, and its return row `c` is distinct from callee `a` and argument `b`.
Its ordinary coalesced form is

```text
(a intersect (b -> c)) -> b -> c
```

The same `b,c` occur in the stored demand and returned Function. The direct
declarative type `(b -> c) -> b -> c` follows by T-Var/T-App/T-Abs. The
scheme equivalence follows from substituting `a := Top` in one direction and
outer-arrow contravariance/intersection elimination in the other, as in the
reviewed import's ordinary `lambda f. f 1` calculation. This local derivation
does not prove the paper's universal principality statement or Yulang Call.

The closed term `((lambda f. lambda x. f x) (lambda y. y)) 1` gives a small
actual source continuation. Let `d` be the identity formal, `e` the first
App result and `r` the second, also at level `L`.

1. First App compares `F(a,F(b,c)) <: F(F(d,d),e)`.
2. Contravariance installs `lb(a)=[F(d,d)]`, replaying the already stored
   `F(b,c)` from the same comparison. Its two child comparisons are
   `b <: d` and `d <: c`. With equal levels and ordered left-variable
   matching these install `ub(b)=[d]`, `ub(d)=[c]`; they need not also
   install matching lower edges on `d,c`.
3. Covariance installs `lb(e)=[F(b,c)]`.
4. Second App inserts `ub(e)=[F(Int,r)]`; replay compares the one actual
   lower `F(b,c)` against that demand. It derives `Int <: b` followed by
   `c <: r`.
5. The first comparison installs `Int` in `lb(b)` and replays `b`'s upper
   to install `Int` in `lb(d)`, then `lb(c)`. The second inserts `r` in
   `ub(c)` and replays its `Int` lower, installing `lb(r)=[Int]`.

The returned root is `r`. The second comparison activates replay when its
upper is inserted against the already retained lower; symmetrically,
inserting either polarity against an existing opposite bound activates that
pair. The trace retains provider/argument/result incidence. The final
ordinary positive coalescing is `r union Int`; this note does not assume
that ordinary coalescing drops the free variable. There is no extrusion,
failed primitive comparison, source execution, handler or SCC operation.

### Recursive function: `let rec f = lambda x. f in f`

At :48–55 allocate expected type `q` at level `L+1` before typing the RHS.
Infer the lambda with a fresh formal `a` at that same level. Its Name `f`
returns the exact monomorphic `q`, so the RHS root is `F(a,q)`. Submit
`F(a,q) <: q`; :118–120 installs `lb(q)=[F(a,q)]`. Its upper list is empty.
Then publish the reference wrapper `PolymorphicType(L,q)` in the environment.
The final Name invokes `freshenAbove(L,q)` at level `L`: allocate `q'`,
record `q -> q'` before descending, allocate `a'`, and resolve the recursive
result occurrence through that map. The result is precisely

```text
q' at level L: lb(q') = [F(a',q')], ub(q') = []
a' at level L: lb(a') = [], ub(a') = []
```

The copied cycle is finite and shared. A later independent use gets a new
`q'',a''` with the same internal cycle shape. No polymorphic instantiation
occurs inside the recursive RHS; no extrusion parent is created in this
example. The bound graph contains the guarded type occurrence `q'` under
Function result; no Yulang source-Value SCC, qualifying parent/copy pair,
runtime termination or let-principality theorem follows from this trace.
In particular, the paper's non-let proof theorem cannot certify this
recursive-let example merely because Fig.8 includes its generation rule.

## 5. Exact extension and conflation boundary

Additional controlling sources for this redesign continuation:
`2026-10-10-parent-copy-scc-intrusion.md`, **Selected operation and compiler
responsibility**, **Value-reference SCC clarification**;
SCC redesign charter §§13,17–18,21–24 (the role clarification in §24
narrows §16); complete-Call contribution definition §§2–4; and the protection
notation note's **Intended reading**. The latter is Draft but records the
settled local user meaning of `'e?`; it grants no new elaboration authority.

| Required extension | Original exact fact | Missing premise or consumer |
| --- | --- | --- |
| Value references and their SCC | `Var` returns an instantiated type; Lambda forms two ports; App returns a fresh result after submitting its arrow demand. Original source defines no semantic Value-owner payload law. | The actual owner must introduce/forward Value contents and their reference targets for each constructor, alias, recursive definition, extrusion and fresh use. Apply's returned result row does not by itself establish ownership of its source callee/argument references. Stop here rather than choose that meaning. |
| Parent/copy intrusion | Polar extrusion retains ordinary inequalities and selected bounds, keyed by identity and polarity; original source has no SCC merge operation. | Retain parent at copy creation; derive actual Value-reference adjacency and same-SCC qualification; prove selected equality preserves typing, lexical/existential scope, bounds, capture sharing and fresh-use independence. Qualification alone is not an original equality lemma. |
| Variable-only levels | Reference variables carry immutable levels; Function/Record cache structural maxima. | Supply the variable-comparison/extrusion traversal invariant required by charter §23, and apply the existential guard in §22 on every derived comparison. Reference structural maxima are a comparison implementation, not permission to attach Yulang constructor-level semantics. |
| Complete Call | Ordinary App submits one two-port demand; an actual lower Function yields argument and result comparisons jointly. | Supply the jointly scoped four-port interface and genuine complete Call operation, including original callee computation, whole argument reification, actual returned provider/receiver entry, ordered pending suffixes, alternative arms and future-use witness. Simple matching effect marginals does not supply complete C0/CallMem. |
| Effect hygiene | No reference effect, protection, activation or attachment constructor exists. | Establish typed-path transport across arguments/captures/results/stores/adapters; retain source origin, provider/attachment/residual lineage and symbolic dependencies; prove release/expiry/subtraction separately. `'e?` changes protection of independently attributed emitted contributions only; it supplies no attribution, membership or handler selection. |
| SCC generalization/publication | Single recursive let uses one expected monotype; use freshening preserves a coherent cycle and outer anchors. | Establish component formation, all-member sharing/generalization, extended bound activation and consistency before atomic public publication. The reference has no mutual-definition SCC theorem or successful-suspension lifecycle. |

Current candidate is inspected only as comparison material. In
`shadow_apply.rs:1332–1383`, the negative Function demand retains argument
value/effect and return effect/value; the callee is kept separately and the
admitted pair is `(callee,demand)`. At :1408–1440 the callee effect and
invocation effect separately flow to application effect. These are actual
constructor/submission facts, not evidence that complete Call formation,
receiver-role elaboration or source result ownership has been proved.
`candidate_extrusion.rs:763–807` replays inserted bounds against opposite
bounds through the contextual consumer; no all-path activation theorem is
inferred from this one entrypoint.

`candidate_intrusion.rs:358–490` constructs an operational dependency graph
from both lower and upper row storage, then Function's four children and
Effect view tails, and checks retained parent/copy component identity. This
code shows which adjacency the candidate uses. The approved Value graph is
over actual references in Values; the original reference source does not
identify that graph with this operational graph. Conversely, lower/upper
storage is not a reason to disqualify a payload occurrence that the actual
Value owner does establish. The user explicitly permits references across
the extrusion-family tree, so ancestry alone neither licenses nor excludes
an edge. No candidate-code correctness finding or language reinterpretation
is claimed by this source crosswalk.

Four conflations therefore have distinct failed premises: a source Name use
is not automatically a type-port occurrence; a subtype judgment is not itself
a source Value edge; physical bound traversal needs the actual owner law;
parent ancestry records creation, not Value reference. The decisive missing
premise is constructor-owned Value content and transport, rather than a third
graph model assuming one of these identities. No equivalent toy probe or
second semantic model was produced.

## 6. Follow-up: approved complete Call to Apply-result ownership

Status: frozen bounded source-semantic derivation and first absent bridge;
unreviewed, no graph or theorem closure. Baseline remains
`1e65dd3d2af604bac2bbbc548503ff4edd398957`; this additive follow-up performs
no new ordinary Simple-sub trace. Its question is whether the approved source
contracts, beyond the original paper, already supply the Apply-result
Value-owner equation. Neither `Own(result,callee/argument)` nor its negation
is an assumption or conclusion.

### 6.1 Governing adopted cases and distinct indices

The adopted source-Generalize definition §2 selects construction
`2026-10-08-source-generalize-definition-and-proof.md` §§3–5. Its §§3.1–3.2
give actual Name, Lambda, Result, Bind and Call rules and inclusion/checking
choices; §4 builds those local clauses; §5.2 supplies lawful whole-frame uses.
The genuine local source laws L1–L5 remain premises; selection of Build does
not fill an unprovided local law. Additional selected sources are:

- `2026-10-08-contextual-function-membership-definition.md` §§2–3 and its
  adopted realization §§3.1,4.1–4.2: actual-provider membership, environment
  restriction/rebind and same-value Return.
- `2026-10-07-complete-call-contribution-definition.md` §§2–4 and the adopted
  construction §§4.1–4.2,6: the full Call operation, ordered Bind and
  result/future placement, with independent complete C0.
- `2026-10-08-call-source-interface-definition.md` §§2–3 and
  `2026-10-08-native-signature-formation-definition.md` §§2–3, selecting
  signature incidence construction §§3.3–3.4: complete result/provider/future
  port packaging, contextual receiver placement and inherited origin partition.
- Charter §§17–18,21,24: whole argument reification, result synthesis, Value
  parameter entry, and actual receiver role. Typed-core §§6,7,9 are used only
  for the source premises reused by these selections, not as adoption of
  their entire Draft package.

Keep distinct the source Call occurrence `c`; semantic result endpoint
`A_c` in `I(c)=Computation(E_c,A_c)`; actual native result Value row `u_c`;
callee-returned callable provider `p_f`; argument's returned provider `p_a`;
complete Call's eventual output provider `p_o`; and static contractual
owner/receiver coordinates in `PortProv`. A runtime provider is not itself
a native Value row. A static owner partition of contractual constituents is
not already the adjacency of references in the Value owned by `u_c`.

### 6.2 Smallest positive source chain, conditional on genuine local laws

Fix one genuine source rule instance with its original scope tree, assignment
`xi`, valid immutable environment, independently admitted whole carrier,
actual callable decomposition, complete receiver membership, legal result
checking, and original complete Call declaration/C0 where its contribution
is used. No provider, scope or witness is selected independently per port.
The following is a source derivation under those premises, not a construction
of arbitrary inhabited environments, C0 or complete solver correspondence.

1. For Name callee code, the environment projection and pure Return yield
   the exact `CalRet` tuple `(v_f,p_f,C_1,w_1)` and its membership at `A_f`
   (realization §4.2). Same-value VIncl and Function membership eliminate at
   this retained actual decomposition; they do not substitute another
   callable sharing its descriptor (realization §3.1).
2. Complete Call's ordered Bind passes that same `p_f,C_1` to receiver
   dispatch, with the independently supplied whole argument. Argument
   reification is inert. For Value entry, receipt precedes the designated
   Force; a completed Force supplies `(v_a,p_a,C_2,w_2)` and its hereditary
   certificate. Typed ValueBind installs precisely this tuple in the
   parameter environment (realization §4.1; complete Call §4.2).
3. The actual body, any source-designated consumer or admitted conversion,
   and invocation return produce the actual output tuple
   `(v_o,p_o,C_3,w_3)`. Result/Return preserves that tuple at the original
   result slot. An actual conversion has its own selected result object;
   no equation with the preceding body provider is assumed.
4. Genuine complete result checking places this same tuple in the source
   result contract `Comp(E_c,A_c)`. In the Name/Name decorated generation
   clause this is the actual `CIncl(ExecuteCallableImage(...),
   Comp(E_c,A_c);e_result)` conjunct, not a bare equality of result ports
   (`2026-10-06-source-call-generation-construction.md` §5).
5. S-ReturnFuture and IF Return/Result place the actual output provider's
   full hereditary future interface at the original result/future slots.
   Root insertion appends a receiver route while preserving each antecedent
   origin; it does not change the owner to the surrounding Call
   (signature construction §§3.3–3.4). The complete Call witness still
   includes its callee, carrier, entry and alternative interfaces.

For a pending callee, the receiver/argument is an unreached ordered suffix;
for pending argument entry, rebind/body/return remains the suffix. Neither
case asserts a returned result tuple. Raw resumption retains its actual
handle and current world. Independently licensed W/Z alternatives keep
their own output-provider/future contracts and original evidence; the
structural chain above does not replace their semantics. These clauses
preserve complete Call and effects rather than project them to a successful
Return relation.

`ReturnImage(Name(d),environment)` in the source-generation note §3 names
the exact source Name result image, not merely its printed `Comp(empty,A)`
interface. Its Name inversion gives the original binding projection. The
whole argument hole remains independent: the returning-Name image is only
the source diagonal. Neither ReturnImage nor receiver dispatch introduces
an equation assigning native row `u_c` the callee/argument source syntax.

### 6.3 Identity and constant-function source cases

Take genuine ordinary unannotated Value-entry closures `id x = x` and
`konst x = 0`, with their actual introduction/complete-invocation laws and
no executing conversion at result. Their actual Pure role and Value entry
remain separate decisions. Fix one admitted carrier whose completed Force
returns `(v_a,p_a,C_2,w_2)`; it may have exposed effects or requests before
that completion. These are conditional source reductions, not parsed,
executed or universally inferred test programs.

For `id`, ValueBind installs the argument's same hereditary certificate.
The body Name projects that binding; Result/Return forwards it. Thus the
completed Call output has `v_o=v_a` and `p_o=p_a`, at the actual output world
and result incidence. The callable provider used for dispatch remains
`p_f=p_id`; it is not substituted for `p_a`. If `v_a` is a closure with a
genuine capture, that returned closure retains its existing capture and
future interface under the same lawful restriction. This proves provider
forwarding; it does not prove which native Value-row targets constitute
references of `u_c`.

For `konst`, the same Value-entry Force and rebind occur even though the
body ignores its parameter. The authentic literal body and Result produce
its literal value/provider `(0,p_0)` with its original result evidence.
The complete Call therefore returns `p_o=p_0`, while retaining argument
execution effects, callee/provider evidence and the complete Call witness.
No conclusion that `u_c` has no argument/callee references follows: retained
contract/evidence fields, actual returned value content and native row-owned
Value content have not been identified. Conversely, the surrounding Call's
retained operand interfaces do not prove such references belong to `u_c`.

These cases separate returned-provider identity from whole-Call operands.
They do not constitute two models of the approved graph or a source-qualified
counterexample to either candidate owner equation. Pending/nonreturning
carriers have the corresponding complete prefixes and no invented output.

### 6.4 Scope/use transport and the exact native stop

Gen-Call-0 scope transport acts once on the complete original tuple
(`2026-10-06-source-call-generation-construction.md` §4.4); capture does
not choose a fresh independent provider. Source-Generalize §§5.1–5.2 keeps
actual binding objects, OneShot/Shared fields and established contracts;
a fresh client opens one whole component description frame at the original
scopes. Aliases route to that same frame. Fresh description choices do not
rerun the initializer or choose another returned object. Event fields
remain beneath the actual invocation/response/resumption telescope; an
EventProof in another description frame does not create another runtime
event. IF-Use/Ref transports the whole original interface and owner partition
under that same lawful substitution. These are positive source laws, not
an inference-row freshening/equality theorem.

The actual native Apply collector supplies `result=pos.value` together with
one source expression, callee/argument, recipe, level and checking cause
(`candidate_source.rs:394–411`; `candidate_call.rs:29–58`). Admission joins
that row to the negative Function result port (`shadow_apply.rs:1332–1383`);
`candidate_call::observe` validates source/port incidence (:282–374).
At a reached positive/negative Function comparison, `lib.rs:12493–12530`
dispatches the positive result port against that negative result port,
alongside the other three child pairs. These facts give a source-anchored
native output endpoint and covariance constraint. They do not supply a
source Return tuple or a semantic interpretation of its row-owned content.

**First absent rule:** relate the genuine Call result at `A_c`, with its
actual `(v_o,p_o,C_3,w_3)` and full result/future certificate, to the Value
content and actual reference targets owned by native `u_c`; preserve this
interpretation through the particular lawful use and extrusion history.
The selected source rule catalogues stop at original semantic result and
contractual incidence; the inspected native constructors stop at anchored
ports and comparisons. No inspected rule bridges those endpoints into the
required Value-owner/reference equation. This is the specific unprovided
source-to-native content law, not proof of logical independence or absence
from every repository file. Lack of an ownership field is not an impossibility
argument. No semantic definition, graph restriction or new implementation
mechanism is proposed.

Thus Name projection, type comparison, bound storage, static contribution
owner/receiver and parent ancestry each fail at their own distinct bridge.
The positive result-provider/port laws above reduce the gap: they establish
the source output tuple and its lawful transport. They do not settle the
remaining native row-owned content meaning, parent/copy SCC qualification,
intrusion equality, complete solver Call correspondence or effect hygiene.

### 6.5 Follow-up checks and dependencies

Commands were bounded `rg`, `sed`, `cat` and `sha256sum`; no execution,
test/build, checker, Oracle, Git or extra write path. Coverage is the selected
source constructor cases and the two conditional source reductions above.
Initial `rg` included nonexistent `spec/` and two guessed source-note names;
correct existing documents were located with `rg --files`, then their exact
sections read. Some combined output truncated; decisive sections were read
narrowly. No full source-semantics inventory or negative existence search
is claimed. Zero seeds, ranges, mutation runs or heavyweight processes;
CPU/RSS and reasoning wall time are unknown. The packet supplied no numeric
resource limit. This follow-up passed bounded independent `compiler_referee`
delta review with no findings in its source-rule/ownership scope. The review
does not establish repository-wide absence or certify the parent theorem. A final read-only
artifact inspection found zero trailing-whitespace lines and ten balanced
fence markers; the 16 rechecked source/selection/candidate dependencies were
unchanged.

New direct dependency snapshot (SHA-256; previously captured Call/authority
and `shadow_apply.rs` hashes remain above):

```text
Function views       4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1
Call formation       4940e031b83d3d0315f17beb51ba2e952ec64ae7d57d9ae0d086024c7305ca9f
Call IF              20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c
Contextual membership 0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0
Generalize selection 46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38
Signature selection e6c6cf995a3618172e45b4f8cdf4578313c057c6ec1e3e118c4dc11b6f162ab9
Generalize construction e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240
Input realization   fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a
Signature incidence 7367ce8eb69376583386c6d675d067712ec6fa173e96f458ee34ce390dc8901a
Call contribution construction ead206bff341c82993acbaecda25ae1d3a760397796bbbbb53ba3ef917a53fb1
Call generation      6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073
candidate_source.rs 13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49
candidate_call.rs   79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35
solver lib.rs       c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94
Typed-core Draft    0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e
Ordinary source Draft ee3f5cf8185d516775b8915b0fda6dbb07390c3ecad7ac028eb5995581dff917
```

No executable oracle is used. The conditional reductions share the approved
actual-provider, source entry/Return and lawful result-checking laws; they
do not independently validate those laws or native ownership. Recommended
next action: assign the exact source-result-to-native-Value-content rule to
its responsible owner using the preserved result/provider/use coordinates,
without replacing it by source Name union or whole-contract port provenance.

## Checks, resources and next action

Static commands: `cat`, bounded `rg`, `nl -ba`/`sed`, `pdftotext -layout` to
stdout for pages 9–11,16–21,24–27, and `sha256sum`. The lease was written with
`apply_patch` and reread. No code edit, test/build, Scala execution, checker,
Oracle, Git command, shared-record edit, delegation or review. Initial combined
output truncated; the decisive original constructors and paper pages were
reread narrowly. Up to four lightweight read commands were batched; actual
overlap, CPU and RSS were not measured. Zero heavyweight processes, probes,
measurement samples, random seeds or enumerated ranges. The 30-minute bound
was not exhausted; precise reasoning wall time is unknown. Requested/observed
model and effort were not exposed as runtime metadata.

The source/PDF and symbolic derivations share the original constructors and
explicit level/store premises; there is no differential oracle or executed
mutation evidence. Hypothetical shortcut changes above were reasoned about,
not applied. Full theorem proofs, arbitrary-store source reachability and
Yulang implementation conformance were not searched or claimed.

Frozen hashes:

```text
paper PDF    5ab2bd4122caee17c20134e4cbe8dc8a4848c142de1e576b5fd178aed8787698
Typer.scala  f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9
package.scala c33b015e51baf32cb42ca48e6452ab005c85ac185a590ec870c19ef198b4fcb2
README       e226d6268278cda2604cdc1168bbcb5077726f1d437af2137b1b5f006c4d3d8e
import note  cd2b84a84d16be8856766f0514a2f400cf224ac95b6e81e42d4a7a875036e113
principles   edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389
```

Redesign continuation checks: direct paper/source rereads and SHA-256 checks
match the imported external snapshot. The three original source traces above
were hand-derived without execution; their coverage is exactly those terms
and hypotheses. No tests, builds, checker, Oracle invocation, Git command or
mutation was run. Numeric process/CPU/RAM/wall limits were not specified in
the redesign packet; only lightweight reads and this leased note write were
used, with no heavyweight process. CPU/RSS and reasoning wall time remain
unknown. The earlier 30-minute envelope belongs to the prior crosswalk lane,
not an inferred new grant. Output capture was bounded; several combined reads
truncated, followed by narrower reads of decisive reference and candidate
windows. No omitted whole-file search or theorem proof is claimed complete.
Final dependency recheck found every captured direct Yulang dependency hash
unchanged. A read-only Python artifact inspection found zero trailing-whitespace
lines and eight balanced fence markers; no compiler implementation was tested.

Redesign dependencies captured before writing, in addition to the hashes above:

```text
parent-copy authority 2f08967e8f0477a1dacda62a211c620cd9cc3b80d476412b4c1e3d60506040c0
SCC charter           547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed
complete Call         4c83a095dce3636ada842bfc32c18cf0ef598db0e361861fb8e659745b74411e
protection notation   87c2c39bf41a8b652fb96cb3409cf9e2c5735c96e4ccfc8b7c5b7f8380ba6050
shadow_apply.rs       230ed70cc8575016967cdf16c6c814544b25e45b0fc687d6c89f0d38e8fb5cd6
candidate_extrusion   fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0
candidate_intrusion   aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0
```

One recommended next action: the primary resolves/supplies the exact
constructor-owned Value content and transport premise to the constructive
lane; retain all parent graph/equality, complete Call and hygiene gates OPEN
until their own source and consumer evidence is established.

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-11-inference-rebuild-original-correspondence.md`.
- Yulang baseline SHA: `1e65dd3d2af604bac2bbbc548503ff4edd398957`; original dependency commit: `9bae772624c23b52a93c1b226157e16898b4d9db`, both primary-supplied.
- Changed dependency hashes: none caused by this leaf; source/PDF match the import snapshot. Current Git/baseline verification remains primary-owned because this packet excluded Git commands.
- Claim/review: frozen unreviewed static characterization and scoped symbolic discriminators; no theorem, implementation or cutover gate closure; writes stopped before submission.
- Checks already run: original source/PDF/import reads, exact locators, dependency SHA-256 snapshot, lease inspection; no tests/builds.
- Proposed checkpoint message: `research: derive redesign source traces from original Simple-sub`.
- Shared-record deltas left to primary/curator: preserve original generation/replay and scheme-sharing facts; add recursive/lambda/apply trace locators; record constructor-owned Value content/transport as the exact absent original premise; keep intrusion equality, complete Call, hygiene and all parent theorem statuses OPEN. No shared file was edited.

## Follow-up commit packet

- Exact leased/changed path: `notes/progress/2026-10-11-inference-rebuild-original-correspondence.md`, additive §6 and this follow-up packet only.
- Baseline SHA: `1e65dd3d2af604bac2bbbc548503ff4edd398957`, primary-supplied; no Git query.
- Changed dependency hashes: none in the final 16-dependency recheck; additional Draft snapshots are recorded in §6.5. No dependency was edited by this leaf. Baseline/live Git verification remains primary-owned.
- Claim/review status: frozen conditional source-semantic derivation, identity/constant source reductions, and bounded first-absent native content rule; independent compiler-referee delta review clean. No graph equation, counterexample, or theorem closure.
- Checks already run: exact adopted-source/constructor window reads, dependency hashes and read-only artifact whitespace/fences; no tests/builds/execution.
- Proposed checkpoint message: `research: trace complete Call result to native ownership boundary`.
- Shared-record deltas intentionally left to primary/curator: record the positive same-provider result/Return/future and lawful-use laws separately from the missing source-result-to-native-row-content rule. Do not identify static contractual owners with Value-reference adjacency; retain full Call, effects, intrusion equality and parent proof gates. Writes stopped before review submission.
