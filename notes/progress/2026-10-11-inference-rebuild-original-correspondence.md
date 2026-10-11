# Inference rebuild: correspondence to original Simple-sub

Status: frozen static source crosswalk and bounded discriminators; unreviewed
Yulang baseline supplied by primary: `d8c097e1f810fb26a8cf1936aa97059f6948bf32`
Original baseline supplied by primary: `9bae772624c23b52a93c1b226157e16898b4d9db`
Exclusive lease: this file; leaf, no delegation

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

One recommended next action: use this crosswalk as the ordinary rebuild
contract, assigning the constructive lane the extended accumulation/replay
invariant with its cache and publication boundary. Do not add a concrete
provider precondition, erase per-use sharing or merge extrusion polarities to
make that obligation smaller.

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-11-inference-rebuild-original-correspondence.md`.
- Yulang baseline SHA: `d8c097e1f810fb26a8cf1936aa97059f6948bf32`; original dependency commit: `9bae772624c23b52a93c1b226157e16898b4d9db`, both primary-supplied.
- Changed dependency hashes: none caused by this leaf; source/PDF match the import snapshot. Current Git/baseline verification remains primary-owned because this packet excluded Git commands.
- Claim/review: frozen unreviewed static characterization and scoped symbolic discriminators; no theorem, implementation or cutover gate closure; writes stopped before submission.
- Checks already run: original source/PDF/import reads, exact locators, dependency SHA-256 snapshot, lease inspection; no tests/builds.
- Proposed checkpoint message: `research: crosswalk inference rebuild with original Simple-sub`.
- Shared-record deltas left to primary/curator: distinguish ordinary immediate constrain/activation from extra eager decision rules; record different sharing contracts for freshening and polar extrusion; retain paper proof-scope limits and all Yulang extension obligations.
