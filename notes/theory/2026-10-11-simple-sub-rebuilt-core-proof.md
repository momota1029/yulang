# Bounded reconstruction of the native Simple-sub core

Status: unreviewed research proposal with local derivations and a minimized
obstruction; not Authoritative and not a closed source theorem.
Date: 2026-10-11
Lease: this file only; producer is a leaf and performs no Git mutation.
Baseline: `d8c097e1f810fb26a8cf1936aa97059f6948bf32`,
`research/simple-sub-intrusion`.
Reference: `/home/momota1029/rust/simple-sub-reference`, commit
`9bae772624c23b52a93c1b226157e16898b4d9db`.

## Objective and frozen obligation

Construct a small mathematical core from native constraint generation, bound
accumulation, propagation, levels, extrusion and generalization, while retaining
the user's selected parent/copy intrusion. The old Rust candidate is inspected
only to locate construction and consumption responsibilities. Its behavior is
not the semantics of the redesign.

The original obligation remains: for every supported, resolved Yulang source
program and its actual lexical scopes, binders, annotations, definition uses,
recursive boundaries and Call occurrences, the deterministic successor must
produce sound typings and the required principal schemes, preserve natural
inference and effect hygiene, and implement equality for actual extrusion
parent/copy pairs qualifying in the Value-reference SCC. A successful run must
retain all required constraints and obligations and publish a consistent
interface. A failed or suspended run must obey the top-level principles.

This is an obligation schema over the selected Yulang typing judgment, not a
new definition of that judgment. In particular, this note does not supply an
alternative complete Call semantics. Its quantified source domain has not been
narrowed to the reference calculus. The original goal stays open.

For the local lemmas below, separately freeze these mathematical hypotheses:

1. There is a finite initial graph of simple type constructors and variables.
   Structural terms are finite between variable occurrences; bounds may cycle.
2. Native variables have immutable lexical levels. The level of a structural
   term is the maximum level of its variable occurrences, taking primitives
   to have level zero. Every stored lower and upper bound has level at most
   its owning variable's level. Call this invariant `L`.
3. The reference's bound insertion, opposite-bound propagation, polarized
   extrusion cache and freshening operations are used exactly as specified
   below. Successful completion, where assumed, is explicit. Lemma 1's
   pair-coverage conclusion additionally requires its initial and bulk-operation
   coverage premises; the operations alone do not establish those premises.
4. For semantic lemmas only, each kind has a preorder of interpretations;
   constructors obey their stated variance. A valuation gives one shared
   interpretation to each variable. It satisfies a lower bound `l` of `a`
   when `l <= a`, and an upper bound `u` when `a <= u`.
5. No desired Value-owner law, SCC-to-subtype implication, equality of parent
   and copy, complete Call bridge or hygiene theorem is assumed.

Conclusions are limited to the named lemmas. Excluded from proved scope are
full source soundness/principality, termination of the complete Yulang solver,
contextual effect admission, handler dispatch, complete Call construction,
public scheme publication and compiler cutover. These exclusions describe
unproved work; they are not source restrictions.

## Governing sources and claim classes

Authority is the top-level principles §§1–5 and Evaluation/Authority; the
parent-copy decision's Selected operation, Value-reference SCC clarification
and Retained boundary; annotation hygiene §§1,3–4; residual lineage's Selected
policy. The parent's current redesign instruction makes the old candidate a
comparison only.

Workflow sources are `rules/agent-orchestration.md`, Model routing and Astra
escalation / Proof delegation and decomposition; `rules/research-lab.md`, One
semantic baseline / Evidence quality and stopping unproductive loops;
`rules/design-authority.md`, Authority order / Natural compiler behavior;
`rules/compiler-engineering.md`, Natural compiler behavior and proof-obligation
economy / Deterministic Simple-sub inference; and `rules/git-concurrency.md`,
Disjoint-file mode / Research-only checkpoint fast path.

The reference paper is *The Simple Essence of Algebraic Subtyping*, local PDF
`/home/momota1029/rust/simple-sub-reference-paper.pdf`: §§3.1–3.3 (native types,
generation, propagation and coalescing), §3.5/Figs.6–9 (levels, extrusion and
let), and §§5.1–5.3/Figs.10–12 (declarative rules and proof sketches). Section
5 explicitly restricts its formalization to the non-let-polymorphic version
and says full proofs are outside its scope. Neither its theorem statements
nor its million-term experiment establish Yulang's new intrusion or effects.

Local derivations here are mathematical lemmas for the frozen model, awaiting
independent review. The source inventory is an inspection-based bounded bridge.
The extended effect/Call signature and intrusion implementation conditions are
proposals and open obligations. No executable probe is claimed.

## Small state and four distinct relations

Let `A_V` and `A_E` be disjoint sets of Value and Effect row variables, each
with kind, lexical level and binder identity. Positive and negative occurrences
refer to the same underlying row; polarity determines the selected view and
extrusion cache coordinate, not a second binder. Use these native terms:

```text
V ::= a_V | Primitive | Record(label:V, ...) | Fn(V,E,E,V)
E ::= a_E | Empty | Concrete(resolved-family, type-arguments)
    | EffectView(annotation-owner, scope, polarity, concrete-atoms,
                 symbolic-tail, attachment, context, provider, witnesses,
                 residual-lineage)
Fn's relative polarities: (-,-,+,+).
```

`Fn(V,E,E,V)` is a signature for the four ports of the current Yulang native
carrier. Ordinary pure Simple-sub is its two-Value-port restriction. The effect
interpretation and complete Call behavior of the other ports are not proved by
declaring this signature. A concrete effect contains resolved identity and type
arguments; a type variable is not a concrete annotation atom.

The proposed state is

```text
Σ = (variables, LBound, UBound, pending constraints, dependency dispositions,
     owned Value descriptions, parent records, canonical equality,
     annotation/context/Call obligations, schemes, publication state).
```

Keep these relations distinct:

| Relation | Meaning | What does not produce it |
| --- | --- | --- |
| `C(l,u)` | Generated subtype comparison to propagate | Value reachability alone |
| `S(a,b)` | A variable reference occurs in a bound stored on `a` | A comparison before choosing its storage owner |
| `R(a,b)` | Value variable `b` occurs in the actual owned Value description of `a` | A comparison judgment or a parent record alone |
| `P(c,p,pol,k,creation)` | Actual extrusion created copy `c` from parent `p` at target level `k` | Matching IDs, levels, shapes or endpoints |

`R` must be obtained by traversing the source-owned Value description, including
its actual reference occurrences. Structural intermediates can be traversed
to project paths onto Value variables without adding subtype edges. It is not
defined to be `S` here, and is not free to be chosen after seeing an SCC. The
missing definition/constructor law for those descriptions is a real bridge
obligation. There is no ban on cross-family references: a parent can reference
a child and a nephew an uncle whenever the actual constructors emit them.

Ordinary bounds, parent provenance and canonical identity need no duplicate
semantic authority. If the Value description naturally is stored bound syntax,
the owner can define `R` by those actual occurrences. Section “Level/SCC
obstruction” then applies; merely naming another graph does not avoid it.

Attachment, annotation authority, provider, witnesses and residual lineage
remain separate coordinates. Canonical row equality may redirect row references
but cannot identify separately constructed residual recipes or grant a filter
at an unrelated occurrence. A complete joint witness is transported as a whole;
the signature does not license selecting its coordinates independently.

## Native generation and propagation

For the reference calculus, resolved variable use instantiates its scheme;
lambda allocates one parameter row and returns a Function of that row and the
body type; application allocates a result row and generates
`type(f) <= Function(type(a), result)`; selection generates the one-field
record demand; record creation constructs its field types. A nonrecursive let
types the initializer at `h+1`, then stores `(boundary=h, body)`; recursive let
first allocates an open monomorphic row at `h+1`, exposes that same row to the
initializer and constrains the initializer's type below it before wrapping the
result scheme. These are `Typer.scala:48–83`, paper §3.2/Fig.8. They preserve
the original lexical binder; recursion does not instantiate the open binder.

For a generated comparison, decompose Function contravariantly at its argument
and covariantly at its result, and records by required labels/depth. At a
variable `a`, insert a level-safe upper or lower bound first, then propagate
against every opposite bound. If the bound's level is too high, extrude it to
`level(a)` in the required polarity and continue constraining. This follows
`Typer.scala:88–129` and paper §3.2.2/Fig.9. Generation need not establish
individual constraint satisfiability in advance.

An asynchronous implementation can preserve these operations with a worklist,
but its pending/discharged distinction must remain real. Every opposite pair
must either have completed processing or retain an owned pending continuation.
Any cache hit must be justified for the exact state and obligation; a cache key
alone does not prove discharge, and changed dependencies must invalidate an
obsolete completed disposition. These are proposed implementation conditions,
not a proof that the old Rust scheduler satisfies them.

### Lemma 1: opposite-bound replay preserves the constraint solution set

For every valuation satisfying the current store, if `l` is a lower and `u`
an upper of the same row `a`, then `l <= a <= u`, hence `l <= u` by
transitivity. Explicitly retaining or processing this derived comparison does
not remove a store solution. Adding a newly generated bound is exactly adding
the associated comparison `l <= a` or `a <= u`; it can remove solutions, as
the source constraint requires. This is a semantic entailment lemma, not a
termination or completeness theorem for decomposition.

The **pair-coverage** part is a separate conditional operational lemma for a
finite interval with retained row identities and monotone bound collections.
An opposite pair is indexed by its actual owner and both bound incidences,
not just by endpoint shapes. Its coverage means an owned pending processing
obligation or an independently justified completed/cache/transport disposition
for that exact pair and its dependencies. The entailment above alone is not
such a processing disposition. Freeze these additional premises:

1. **Initial coverage:** every opposite pair already in the initial store has
   such coverage. Empty bound stores satisfy this vacuously; an arbitrary
   populated finite initial graph does not. The coverage must be supplied or
   established by its initialization owner.
2. **Replaying insertions:** each ordinary insertion first stores its bound
   and then retains/processes its comparison with every currently present
   opposite bound, as at `Typer.scala:115–120`. Reentrant insertions obey the
   same rule.
3. **Bulk coverage preservation:** an extrusion, freshening or other direct
   initialization step must preserve valid inherited dispositions and account
   for every newly formed opposite pair. It may transport an old disposition
   only under a separately justified joint remap/dependency law; otherwise it
   must retain/process that pair's obligation. Any invalidated disposition is
   replaced by a valid disposition or owned pending work. This premise is not
   proved by copying bounds or admission origins.

Proof of coverage under these premises: classify the first event at which a
final pair is present at its owner. An initial pair is covered by premise 1.
For a replaying insertion, the later bound sees the retained earlier opposite
bound; premise 2 creates its obligation, including for a reentrant insertion.
A pair first present after a bulk step is accounted for by premise 3.
Subsequent steps retain valid coverage or replace invalidated dispositions.
Thus every final pair has coverage. Only if all initial, inherited and newly
created pending obligations subsequently complete or receive justified
dispositions may quiescence imply completed coverage of all final pairs.
This establishes ordinary insertion's pair creation, conditional coverage
preservation, and no unconditional execution/completeness result. Equality
merges and nonmonotone changes require their separate coverage accounting.

**Source-relevant bulk accounting.** Reference extrusion writes its parent
link and selected copy bounds directly (`Typer.scala:149–154`), bypassing
`constrain`'s insertion replay. A fresh copy initially receives only one bound
side, so its local opposite-pair set is empty at that point; the new parent
link can nevertheless form pairs with existing opposite bounds at the parent.
Those obligations need their own justified disposition or activation.
Reference freshening assigns both sides directly (`:173–181`), so copied
lower/upper pairs need valid inherited coverage under the same per-use remap
or new obligations. Shared rows retain their existing coverage; changed
dependencies still require revalidation. Lemmas 2, 3 and 5 prove their stated
level/interpretation/renaming properties, not transport of replay dispositions.

The old Rust candidate similarly inserts extrusion links and selected bounds
directly (`candidate_extrusion.rs:123,308–323`); origin transfer does not prove
pair processing. Its scheme restoration instead inserts the bound, saves an
opposite count and constructs exact replay children
(`candidate_scheme.rs:965–976,1221–1266`;
`candidate_extrusion.rs:659–678,716–759`). These are activation-owner facts,
not proof that every inherited or newly created pair completes, particularly
across other bulk changes. Initial and bulk coverage remain explicit OPEN
source/implementation premises; the full source theorem is unchanged.

## Polarized extrusion

At target `k`, return an acceptable-level term unchanged. Traverse structural
constructors with composed polarity. On a variable `p` above `k`, memoize a
new variable `c` at level `k` by `(p,polarity)` before visiting its selected
bounds and retain the actual `P` record:

```text
positive: add p <= c; copy/extrude p's lower bounds into c's lowers
negative: add c <= p; copy/extrude p's upper bounds into c's uppers
```

The two polarities may create distinct copies. The directed link is an
inequality, not equality. These are `Typer.scala:131–159`, paper Fig.7 and
§3.5.1. Parent retention is the selected Yulang extension at this creation
point; it adds provenance without changing the meaning of the directed link.

### Lemma 2: native extrusion preserves level invariant `L`

For every finite initial graph satisfying `L`, a completed native extrusion at
`k >= 0` returns a term of level at most `k`, and all newly created bounds
respect their owner's level. Acceptable subterms already satisfy the conclusion.
For a copied variable, `level(c)=k<level(p)`, so the link stored at `p` respects
`L`; every selected copied bound has been recursively extruded to level at
most `k`, so its storage at `c` respects `L`. Structural cases take maxima and
reverse polarity only at contravariant children. Polarity reversal does not
alter the level argument.

This is a finite graph traversal argument: memoizing `(p,polarity)` before
traversing bounds prevents a bound cycle from allocating a repeated copy.
For `n` reachable original variables it allocates at most `2n` row copies in
one target-level extrusion. This is a row-allocation bound only; it is not a
whole-program time bound or a promise of no structural copying. Level-safe
subsequent ordinary bound insertions preserve `L` by their guards. Equality
with level changes is not covered by this lemma.

### Lemma 3: directional approximation and a conservative extrusion extension

For every valuation satisfying the post-extrusion directed links, constructor
variance gives `t <= extrude_+(t)` and `extrude_-(t) <= t`. At a copied variable
these are the recorded links; acceptable terms are reflexive. At Function the
argument direction reverses and result direction is retained; records preserve
the direction. These comparisons recurse only through structural syntax;
variable bound cycles do not require an unguarded recursive-subtype assumption.

For every valuation satisfying the old store, extend it by giving every new
copy its original parent's interpretation, with the *same* valuation used for
all copies. Then every copied structural bound has its original interpretation,
every copied bound is satisfied and every parent link is reflexive. This
establishes conservative extension of the isolated extrusion operation under
the stated interpretation hypotheses. It does not assert that future uses
must equate the copies, or that equality is entailed: existence of one extension
with equal copies is not universal equality. It does not prove the additional
consumer comparison succeeds.

The extension applies to Effect constructors only after their actual
interpretation, scope transport and variance are established. Declaring an
EffectView field is insufficient. This note establishes the pure structural
case and gives a conditional signature for the extension.

## Level/SCC obstruction and the selected intrusion

The selected operation is retained as a rule schema:

```text
P(c,p,pol,k,creation) and c,p in the same actual Value-reference SCC
    => equate c and p in solving and later uses.
```

The SCC is over Value variables and references in their values. Comparisons
and parent metadata do not themselves form its edges. Effect parent/copy
transport needs the actual qualifying Value ownership/correspondence; this
note supplies no invented Effect-SCC substitute.

### Lemma 4: level-respecting reference SCCs are level-homogeneous

For every graph in which each edge `a -> b` satisfies
`level(b) <= level(a)`, levels do not increase along any path. If `a` and `b`
are in the same SCC, paths in both directions give both level inequalities,
hence `level(a)=level(b)`.

Consequently, in every native store satisfying `L`, the graph `S` of variable
occurrences in either bound side has level-homogeneous SCCs. Every occurrence
in a stored bound is no higher than the bound, which is no higher than its
owner. Since actual extrusion creates `level(c)<level(p)`, an unchanged native
store can never put that distinct parent/copy pair in the same `S` SCC.

This is not a refutation of the user's operation. It proves the minimum
obstruction to identifying the actual Value graph with strictly
level-respecting native bounds while expecting such an intrusion to occur.
The missing construction premise is exactly this:

> Which actual Value-description constructor emits a reference path from the
> lower-level copy back to its higher-level parent, or which justified level
> transition makes their levels coincide before qualification, while preserving
> native bound scoping, natural inference and generalization?

If reference levels are not constrained by native bound levels, the graph must
have its real owner and scope law traced independently. If levels can change,
Lemma 4 applies to each graph snapshot satisfying its hypothesis; the proof
must identify the earlier level mutation and establish `L` for later bounds.
No absence-of-qualifying-pairs conclusion is claimed for the Rust candidate.

### SCC reachability alone also does not entail equality

Even at one level, native occurrence cycles are not mutual subtype proofs.
Consider two Value rows at the same level with these bounds:

```text
U(p) contains c and Record(left:Int, next:c)
U(c) contains Record(next:p)
L(p)=L(c)=empty.
```

The bound-occurrence graph has `p -> c -> p`, and it includes the directed
constraint `p <= c`. In ordinary structural record semantics the shared
valuation `p=Bottom`, `c=Record(next:Bottom)` satisfies all bounds: Bottom is
below both uppers of `p`, and `c` is its own required upper. But `c <= p`
fails. Thus this native cyclic storage pattern plus one directed link does
not imply equality. No independently chosen marginal witness is used.

This is a minimized mathematical falsifier for the shortcut “SCC implies
equality”. It is not an authentic extrusion parent pair: the two levels are
equal. Relabeling it with an extrusion `P` record would assume a false
construction history. Making `p` higher than `c` would violate `L` at the
upper of `c`; that is precisely the first obstruction. No source-qualified
counterexample to the selected Yulang rule is claimed.

The decisive semantic bridge, beyond graph construction, is therefore one of
the following arguments grounded in the approved source typing judgment:
the qualifying source cycle entails both inequalities, or the selected
intrusion is a source-typing rule whose equality must be included and whose
soundness and required principality must be proved. This note does not select
between those accounts. The reference algorithm has no parent tracking or
intrusion rule from which either follows.

### Conditional equality merge fact

If a source-grounded rule establishes that a row pair must be equal, replacing
them by one representative and taking the union of both lower and upper bound
collections preserves exactly the old store solutions satisfying that equality.
Every pre-merge bound becomes the same comparison on the representative;
conversely an equal pre-merge valuation restricts to the representative.
Transport all current/future obligations and retain separate recipe lineage.

All merged lower/upper cross pairs must then be activated: old within-row
replay does not cover newly created cross pairs. This is the equality-merge
implementation condition, not a derivation of the qualifying equality premise.
Lowering a representative's level to the minimum requires re-establishing `L`
for *every* transferred bound; the set-union fact does not prove that a
level decrease is scope safe.

## Generalization and instantiation

A reference scheme stores `(boundary=b, body=t)`. Instantiation shares every
row at level at most `b` and allocates a fresh row for each reachable original
row above `b`, using one per-use memo across both bound sides. Different uses
have disjoint fresh rows. This is `Typer.scala:166–203`; the paper §3.5.1
describes it but leaves the freshening implementation out.

### Lemma 5: freshening retains correlation and low-level sharing

For every finite native store satisfying `L`, boundary `b`, and instantiation
level `h >= b`, memoized freshening maps each high-level original row to
exactly one fresh row at `h`. All references to that row, through either
bound side or any structural occurrence, use that same image. Each low-level
row remains itself. A low-level row cannot have a bound reference above `b`,
by `L`, so its unchanged state contains no stale generic copy reference.
Bounds of fresh high rows contain only fresh rows at `h` or shared rows at
levels at most `b`; hence they obey `L`. Independent per-use memos give fresh
identity independence without duplicating shared lexical captures.

This proves a graph renaming/scoping property. Universal scheme semantics,
equivalence to duplicating let-bound definitions, and required principality
under the added intrusion/Effect/Call rules remain separate obligations.
In particular, a merged generic parent and nongeneric copy can change which
binders are quantified; proving its scope/typing justification is required.

## Actual constructor and consumer inventory

All Rust locators below are at the pinned baseline and are comparison evidence.
No redesign correspondence is asserted merely because an old function exists.

| Responsibility | Actual source locator | Evidence and unresolved bridge |
| --- | --- | --- |
| Native generator | Reference `Typer.scala:48–83` | Lambda/App/let allocation and original binders are explicit; no Yulang effects or intrusion. |
| Native bound owner | Reference `Typer.scala:115–126` | One storage orientation chosen by level; opposite replay follows ordinary insertion. Lemma 1 additionally needs coverage of populated initial stores and non-replaying bulk updates. |
| Native extrusion | Reference `Typer.scala:134–158` | Polarized memo, directed parent link and selected copied bounds. No parent record. Direct writes at `149–154` bypass insertion replay; newly formed parent-side opposite pairs require separate coverage. |
| Native scheme use | Reference `Typer.scala:166–203` | Both bound sides freshen with one memo; levels select binders. Direct assignments at `180–181` require justified transport of old pair dispositions or activation of copied pairs. |
| Yulang source actions | `crates/yu-solver/src/candidate_source.rs:168`, `394–411`, `445–461` | Actual Apply recipe retains callee/argument/result, effect positions, occurrence and checking input; lambda recipe retains parameter/body. No distinct authoritative Value-description constructor is established here. |
| Actual Apply consumer | `crates/yu-solver/src/shadow_apply.rs:1304–1399` | Validates recipe/source incidence, creates four-port negative demand and native invocation interface, and invokes `constrain_live_value`. This is not complete Call. |
| Candidate extrusion parent creation | `crates/yu-solver/src/candidate_extrusion.rs:82–162` | Copy is fresh at target; `retain_extrusion_parent` precedes memo/link/selected bounds. |
| Parent record owner | `crates/yu-solver/src/candidate_intrusion.rs:171–220` | Retains actual pair, polarity and target. This fact should not be reconstructed downstream. |
| Candidate bound activation | `crates/yu-solver/src/candidate_extrusion.rs:808–838` | `candidate_apply_value` inserts then invokes `candidate_replay_bound`; direct extrusion insertion is a different path and needs its own activation accounting. |
| Candidate SCC and equality | `crates/yu-solver/src/candidate_intrusion.rs:358–506`, `513–605` | The old graph traverses both bound sides, Effect rows/views and four-port Function children; canonical merge transfers both sides, sets minimum level, and replays lowers. It does not establish the new Value-owner law or scope proof for all transferred bounds. |
| Captured schemes and later uses | `crates/yu-solver/src/candidate_scheme.rs:39–88`, `965–976`, `1221–1266`, `1512`; `candidate_extrusion.rs:659–678,716–759` | Captured graph stores bounds/evidence and four-port nodes. Restoration inserts first and owns replay of its saved opposite count; full initial/inherited/bulk pair coverage and completion are not proved here. |
| Complete Call deficit | `crates/yu-solver/src/candidate_call.rs:85–124` | Actual pending supplier enum includes original registration, introductions/exposure, Gen-Call-0, whole argument reification and complete result/future interfaces. Treat these as open compiler suppliers, not satisfied by scalar endpoints. |

The minimal implementation handoff is therefore a single owned Value
description and reference traversal at generation/extrusion/freshening, an
actual parent record at copy creation, justified equality qualification and
scope transport at SCC processing, and real activation of all merged/current/
future obligations. Source owners must retain facts they actually know; none
of these handoff conditions is permission to add a second solver or recover
ownership from subtype success.

## Effects, Call and outstanding extensions

The selected concrete policy remains composed-polarity local subtraction in
negative positions and allowance in positive positions. A variable is omitted
only from the concrete atom set; its later concrete lowers still encounter the
retained checks. This requires actual annotation-owner construction and exact
scope/attachment transport. Equality of rows does not confer annotation-local
authority at another boundary. Existing reviewed conditional hygiene results
retain their hypotheses; this note does not reprove or extend them.

Full Call must carry the original correlated registration, complete demand,
argument reification, provider/receiver incidence, immediate and complete result
positions and latent future interface. The pure App generation rule and
four-port signature are necessary structural ingredients, not a proof of
these complete obligations. Exact constructor/consumer and scope evidence is
still required at those owners. No full-Call registry is introduced as a
prerequisite for every elementary bound insertion.

The unresolved critical path is:

1. Establish the actual Value-description/reference owner law, including a
   qualifying parent/copy route compatible with levels, or prove which level
   mutation enables qualification and why scoping remains sound.
2. Prove the selected equality's source-typing justification and its effect on
   generalized binders and required principality; activate and preserve all
   transported obligations with exact lineage.
3. Extend native constraining/coalescing soundness, termination and required
   completeness to the authentic Effect and complete Call constructors.
4. Establish the redesign's source/operational correspondence and publication
   invariant at every relevant constructor and consumer.

No plan change or obligation classification resolves any of these items.

## Bounded method, stopping audit and verification

Method: direct inspection of the reference operations and induction on native
structural construction, event order for bound replay, and a monotone-level
path argument. Falsifiers: a legal stored bound above its owner; a later
opposite insertion that creates no replay obligation; a freshening memo that
splits one row into independently chosen images; or a source-qualified
parent/copy SCC with unequal levels under a proved nonincreasing reference
law. The last would contradict that law, not automatically the approved rule.

One bounded constructive pass produced the level/SCC obstruction; a separate
two-row valuation falsifies the generic SCC-to-equality shortcut. No third
equivalent proof attempt was made. The economy audit classifies actual
parent retention/reference incidence as D when already known at constructors;
selected equality's soundness/scoping as A; qualifying recursion and retained
principal generalization as B. The graph shortcut's falsifier is not a reason
to demote A/B to optional C research. Owner retention can remove reconstruction
debt, but cannot manufacture the missing equality theorem.

Commands: `cat`/`sed`/`rg` for the named rules, authority and owning source;
`pdftotext -layout ... -` piped to section reads; read-only `git rev-parse`,
`git status`, `git branch --show-current`, and dependency-scoped
`git diff --name-only <baseline> -- <inputs>`; `sha256sum` for frozen inputs.
Reference HEAD matched its pin and its working tree was clean. The Yulang
branch/HEAD matched the packet at inspection; direct inputs showed no diff
against the pinned baseline. Unrelated concurrent notes were not consumed.
No compiler, Cargo, Oracle, tests, search enumeration, benchmark or executable
model ran. Independent review is pending. No measurement samples or heavyweight
processes; at most three concurrent lightweight read commands. Tool-reported
individual shell calls completed in under one second; whole-task CPU/RAM and
wall-time were not instrumented. No subagents were launched.

Requested routing: ordinary proof leaf, Sol/high. `.codex/config.toml` declares
`gpt-6.1-sol/high` subagent defaults and registers `prover`; the prover role
omits model/effort pins. The live tool schema exposes `prover`, but no child
launch occurred in this leaf. Effective runtime model/effort metadata was not
provided to the leaf and is unknown. No Astra execution or hot reload is
claimed. The primary's dispatch record is the authority for requested settings.

### Bounded repair of Lemma 1

A fresh repair owner applied the primary's accepted independent MAJOR finding:
the former later-insertion argument omitted populated initial stores and
non-replaying extrusion/freshening writes. The repair adds initial coverage,
bulk coverage preservation and exact source accounting to the local
pair-coverage lemma. It preserves the original all-source obligation and
leaves the corresponding source gate OPEN; no pair-completion claim is added.
Lemmas 2–5 and semantic authority are unchanged. This is a producer repair
for independent delta review, not self-certification or a theorem promotion.
Repair checks are static reference/Rust citation and behavior crosswalks,
dependency hashes and artifact-section integrity; no code/tests/Git/shared
records or additional workers are involved. Requested normal Sol/high;
observed effective runtime model/effort unknown. No heavyweight process or
measurement sample; CPU/RSS and exact wall time were not measured.

## Dependency snapshot and commit packet

Frozen content SHA-256:

```text
reference Typer.scala f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9
reference paper      5ab2bd4122caee17c20134e4cbe8dc8a4848c142de1e576b5fd178aed8787698
top-level principles edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389
parent-copy decision 2f08967e8f0477a1dacda62a211c620cd9cc3b80d476412b4c1e3d60506040c0
annotation hygiene   503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a
residual lineage     d5c46b74d678028046bdfa0f7fd2b71bb2abfb112987000fe43e0fa5875d5d98
candidate_intrusion  aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0
candidate_extrusion  fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0
candidate_source     13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49
candidate_scheme     9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1
candidate_call       79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35
shadow_apply         230ed70cc8575016967cdf16c6c814544b25e45b0fc687d6c89f0d38e8fb5cd6
```

Exact changed path: `notes/theory/2026-10-11-simple-sub-rebuilt-core-proof.md`.
Baseline SHA: `d8c097e1f810fb26a8cf1936aa97059f6948bf32`.
Changed dependency hashes: none at inspection; recheck these dependencies
before integration if the primary's redesign changes them.
Claim/review status: unreviewed local mathematical derivations and a bounded
source inventory; original theorem and production bridge open.
Checks already run: source/pin/dependency inspection above; no executable
semantic checks. Producer writes stop at handoff; primary owns review and Git.
Proposed checkpoint message: `research: derive native Simple-sub core and isolate intrusion bridge`.
Shared-record deltas left to primary/curator: record Lemmas 1–5 as unreviewed
local results; keep the parent proof gate OPEN with the Value-owner/level route
and equality/generalization premises named; do not promote source soundness,
principality, complete Call or hygiene.
One next action: have the actual Value constructor owner supply the qualifying
parent/copy reference and level-transition trace, then independently review the
frozen derivation against that trace.
