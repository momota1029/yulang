# Nested odd/even: ordinary Simple-sub reasoning before intrusion

Date: 2026-10-12
Status: frozen, unreviewed research checkpoint; conditional derivation and static source crosswalk
Baseline: `e466f629452d1d868f23f70ccd1fe8581c213011`, `research/simple-sub-intrusion`
Exclusive lease: this file; proof leaf, no further delegation
Reference baseline: `9bae772624c23b52a93c1b226157e16898b4d9db`

## 1. Frozen statement and authority

The assigned illustrative source is exactly:

```yulang
my odd n = my even n = if ... odd(n-1); even(n-1)
```

The ellipsis leaves the test, other arm, and primitive declarations unspecified.
The more explicit earlier example has `if n <= 0 { true } else odd(n - 1)`;
it is subject to the same missing admission/elaboration and primitive laws.
Neither spelling is replaced by a Call-only program here.

Freeze distinct binders `O` (outer recursive odd), `E` (nested local even),
`a` (outer n), and `b` (inner n). E's initializer sees O and b; b shadows a
there. The final outer expression sees published E and a. O remains active
and monomorphic while E's initializer and the outer final expression are
inferred. E is not a same-level mutually recursive sibling of O.

For every faithfully resolved/elaborated instance with these binders, and
every successful finite ordinary Simple-sub history implementing that instance,
derive the forced recursive-root, level, Call-demand, extrusion, and local
generalization judgments from the native operations. Retain the actual test,
arithmetic, branch clauses, providers, effects, witnesses, and their original
scopes as premises when their laws are absent. Determine the precise boundary
before any claim about selected intrusion needs additional evidence.

The original parent claim still ranges over supported source programs and
lawful histories, with all original lexical/type/event scopes, and actual
retained distinct Value extrusion pairs `(copy,parent)`. Its qualification is
two-way reachability in the selected Value-reference graph **before** the
equality. Its conclusion includes preservation of joint source typing, complete
Call, effect/attachment/residual evidence, soundness, required principality,
and actual compiler construction/consumption. This local result does not
discharge that universal claim or narrow its source domain.

Authority used:

- [Top-level inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md),
  §§1–5 and Authority and integration: ordinary generation/propagation, levels,
  extrusion, intrusion and generalization; no eager per-constraint typing search.
- [Source Generalize](../design/2026-10-08-source-generalize-definition.md),
  §§2–5, selecting construction §§3–5 in the
  [source proof](2026-10-08-source-generalize-definition-and-proof.md).
- [Parent-copy decision](../design/2026-10-10-parent-copy-scc-intrusion.md),
  Selected operation, Value-reference SCC clarification, Apply-result
  source-fragment ownership, Nested Apply membership, Definition-root Value
  ownership, and Retained boundary.
- [Local self-recursive binding](../design/2026-10-10-local-self-recursive-binding.md),
  Selected source behavior and Proposed source-to-solver seam: a helper's
  reference to an active enclosing binder uses its existing monomorphic root.
- Parreaux, local `../simple-sub-reference-paper.pdf`, §3.5 and Figs.6–9;
  §5/§5.3 for the exact limitation of the imported soundness/principality sketches.
  Relative to this repository the actual paper/reference locators are
  `/home/momota1029/rust/simple-sub-reference-paper.pdf` and
  `/home/momota1029/rust/simple-sub-reference`, not `../rust/...`.

Claim class: **conditional derivation** of native rule instances and a
**bounded static characterization** of the Rust owners. No established new
soundness/principality theorem, proposed semantic restriction, executable probe,
or independent certification is reported. Falsifier: an actual cited constructor
violating the displayed rule/level/sharing consequence under its hypotheses,
or a faithful exact-source derivation supplying the missing local laws.

## 2. Original source ownership closes independently of typing

The approved definition-root rule gives `E → O` from E's own initializer and
`O → E` from the outer body's final use of E. The nested initializer is owned
by E, not forwarded into O merely because it is syntactically inside O.
Thus O and E belong to one nontrivial original-root SCC across lexical levels.
This is a direct application of the selected semantic rule under the fixed
Name resolutions, not an observed emitted solver graph.

The separate Apply rule gives `R → O` for the inner Call result and `S → E`
for the outer Call result, since each callee is an actual resolved Name in
that Apply fragment. Additional argument/test incidences require their actual
source trees and applicable membership boundaries; no complete adjacency list
for the unspecified ellipsis is claimed. Roots O/E, Apply results R/S,
Lambda/Block rows, parameter rows, occurrence facades, and use copies remain
distinct constructors. No subtype comparison creates any of these edges.

The O/E SCC neither identifies O with E nor identifies R with E. Selected
intrusion only equates an actual retained extrusion copy with its recorded
parent when that pair qualifies. The approved root SCC does not name such
a pair. Numerical levels do not filter the selected reference edges.

## 3. Ordinary recursive introduction and the level boundary

Work first in the original reference algorithm, separately from full Yulang
Call semantics. `Typer.scala:48–55` allocates an outer recursive placeholder
`o` at level 1 when the publication boundary is 0; it infers the RHS under
`odd ↦ o` at level 1 and later constrains the RHS type below o. Lambda
introduction allocates `A` for a at level 1 (`:64–67`).

The nested let RHS is inferred at level 2, with a fresh formal `B` for b
at level 2 (`:48–55,:81–83`). Its recursive reference to odd returns exactly
o: `Var` calls `instantiate`, and a monomorphic `SimpleType` returns itself
(`:62–63,:205–207`). Enclosing recursion is not instantiated as a published
scheme because a lexical helper is being inferred.

Whether the original-grammar local let uses a recursive placeholder for even
or a nonrecursive RHS makes no difference to this enclosing-odd lookup. In the
recursive variant it additionally allocates `e` at level 2 and checks the
formed inner Lambda below e; in the nonrecursive variant it returns that
Lambda type directly. The selected Yulang local function rule exposes an
open initializer root. This example has no self-use of even in its initializer,
so no proof here identifies the optional Scala placeholder e with a particular
Yulang Lambda/root row.

Let `Q_I` be the genuinely supplied inference of the inner argument `b-1`,
with result type T, at level 2. Let `Q_B` be the genuine branch/test/other-arm
rule, retaining the recursive Call and yielding body result J at level 2.
These are named *missing local derivations*, not new opaque source primitives
or assertions that successful generalization exists. Their actual clause
programs must replace these labels before a full source proof can close.
The supplied reference has no minus/comparison builtin (`Typer.scala:23–33`)
and no Yulang Branch term (`syntax.scala:7–14`); no `int → bool` signature or
branch join is selected by this note.

The original local scheme boundary is exactly **1**, after E's initializer,
not 2 and not the boundary of O's eventual publication. The outer final Call
is inferred at level 1. O's recursive closure check and boundary-0 publication
follow after that expression. These levels follow native let/Lambda rules,
not a Value-reference SCC rank.

## 4. A forced Call/extrusion judgment with arbitrary existing bounds

Assume Q_I has completed successfully with `level(T) ≤ 2`, and the current
store satisfies the reference level invariant: every stored bound of variable
v has level at most `level(v)`. No emptiness assumption is made for o's bounds
or T's reachable bounds. The inner App then allocates a fresh result R at
level 2 and generates:

```text
constrain(o, Function(T,R)).
```

This follows `Typer.scala:68–72`: the lazy result variable is first demanded
after the callee and argument types have been obtained. R is distinct from
their existing variable graphs and starts with both bound lists empty.
The demand has level 2 because of R, even if T is ground.

1. The left-variable direct-insertion guard fails since `2 > level(o)=1`.
   The negative extrusion branch runs with target 1 (`:115–126`).
2. Function extrusion flips the argument polarity and preserves result
   polarity (`:134–144`). Write `T_plus = extrude(T,+,1)` and
   `D = extrude(R,-,1)` in the **same polar memo**.
3. D is a fresh level-1 variable; the memo records `(R,-) ↦ D`,
   `L(R)` acquires D, and `U(D)` copies R's initially empty upper list
   (`:146–156`). Therefore the result copy is forced independently of
   Q_I's concrete arithmetic typing. It is not a copy of o or E.
4. If T is a level-2 variable, its positive extrusion allocates a distinct
   C at level 1, appends C to `U(T)`, and fills `L(C)` from the positively
   extruded previous lower bounds of T. If `level(T) ≤ 1`, T is unchanged.
   General structural T can cause several polar copies; no universal
   argument-copy count of one is asserted.
5. The rewritten demand `Function(T_plus,D)` has level at most 1. It is
   appended to `U(o)` and **each existing lower of o is replayed against it**
   (`:115–117`). If such a lower is `Function(P,Q)`, the actual child calls
   are `T_plus <: P` and `Q <: D` (`:106–108`). They can add bounds to D
   or fail. Their completion is a premise for a successful history; stored
   demand alone is not proof of their successful activation/discharge.

At the immediate D-construction cut its selected copied list is empty; after
replay it need not be. Subsequent branch consumption may constrain R and
activate its D lower. No branch consumer is invented here. The result-copy
claim is about the actual reference App/extrusion instance under Q_I, not
an executed exact Yulang source history.

The earlier [finite Call-only derivation](2026-10-12-odd-even-parent-copy-scc-derivation.md)
§3 gives an entire empty-store example. The new conclusion here removes its
empty-existing-bound dependence and does not delete the source arithmetic
or conditional to claim exact-program typing.

## 5. What ordinary levels and generalization do establish

The reference level invariant is preserved by these local operations:

- Direct bound insertion is guarded by `bound.level ≤ owner.level`; replay
  creates further ordinary constrain calls under their own guards.
- Extrusion stops at acceptable levels. At a wrong-level variable it inserts
  a target-level copy on the original's opposite side and recursively copies
  only the selected bound side to the new row. Registering the polar memo
  before descending handles cycles without choosing independent copies.
  Every completed copied bound has level at most the target. Function/Record
  reconstruction takes the maximum of acceptable child levels.
- At an E use at level 1, `freshenAbove(1,tE)` retains every variable of level
  at most 1 and maps each reachable higher-level variable to one fresh
  level-1 variable. The single memo is installed before copying **both** bound
  lists (`Typer.scala:166–188,:201–202`). Repeated occurrences and recursive
  bound references use that same map; fixed o/C/D anchors stay shared.

The cyclic cases above are finite graph arguments: a memoized variable is
visited once per applicable key and subsequent occurrences reuse its output;
structural reconstruction does not introduce higher-level leaves. They prove
the stated numerical level and sharing properties for completed operations.
They are not a proof that extrusion preserves all Yulang semantic solutions.

In particular, any bound path starting at o at level 1 can only visit variables
at levels at most 1. It cannot reach B/R at level 2 through bound payloads.
Extrusion retained lower-level approximations precisely where those higher
variables would escape. Hence E can generalize its reachable level-2 variables
at boundary 1 while keeping the enclosing monomorphic o and its escaping
approximations shared. A source Value-reference edge `O → E` does not contradict
this **different** bound invariant. This argument is not a level-based
acyclicity argument for the approved Value graph.

After genuine Q_B yields J, the inner Lambda type is `Function(B,J)`.
The appropriate inner RHS/root becomes `PolymorphicType(1,tE)`. The later Name
even instantiates that scheme at level 1. After the genuine outer argument
derivation Q_O yields U, its App allocates S at level 1 and generates
`tE_instance <: Function(U,S)`. Actual Function comparison/replay uses the
ordinary algorithm. The outer RHS then has `Function(A,S)`; recursive-let
completion checks it below o and replays o's upper demands before publishing
`PolymorphicType(0,o)`. This is a conditional **rule sequence**, not a claimed
successful complete store, final printed scheme, or principal `int → bool`.

These constructors require no intrusion premise. The justified conclusion is
that the ordinary generation, numerical level guard, polar approximation,
monomorphic recursive lookup, and coherent local instantiation steps already
explain this nested shape. Whether the full exact Yulang history succeeds, or
selected intrusion changes a later consumer, is left open. The paper's §5
explicitly restricts its proof sketches to the non-let-polymorphic fragment;
its §5.3 theorems do not certify this let/effect/complete-Call extension.

## 6. Exact source Generalize and the Rust bridge

The semantic generalization boundary is also E's actual publication, but it
is not defined by the numerical level test alone. Source Generalize §§2–3,
and its selected construction §§3.1, 3.3, 4, 5.1–5.2, require:

```text
Generalize_source(S,b_E)
  = ScopedClosure(p_E,C_E,T_source,anchors_E,templates_E,N_E,FinalRoot_E).
```

The source Bind keeps the actual initializer Return/rebind/current-world tuple;
Lambda retains capture, receipt, body consumer and invocation return; Call
keeps callee computation, inert whole argument, receiver, entry and complete
consumer/result. Branch retains original guards and ordered alternatives.
Build conjoins all these actual local clauses under their original binders.
Neither a two-port Function demand nor its successful replay replaces them.

`C_E` must come from the actual source recursive/definition registration, not
be guessed as `{O,E}` from Value SCC membership. For an actually registered
same-component live peer, its description edge is Internal and retains the
whole joint relation; fixing raw provider identity does not fix all inferred
descriptions. An actual established external monomorphic contract instead
fixes every free descriptive coordinate it requires. Thus the physical capture
of odd does not by itself decide template eligibility. The caller cannot choose
Shared witnesses independently or turn current recursive references into
fresh incoming instances. Numeric boundary-1 sharing of o is a reference
algorithm fact; correspondence to this full source package is still required.

The following are actual Rust owners, characterized only on an admitted carrier:

| Judgment | Owning constructor/consumer |
| --- | --- |
| Separate local identity and inner formal | `yu-hir/src/module/local_source.rs:338–372,740–769`: temporary self binder, parameter shadowing, restore then publish; Name lookup at `:636–657` uses lexical binding before module namespace. |
| Outer 1 / nested 2 / final use 1 | `yu-solver/src/candidate_source.rs:254–307`: Lambda preserves level; Block initializer raises it; Install records the enclosing boundary. |
| Active enclosing module root and distinct occurrence facade | `candidate_source.rs:375–378,672–677`; `candidate_scheme.rs:869–882,938–944`; `lib.rs:15765–15782`: active internal use routes root O below occurrence U. U is not identified with O. |
| Active local enclosing root, if outer odd itself is local | `candidate_source.rs:381–387`: active initializer emits Link rather than a LocalScheme route. This is the selected local-helper rule's actual owner. |
| Apply endpoints/effects | `candidate_source.rs:394–411`: recipe and source input retain callee, argument, result, callee/argument/application effects and occurrence. |
| Native four-port demand | `shadow_apply.rs:1335–1385`: negative Function contains argument Value/effect, invocation effect and result Value; callee/application effects remain in NativeInterface. |
| Accumulation and actual opposite-side replay | `candidate_extrusion.rs:763–804,808–831`: bound insertion invokes the contextual replay constructor/driver. Completion and each context/effect premise still need actual history evidence. |
| Wrong-level structural extrusion and parent retention | `lib.rs:12412–12454`; `candidate_extrusion.rs:82–163,224–250`: Function flips argument Value/effect polarities, retains invocation/result polarities, and stores typed parent at creation. |
| Later Function consumers | `lib.rs:12493–12536`: four separate argument, argument-effect, invocation-effect and result comparisons; neither effect comparison is erased. |
| Live E installation and later use | `candidate_source.rs:307–328`; `candidate_scheme.rs:1316–1334,1362–1382`: one-shot initializer effect is separate; LocalScheme retains live root/boundary; later use captures the graph and prepares coherent freshening. |
| Outer formed-root link / publication | `candidate_source.rs:479–495`; `candidate_scheme.rs:891–904`: final formed root is checked/linked, then member graphs are captured before visibility. This is not proof of full source ScopedClosure adequacy. |

This source traversal does not show that the exact program reaches these rows.
`LocalSourceForm` has no conditional variant (`local_source.rs:107–137`);
its body constructor requires an OperatorChain (`:251–255`), and the
[exact admission audit](../progress/2026-10-12-odd-even-source-admission-audit.md)
records the missing inline/indented body, infix and conditional steps. No new
admission investigation or execution was substituted for the assigned proof.

Even on an admitted carrier, `CandidateSourceCall` explicitly records that
native demand/scalar provenance is not original typing (`candidate_call.rs:91–130`).
Complete Gen-Call-0 inputs, actual local primitive/Branch clauses and their
checked source/elaboration correspondence remain necessary. This table proves
neither their availability nor complete replay of an unobserved source run.

## 7. Minimum open premises, economy audit, and stop

There are three distinct boundaries, with different owners:

1. **Exact-source inference:** a faithful resolved/elaborated judgment for the
   original body with O/E/a/b, actual minus/test/branch laws and full Call
   clauses. It must preserve the source computation and telescopes; current
   syntax/HIR admission is incomplete. This is an ordinary missing
   constructor/bridge premise, not a new source restriction or an undecided
   choice that copying could resolve. Owner: source admission/elaboration
   and the original local primitive/Call/Branch construction owners.
2. **Source Generalize correspondence:** genuine component/provenance records
   and complete active clause program at E's publication, connected to live
   capture/freshening without changing Shared/Internal/Established/event
   scopes. Source Generalize supplies the definition, not this compiler
   correspondence. Owner: source registration/generalization bridge.
3. **Intrusion qualification and preservation:** after actual retained Value
   parents are known, source incidences must be emitted and their extrusion/
   fresh-use targets transported by the selected copied-row law. That copied
   incidence meaning is pending. `settle_candidate_intrusion`
   (`candidate_intrusion.rs:358–488`) currently builds adjacency from bound
   sides, Function ports and Effect dependencies before comparing parent/copy
   component numbers; this does not supply the missing approved source
   incidence equations. Owner: primary's copied-row decision and subsequent
   construction/consumer bridge, then independent equality proof/review.

The minimum *typing* rule to request now is the first judgment in item 1, not
another SCC transport lemma. Conditional arithmetic inference already implies
the negative result-copy step; no copy-incidence decision is needed for that
ordinary constraint operation. The first judgment required for *intrusion*
remains actual retained pair qualification in the selected graph, not O/E
membership. No such pair is qualified here.

Prior finite skeleton and source-owner/copy routes already leave copied
incidence untouched. This pass does not make a third graph restatement: it
separates the native arbitrary-store Call/level/generalization consequences
that need no such premise. Economy audit: faithful generation and full
Call/generalization/equality are A/B; reconstructing source owners from bounds
is D. Actual constructors should retain incidence known there, but retaining
it cannot decide the pending meaning of a copy. No classifications change
parent status, no theorem is promoted, and no more equivalent proof route is
proposed.

One next action: primary requests the authentic local body/primitive/Branch/
complete-Call formation judgment for this exact binder tree, then plugs its
concrete clauses into §§3–6. Keep the separate copied-row question pending
and the equality, full soundness/principality, effect hygiene, public scheme
and F5 gates OPEN.

## 8. Checks, resource and runtime report

Static `cat`, `rg`, `nl`/`sed`, local PDF-to-text reads and SHA-256 snapshots;
document whitespace/link-target checks only. No tests, builds, executable
probes, Oracle calls, benchmarks, compiler edits, shared-record writes, child
launches, or external communication. At most five lightweight read commands
were concurrent; no heavy process. CPU/RSS and exact reasoning elapsed time
were not measured; the work used one bounded 45-minute proof pass.

Packet deviation: initial branch/reference identity and leased-path status
were read using read-only Git commands (`rev-parse`, `branch --show-current`,
`status --short`) despite the packet's no-Git instruction. There were no Git
mutations. Subsequent checks use filesystem reads/hashes only. No baseline
blob-equality check or independent review is claimed.

Requested route: ordinary `gpt-6.1-sol/high` proof leaf. The actual registered
prover file has no model/effort pins; project defaults are Sol/high. Observed
effective model/effort metadata is unavailable to this leaf: **unknown**.
No Astra assignment, override, or hot reload is claimed.

Direct dependency SHA-256 snapshot:

| Input | SHA-256 |
| --- | --- |
| top-level principles | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| source Generalize design | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| parent-copy decision | `fd07ecc76e9df0b1937f72e74ce4a35b982b51031b04022672228e307d03615c` |
| local self-recursion design | `38d42183fdc4f2c0136112d8b305816241d8f449367b473e4de3a5135dc49895` |
| source Generalize construction | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| previous finite Call derivation | `238e21c0a027aa9f0ca14c563c3fbaa11188ee268e8b819a049f81dd6afd5830` |
| admission audit | `2bb4b6a1389dc054f6a16a1bf566b68cba7648cd31355a4b10c29b1f91d2cb06` |
| HIR local_source.rs | `906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed` |
| candidate_source.rs | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| candidate_scheme.rs | `9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1` |
| candidate_extrusion.rs | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| candidate_intrusion.rs | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| candidate_call.rs | `79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35` |
| shadow_apply.rs | `cbd2e0c49a3f1fbe3c5fc78a06d469faedf4aa261525b24a0c9584e9956c2411` |
| solver lib.rs | `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94` |
| reference Typer.scala | `f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9` |
| reference syntax.scala | `f26f19f6905d42c247198c45da9b1675b22619dd59749047023efe5f7ee3c60f` |
| reference paper | `5ab2bd4122caee17c20134e4cbe8dc8a4848c142de1e576b5fd178aed8787698` |

## Commit packet

- Exact leased/changed path:
  `notes/theory/2026-10-12-cross-level-odd-even-inference-derivation.md`.
- Baseline: `e466f629452d1d868f23f70ccd1fe8581c213011`; reference baseline
  `9bae772624c23b52a93c1b226157e16898b4d9db`.
- Changed dependency hashes: none caused by this leaf; final snapshot recheck
  is reported with the handoff. No comparison against baseline Git blobs is
  asserted; the primary retains that integration check.
- Review status: frozen, unreviewed conditional research checkpoint;
  no theorem/implementation certification or semantic adoption.
- Checks already run: narrow static source/PDF reads, dependency SHA-256
  snapshot/recheck and document whitespace/link-target integrity. No runtime
  verification; primary remains the verification/integration owner.
- Proposed one-line checkpoint:
  `research: separate cross-level Simple-sub derivation from intrusion qualification`.
- Shared-record deltas left for primary/curator: record the arbitrary-store
  forced negative result-copy rule and boundary-1 shared-anchor argument as
  conditional native consequences; preserve exact source formation, full
  Generalize/Call correspondence and copied-row qualification as separate
  OPEN premises. No shared record was edited. Writes stop at submission.
