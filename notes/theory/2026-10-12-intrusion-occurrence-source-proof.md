# Native nested-call extrusion: source location and missing Value certificate

Status: unreviewed research derivation; no theorem-status promotion
Baseline: `e5e7b5878ced01b8cc4682492b6187c3907fd014`
Branch: `research/simple-sub-intrusion`
Original Simple-sub: `9bae772624c23b52a93c1b226157e16898b4d9db`
Exclusive output: this file only

The native constructors identify one extrusion invocation at `f y`, inside
the active initializer of `g`, against the outer recursive `f` placeholder.
They produce exactly `(C,B,+,1)` and `(D,R,-,1)` in that invocation. They do
**not** output an origin Value `G`, a receiving Value `F`, or an event joining
those Values to these pairs. The user's selected rule fixes `G/F` for this
example; it is compatible with the derived source location, but is an added
normative association, not an existing Scala constructor output. The missing
bridge starts at App-demand generation and its handoff to extrusion.

## 1. Frozen question, scope and authority

Fix the original AST, with the indicated distinct binding occurrences:

```text
Let(true, f,
  Lam(x,
    Let(true, g, Lam(y, App(Var(f), Var(y))),
                 App(Var(g), Var(x)))),
  Var(f))
```

Inference starts at level 0 with the original builtin context. None of its
builtin Names occurs in this AST. Assume ordinary finite allocation and the
actual source evaluation order of `Typer.scala`; allocation UIDs are irrelevant
and may be renamed injectively. All source binding scopes remain original:
outer `f` scopes its initializer and final body; `x` scopes the outer Lambda
body; inner `g` scopes its initializer and inner Let body; `y` scopes only the
inner Lambda body. There is no shadowing between these four binders.

Let `F` and `G` denote the semantic definition-root Values selected for the
two binding occurrences by the approved successor rule. They are distinct
from type coordinates and from Lambda/Apply result Values. Let `o,h,A,B,R`
denote respectively the native recursive placeholders for `f,g`, the formal
types for `x,y`, and the result type of the inner App. Freeze `C,D` as the
fresh type copies created by the first crossing, rather than choosing other
rows with similar shape or SCC membership.

**Original correspondence claim under investigation.** For every native run
of this fixed AST from the stated initial conditions, the actual extrusion
invocation creating `C,D` identifies its semantic origin as `G` and receiving
Value as `F`, and links those endpoints to both actual signed pairs. The
quantifier is over runs/UID renamings of this AST, not all recursive programs,
all solver assignments, or arbitrary possible occurrence associations.

**Established local claim proposed for independent review.** Every such run
reaches one invocation
`extrude(Function(B,R),false)(1,emptyPolarMemo)` from `App(Var(f),Var(y))`
while typing the active `g` initializer. Its lower operand is the exact `o`
introduced for the outer recursive `f`. Its two fresh-variable memo entries
are `(B,true)->C` and `(R,false)->D`. This is a direct bounded native
construction derivation. It does not contain the semantic Value endpoint
conclusion of the investigated claim.

Authority is the integrated receipt
`questions/2026-10-12-type-value-occurrence-association/receipt.md`, consumed
through its **Outcome and reason**, and
`notes/design/2026-10-12-intrusion-value-type-association.md`, especially
**Approved extrusion-event qualification**, **Implementation and proof
boundary**, and **Earlier source-construction discriminator**. The displayed
example's normative endpoints are already selected as `G/F`; this note neither
reopens that decision nor treats it as proof of existing constructors.
The graph and operation remain those of
`2026-10-10-parent-copy-scc-intrusion.md`, **Selected operation and compiler
responsibility** and **Value-reference SCC clarification**, including
**Definition-root Value ownership**. Top-level inference principles §§1–3
govern the direct native method; abnormal-path principles are not implicated
by this successful finite trace.

Exclusions: no new ownership convention, permanent type-ID owner, graph edge,
SCC schedule, equality transport, source restriction, or semantic adoption.
This does not prove soundness, required principality, normal progress of the
combined algorithm, complete Yulang Call, effects, or F5 cutover. It does not
claim that current Yulang syntax admits the exact displayed spelling.

## 2. Constructor trace through the crossing

Exact original owners are
`/home/momota1029/rust/simple-sub-reference/shared/src/main/scala/simplesub/`:
`syntax.scala:6–14` and `Typer.scala:48–83,88–159,163–233`.

| Constructor/site | Current level and environment consequence |
| --- | --- |
| Outer `Let(true,f,...)` | `typeLetRhs` at boundary 0 creates fresh `o` at 1; RHS context adds `f->o`. |
| Outer `Lam(x,...)` | At 1 creates fresh `A`; body context adds `x->A`, still at 1. |
| Inner `Let(true,g,...)` | `typeLetRhs` at boundary 1 creates fresh `h` at 2; RHS context adds `g->h` while retaining `f->o,x->A`. |
| Inner `Lam(y,...)` | At 2 creates fresh `B`; body context adds `y->B`, still at 2. |
| Inner `Var(f)` | At 2 resolves the unique outer entry `f->o`. `SimpleType.instantiate:207` returns the same `o` at level 1. |
| Inner `Var(y)` | At 2 resolves the formal entry `y->B` and returns the same `B` at level 2. |
| Inner `App(f,y)` | At 2 forces its lazy fresh result `R` at 2 and calls `constrain(o,Function(B,R))`. |

The stack at this call is, from outer to inner:

```text
typeTerm(Let f, level 0)
  typeLetRhs(true,f, boundary 0)
    typeTerm(Lam x, level 1)
      typeTerm(Let g, level 1)
        typeLetRhs(true,g, boundary 1)
          typeTerm(Lam y, level 2)
            typeTerm(App(f,y), level 2)
              constrain(o, Function(B,R))
```

`h` has not been constrained yet. Neither Lambda's Function result has been
returned yet. Thus the demand `Function(B,R)` is constructed by **App**, before
the inner Lambda subsequently constructs its own `Function(B,R)`. Matching
ports, or later structural equality of those two Function descriptions, does
not itself identify the demand's semantic origin with a definition Value.

At this cut, `o,h,A,B,R` have empty lower/upper lists. `Function(B,R).level=2`
by `:209–210`. The left-variable direct-insertion guard at `:115` fails because
2>1; the right-variable guard does not apply to a Function RHS. `:121–123`
therefore calls negative extrusion with target `o.level=1` and a new empty
polar map. The constraint memo contains the initial `(o,Function(B,R))` but
is a separate object from the extrusion map.

The Function extrusion at `:144` evaluates its argument first, reverses its
polarity, and leaves result polarity unchanged:

| Visit | Memo key and action | Exact stored bounds immediately afterward |
| --- | --- | --- |
| `extrude(B,true)` | Fresh `C` at 1; memo `(B,true)->C` before bound traversal | `U(B)=[C]`, `L(C)=[]` |
| `extrude(R,false)` | Fresh `D` at 1; memo `(R,false)->D` before bound traversal | `L(R)=[D]`, `U(D)=[]` |

The selected bound lists are empty: `L(B)=[]` and `U(R)=[]`. Consequently
there are exactly two allocations in this invocation. `B` and `R` are distinct
fresh variables; polar memo identity cannot conflate them. Both visits share
the same operation-local map. The returned type is `Function(C,D)`; recursive
`constrain(o,Function(C,D))` satisfies `:115` and stores
`U(o)=[Function(C,D)]`. `L(o)` is still empty, so its opposite-bound replay
performs no further call at this point.

This proves unique **dynamic invocation** membership of the two pairs. It
does not prove retention: Scala stores only the returned Function and changed
bounds. The polar map is local, and no parent/event record is emitted.

## 3. Remaining binders, Names, App and publication

The inner Lambda returns `Function(B,R)` at level 2. Inner recursive completion
checks `Function(B,R)<:h`: `:118–120` stores that Function in `L(h)`, with
empty `U(h)`. `g` is published as `PolymorphicType(1,h)` at `:55`; it is
**not** published directly with the Function as scheme body in this recursive
AST. This difference from a nonrecursive `g` does not change the first event.

The inner Let body runs at level 1 with the published scheme replacing `g->h`:

1. `Var(g)` invokes `freshenAbove(1,h)` with one new unpolarized memo. The
   memo contains `h->h1`, `B->B1`, `R->R1`, all fresh at 1. It produces
   `L(h1)=[Function(B1,R1)]`, `U(B1)=[C]`, `L(R1)=[D]`.
   `C,D` are reused because their levels equal the boundary. This freshening
   is not extrusion and has no polar parent pair.
2. `Var(x)` returns the unchanged formal `A` at level 1. `App(g,x)` creates
   result `S` at 1 and checks `h1<:Function(A,S)`. Direct insertion on `h1`
   replays its lower Function, producing `A<:B1` and `R1<:S`.
   Exact variable-side effects are `B1` appended to `U(A)`, `S` to `U(R1)`,
   and replay of `L(R1)=[D]` appends `S` to `U(D)`. These comparisons do not
   symmetrically populate the right variable's lower list: the left-variable
   clause has priority. No new extrusion occurs.
3. Outer Lambda returns `Function(A,S)` at 1. Outer recursive completion
   stores it in `L(o)` and replays `U(o)=[Function(C,D)]`, generating
   `C<:A` and `S<:D`. They append `A` to `U(C)` and `D` to `U(S)`.
   Their left lower lists are empty, so there are no further replay calls.
   The resulting upper-bound cycles include `A->B1->C->A` and `D->S->D`;
   these are type-bound paths, not Value-reference edges.
4. `f` publishes as `PolymorphicType(0,o)`. Final `Var(f)` at 0 opens a
   different unpolarized freshening memo. Reachable variables are
   `o,A,S,B1,C,D`, copied coherently to level 0 while preserving those cycles.
   Original `B,R,h` and use-only `h1,R1` are not reached from `o` through
   these stored bounds. No final App or checking consumer occurs.

Thus all relevant Name/binder/App levels are accounted for, and the displayed
native inference encounters exactly one extrusion invocation. Publication and
freshening do not reconstruct the erased Value event. This derivation is hand
evaluation of the actual rules, not an executed Scala inference test.

## 4. What the finite source bridge establishes

The source trace supplies this exact certificate at the construction site:

```text
site = the inner App(Var(f),Var(y)) occurrence
active innermost declaration initializer = the g binding occurrence
resolved callee binding = the outer f binding occurrence
resolved callee type = its monomorphic recursive placeholder o
actual operation = negative extrusion of App demand Function(B,R) to 1
actual produced pairs = {(C,B,+,1), (D,R,-,1)}
```

Uniqueness follows from the frozen AST, lexical contexts, monomorphic lookup
and one common extrusion memo. It does not rely on source spelling: alpha
renaming with unchanged resolution gives the same binding-occurrence witness.
It also does not assign all suboccurrences of a Function to an enclosing Value.

The approved **definition-root** rule gives source reference edges `F->G`
from `g x` in `f`'s own body and `G->F` from `f y` in `g`'s initializer.
Accordingly `F,G` share the approved Value-reference SCC. These are normative
source incidences, not emitted Scala graph edges or consequences of bounds.
The approved **example association** identifies the certificate's selected
origin/receiver as `G/F`. Given that association and an operational event
record retaining the common pair set, qualification follows immediately.

The latter premise is not an output of the native judgment. Its interfaces
are `Ctx = Map[String,TypeScheme]`, `typeTerm: ... -> SimpleType`,
`constrain(SimpleType,SimpleType):Unit`, and
`extrude(SimpleType,Boolean)(Int,Map[(Variable,Boolean),Variable]):SimpleType`.
They carry no definition-root Value, receiving Value or occurrence identity.
The recursive stack retains a `g` binding *site*, while lookup retains `o`
as a *type*. Neither is the semantic Value endpoint record by itself.

This is an underdetermination of the unaugmented operational output. Erasing
any annotations of origin/receiver leaves the same native trace; the trace
alone cannot distinguish annotation `origin=G` from annotation using the inner
Apply Value. The latter is excluded by the already selected example rule and
is not offered as a lawful alternative or as a counterexample to that rule.
No original constructor emits a conflicting endpoint: it emits no endpoint.
Hence the finite binding/site correspondence is established by derivation,
while the claimed existing endpoint output is unsupported. There is no
refutation of the selected extension and no general impossibility result.

## 5. Current Y3 construction and consumption seam

At the pinned Y3 baseline, the relevant checked owners are:

| Owner | Actual input/output and bridge limitation |
| --- | --- |
| `candidate_source.rs:250–309,369–410` | Local initializers raise level; active recursive locals use their existing endpoint; Apply records operands, result and source expression. `ApplySourceInput.owner` is `source.definition_root()`, including nested local initializers. It is not a retained nested-origin Value certificate. |
| `candidate_call.rs:30–58` | Source input retains source indexes, levels, checking occurrence, operand type endpoints, effects and native interface. It has no extrusion-event origin/receiver Values or pair-set identity. Its own module describes inputs as pending complete Call construction, not certificates. |
| `shadow_apply.rs:1312–1404` | Validates the actual source recipe, constructs the four-port negative Function demand, records `NativeInterface`, then enters live value constraint processing. This is useful actual demand provenance; it does not make body result equal complete invocation or supply semantic event endpoints. |
| `lib.rs:12411–12439` | Structural/row constraint processing passes only an endpoint, polarity and row level to `candidate_extrude`; on the analogue of the native crossing it passes the upper demand negatively. The call supplies neither semantic endpoint nor a common extrusion-event identity. |
| `candidate_extrusion.rs:4–5,21–35,90–123` | Local memo key is `(ExtrusionEndpoint,Polarity,target)`; a fresh copy is memoized and its actual parent retained before selected-bound traversal. `candidate_extrude` accepts no source event context. |
| `candidate_intrusion.rs:23–28,171–219,358–388,474–505` | `Parent` retains copy/parent type rows, polarity and target. Settlement compares SCC IDs of those type endpoints and merges selected rows. It consumes no `G/F` Value event and therefore does not implement the corrected event qualification. |

This is a bounded interface/constructor/consumer audit, not proof that the
original AST has a complete current Y3 realization, and not an Oracle
production-constructor audit. More pending constraints, source positions or
parent rows cannot alone supply the missing Value association or its activation.

## 6. First missing premise and obligation-economy stop

The precise missing operational premise is:

> At the actual App-demand/crossing construction, retain a semantic event
> identifying the selected origin `G` and receiving `F`, and ensure both
> copies created by this same polar traversal attach to that event. Preserve
> that event-to-pair relation until the Value-SCC consumer uses it.

For this fixed AST the lexical/resolution witness above is independently
available; it is the smallest concrete input to such retention. Passing the
whole source descriptor, assigning `G` to every type port, or recovering owners
later by type-ID lookup is neither necessary nor justified by this result.
For other sources, replay, sharing and generalized uses, the correct event
construction/transport still needs its own proof. No general enclosing-RHS or
callee-root rule is adopted here merely because it would fit this example.

The earlier pair derivation and this direct constructor analysis leave the
same missing event certificate. The audit required by
`compiler-engineering.md`, **Natural compiler behavior and proof-obligation
economy**, and `research-lab.md`, **Evidence quality and stopping unproductive
loops**, now favors examining retention at the source owner rather than a
third equivalent native derivation. The parent qualification/correctness gate
remains A/B and OPEN. Recovering the already known source site and resolved
binder after their context was erased is D reconstruction debt within that
required gate; this classification does not retire or weaken it.

One next action: the primary assigns the exact App-to-extrusion event
construction/consumer bridge using the finite lexical/resolution witness,
with fresh independent review. Equality preservation remains a separate open
theorem even after this bridge is implemented or proved.

## 7. Checks, resource use, runtime and commit packet

Checks: bounded `cat`, `rg`, `nl`/`sed` source and governing-rule reads; direct
hand derivation; SHA-256 dependency snapshots; read-only `git show` byte
comparison against the pinned Y3/reference commits. All ten direct Y3/authority
dependencies below match the pinned baseline; both reference files match their
pin. One `rg` included a nonexistent `candidate_propagation.rs` and exited 2;
the actual propagation owner was subsequently located at `lib.rs:12411–12439`.
Some initial combined captures truncated; decisive rule/source windows were
reread. No build, test, interpreter, model checker, probe, exhaustive search,
performance measurement, Git mutation or child dispatch occurred. One bounded
reasoning lane; zero heavy processes and zero inference/performance samples.
CPU/RSS and reasoning wall time were not instrumented.

Requested routing: configured `gpt-6.1-sol/high` as supplied by the primary.
Observed model/effort runtime metadata: unknown. Inspected config defaults and
the unpinned prover role are not runtime confirmation. No Astra escalation,
hot reload, independent review, semantic adoption or parent closure is claimed.
The `yulang-proofs` skill was read and applied subject to the explicit leaf
packet: no delegation and no writes beyond this lease.

Direct dependency SHA-256 snapshot:

```text
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389 notes/design/2026-10-11-yulang-inference-top-level-principles.md
0063b88d17104f85182439d80360e42f8f99a5af4793eab70640a66f955ede25 notes/design/2026-10-12-intrusion-value-type-association.md
6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b notes/design/2026-10-10-parent-copy-scc-intrusion.md
3508c7451a4303908107b1a4d6d78109022c7011beeb2222c643292f7628c1e4 questions/2026-10-12-type-value-occurrence-association/receipt.md
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49 crates/yu-solver/src/candidate_source.rs
79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35 crates/yu-solver/src/candidate_call.rs
cbd2e0c49a3f1fbe3c5fc78a06d469faedf4aa261525b24a0c9584e9956c2411 crates/yu-solver/src/shadow_apply.rs
fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0 crates/yu-solver/src/candidate_extrusion.rs
aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0 crates/yu-solver/src/candidate_intrusion.rs
c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94 crates/yu-solver/src/lib.rs
f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9 reference/shared/src/main/scala/simplesub/Typer.scala
f26f19f6905d42c247198c45da9b1675b22619dd59749047023efe5f7ee3c60f reference/shared/src/main/scala/simplesub/syntax.scala
```

Commit packet:

- Exact lease: `notes/theory/2026-10-12-intrusion-occurrence-source-proof.md`.
- Baseline: `e5e7b5878ced01b8cc4682492b6187c3907fd014`; original pin as above.
- Changed dependency hashes: none; this producer edited no dependency.
- Claim/review: finite source-location/pair derivation, exact operational
  obstruction; unreviewed research checkpoint. Parent A/B theorem remains OPEN.
- Checks already run: source/rule inspection, hand derivation and pinned-byte
  dependency comparison; final leased-file integrity checks reported at handoff.
- Proposed message: `research: derive nested extrusion source location and isolate Value event bridge`.
- Shared-record delta for primary/curator: record the unique native invocation,
  active `g` initializer and resolved outer `f` witness; distinguish selected
  normative `G/F` from missing emitted event; keep qualification implementation,
  equality preservation and parent proof gates OPEN. No shared record changed.

Writes stop at handoff; the primary owns review, integration and any status change.
