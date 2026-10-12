# Cross-level odd/even: complete native Simple-sub derivation and source boundary

Date: 2026-10-12
Status: unreviewed research; complete derivation of the specified reference term,
conditional correspondence to the user's original source
Yulang baseline supplied by primary: `e37a937d02c88400a381e08253d0bfd7ac45a473`
Exclusive lease: this file only; leaf, no further delegation
Reference: `/home/momota1029/rust/simple-sub-reference`; file hashes in §8

## 1. Frozen obligation, binders and exclusions

The original witness is preserved:

```yulang
my odd n =
    my even n = if n <= 0 { true } else odd(n - 1)
    even(n - 1)
```

Freeze distinct source definition Values `O` and `E` and distinct formal Values
`a` and `b`. The `n` occurrences in E's initializer resolve to b, including
the condition and subtraction. The final subtraction resolves to a. The inner
`odd` resolves to O; the final `even` resolves to E. O remains a monomorphic
recursive binding during its entire initializer, including E's construction
and the final E use. E has its own nested publication; this is not a group of
same-level sibling definitions. No identifiers or definition roots are merged.

The assigned original claim asks whether this source recurses across the lexical
boundary and has a native typing, together with its actual final scheme and
its extrusion/intrusion bridge. It is not replaced by a Call-only witness.
No hypothesis that a Yulang parser/HIR/solver already admits this text is made.
The original source gate is **OPEN**: §2 states the precise remaining extension
premise. The original soundness, required principality, complete Call, effect
hygiene, intrusion preservation and implementation-correspondence obligations
remain OPEN with their original scopes and binders.

The bounded proposition actually derived is: for the fixed reference term in
§2, in a fresh reference `Typer` under its builtins extended by the independently
grounded integer primitive contracts, `typeLetRhs(true,"odd",rhs)(ctx,0)`
completes, returning the graph scheme in §5; reference compacting and
simplification yield `int -> bool`. Fresh variable identities may be renamed
injectively; there is no quantification over alternative overload selections,
effect extensions, arbitrary stores, or different source elaborations.

Claim class: constructive native operational derivation and direct declarative
typing of one fixed integer instance; **conditional source correspondence**,
not an independently established Yulang theorem or an executable probe.
Falsifier: a cited reference constructor produces a different displayed bound,
level, copy or replay, or a required primitive/source clause fails the exact
extension premise. No independent review or theorem-status promotion occurred.

Governing Yulang decisions: top-level inference principles §§1–5;
parent-copy SCC decision, Value-reference SCC clarification and Definition-root
Value ownership; copied-description incidence Decision; value-to-type
association, Approved extrusion-event qualification; Source Generalize §§2–4.
The original Scala algorithm supplies the native operations, not the Yulang
implementation or these successor semantic definitions.

## 2. Grounded primitive contracts and exact reference term

The reference has no `<=` or `-` builtin. `Typer.scala:23–33` supplies `true:bool`
and the scheme `if:forall j. bool -> j -> j -> j`. `syntax.scala:7–14` has
Var/Lam/App/Let/Lit/Record/Selection, with no infix, Yulang Branch or effect
constructor. `Parser.scala:33–34` translates its own `if ... then ... else ...`
to three Apps of this combinator. Thus unextended native Simple-sub does not
parse or type the exact Yulang spelling; this is a domain mismatch, not a
source-level typing counterexample.

The persistent Oracle checkout `/home/momota1029/rust/yulang2-oracle-capture`
independently grounds an integer instance:

| Owner | Actual contract |
| --- | --- |
| `lib/std/int.yu:6,11` | `le:int -> int -> bool`; `sub:int -> int -> int` |
| `crates/infer/src/builtin_ops.rs`, `resolve_builtin_op` | IntLe has BinaryPredicate(int); IntSub has Binary(int,int). |
| `crates/infer/src/lowering/builtin_op.rs:15–39,170–207,219–269` | Creates a pure reference value, adds both signature bounds, and builds curried function ports with empty return effect. |
| `web/docs/reference/std/num.md`, std::int Quick reference | Independently documented integer comparison and subtraction signatures. |

The actual surface operators have a further owner: `lib/std/core/ops.yu:30,38`
defines `-` as `lambda x. lambda y. x.sub y` and `<=` as
`lambda x. lambda y. x.le y`. These are role methods, not globally monomorphic
primitive names. `lib/std/num.yu:8–9,27–28` supplies Sub and its int instance;
`lib/std/core/cmp.yu:6–19` supplies Ord and its int instance.
`lib/std/prelude.yu` reexports those definitions.
`web/docs/reference/operators.md` requires operator syntax imports and describes
the overloads; `web/docs/reference/control-flow.md`, if, specifies a Boolean
condition and braced syntax. These sources establish the available integer
implementation contracts; they do not establish that a particular current
Yulang inference resolves this witness to them or that its complete Call and
conditional semantics equal the reference combinator's semantics.

Let I be this Typer's `IntType` object and K its `BoolType` object, and extend the reference Ctx
by `le -> Function(I,Function(I,K))` and
`sub -> Function(I,Function(I,I))`. These are the integer contracts above,
imported as external Ctx entries using the existing reference API.
Object sharing matters: `package.scala:12` defines `is` as reference identity,
and constrain's primitive success relies on that identity early return.
No compiler configuration, primitive registry or source semantics is modified.
The fixed native RHS is:

```text
Lam("n",
  Let(true, "even",
    Lam("n",
      App(App(App(Var("if"),
                  App(App(Var("le"), Var("n")), Lit(0))),
              Var("true")),
          App(Var("odd"),
              App(App(Var("sub"), Var("n")), Lit(1))))),
    App(Var("even"),
        App(App(Var("sub"), Var("n")), Lit(1)))))
```

The exact **source extension premise** is a scoped elaboration from the
original overloaded operators, literals, local definitions and conditional to
this integer reference term, preserving O/E/a/b resolution, recursive visibility,
publication points, argument/branch checking and all original Call/effect
obligations. The reference supplies no role selection, complete Call/effect
proof or current Y3 admission bridge. The derivation below computes the whole
native instance; it does not assume that missing premise to close the original
source gate. No new restriction on the user's source is selected.

## 3. Actual native constructors and complete constraint generation

Use `L(v)`/`U(v)` for mutable bound lists. The tables record their distinct
members; actual lists may repeat a member during fresh constrain calls.
All variables start with empty lists. `Typer.scala:48–55` introduces o at
level 1 for O, `:64–67` introduces A at level 1 for a, then the nested recursive
let introduces e and B at level 2 for E and b. e is available but unused in
its own initializer. `Var` lookup at `:62–63` invokes instantiate;
`SimpleType.instantiate` at `:205–207` returns o unchanged for the inner odd.
No generalized O use is substituted here.

App (`:68–72`) visits callee, then argument, then allocates its lazy result and
constrains the callee below Function(argument,result). Function comparison
(`:106–108`) reverses argument comparison and preserves result comparison.
There are eleven native App nodes in the displayed RHS, all retained below.

The integer curried applications use the following common exact derivation:
for `p:I -> I -> Z` applied to variable x then literal k, first result P gets
`L(P)={Function(I,Z)}` and `x <: I`; the second App adds
`U(P)={Function(I,T)}` and replays its lower, yielding `I <: I` and `Z <: T`.
Hence `L(T)={Z}`. This follows actual insertion and replay, not an assertion
that a stored function constraint must succeed. Use this for le with Z=K,
and for sub with Z=I.

| Native occurrence, in actual recursive traversal order | Generated constraints and completed consequences |
| --- | --- |
| `if` Name, before its guard | Freshens builtin if above boundary 0 into j at level 2; returns `K -> j -> j -> j`. |
| `le b`, then `(le b) 0` | Level-2 P_le/G; `B <: I`; `L(P_le)={I -> K}`, `U(P_le)={I -> G}`, `L(G)={K}`. |
| `if G` | Level-2 H; `G <: K`, which stores U(G)=K and replays K below K; `L(H)={j -> j -> j}`. |
| `(if G) true` | Level-2 Q; `U(H)={K -> Q}`; replay yields `K <: j` and `L(Q)={j -> j}`. |
| `sub b`, then `(sub b) 1` | Level-2 P_sub/T; another `B <: I`; `L(P_sub)={I -> I}`, `U(P_sub)={I -> T}`, `L(T)={I}`. |
| `odd T` | Allocates R at level 2, generates `o <: Function(T,R)`; the extrusion and insertion in §4 complete. |
| `((if G) true) R` | Level-2 V; `U(Q)={R -> V}`; replay yields `R <: j`, then `j <: V`; both propagate their existing lower lists. |
| E recursive RHS completion | `Function(B,V) <: e`; inserts `L(e)={Function(B,V)}`; U(e) is empty. Publishes `PolymorphicType(1,e)`. |
| `even` Name | `freshenAbove(1,e)` at level 1 produces exactly e', B', V'; retains C and D unchanged. |
| `sub a`, then `(sub a) 1` | Level-1 P_outer/T_outer; `A <: I`; `L(P_outer)={I -> I}`, `U(P_outer)={I -> T_outer}`, `L(T_outer)={I}`. |
| `even T_outer` | Level-1 S; `e' <: Function(T_outer,S)` inserts U(e') and replays its lower: `T_outer <: B'` and `V' <: S`. |
| O recursive RHS completion | `Function(A,S) <: o`; inserts L(o) and replays **the actual existing** U(o), as §5 derives. Publishes `PolymorphicType(0,o)`. |

The type recursion is therefore generated across an inference level: o is
level 1 while its inner recursive application is inferred at level 2. The
outer source Value O is not the numerical type variable o, and a is not A.
Each correspondence here is local notation for this native derivation, not
an unproved Yulang occurrence-owner certificate.

## 4. Exact extrusion and completed conditional consumer

At `o <: Function(T,R)`, `level(T)=level(R)=2`, `level(o)=1`. The direct
left-variable insertion guard in `:115` fails. `:122–124` negatively extrudes
the demand to level 1 using one new polar memo. Function extrusion (`:144`)
flips argument polarity and keeps result polarity:

```text
extrude(Function(T,R),-,1) = Function(C,D)
memo(T,+)=C; memo(R,-)=D
U(T) gains C; L(C)={I}
L(R) gains D; U(D)={}
```

C and D are distinct fresh level-1 rows. `:146–155` memoizes each polar key
before traversing bounds. C copies T's positive lower I, while D copies R's
negative upper list, empty at this construction cut. **C's parent is the
subtraction result T, not the formal B.** No extrusion copy of B is needed:
B is not a child of this generated demand. There are exactly two wrong-level
variables in this occurrence and thus exactly these two polar pairs.

`constrain(o,Function(C,D))` now inserts `U(o)={Function(C,D)}`. L(o) is empty
at this cut, so there is no recursive-body lower to replay yet.
The later final if App compares Q's already stored `Function(j,j)` against
`Function(R,V)`. It stores `U(R)={j}` and replays `D <: j`.
Since D is level 1 and j is level 2, the **right-variable** guarded case
stores D in L(j); it does not install a high-level j in U(D).
Then `j <: V` stores U(j)=V and replays both lower members K and D. Consequently:

```text
L(j)={K,D}; U(j)={V}
L(V)={K,D}; U(V)={}
L(R)={D}; U(R)={j}
L(D)={}; U(D)={}                 [still empty at E publication]
```

All primitive comparisons so far are identity checks. The reference returns
immediately for identical SimpleTypes (`:92`); it does not require bool below
int. Every recorded high-level dependency is stored only on a row of a
sufficient level. This is the actual branch consumer/replay derivation, not
an opaque conditional result premise.

## 5. Nested generalization, outer replay and computed final scheme

At E publication the reachable native bound graph is:

```text
PolymorphicType(1,e)
e(level 2): L={Function(B,V)}, U={}
B(level 2): L={}, U={I}
V(level 2): L={K,D}, U={}
D(level 1): L={}, U={}
```

`freshenAbove` (`Typer.scala:166–188`) uses one unsigned identity map, copies
both lists of each reachable row above boundary 1, and stops at rows of level
at most 1. Thus the E use receives e', B', V' at level 1, with
`L(e')={Function(B',V')}`, `U(B')={I}`, `L(V')={K,D}`. D remains the **same
low-level row**; the map never visits j/R/T from this root, since they are not
in e's bound payload reachability. e' is not identified with e or O/E. C stays
on o's demand and is not in the local scheme graph.

The outer use's actual Function replay gives `T_outer <: B'`. At equal levels
the left-variable case wins, adding B' to U(T_outer); its lower I then enters
L(B') and is replayed against U(B')=I. It also gives `V' <: S`, placing S in
U(V') and replaying K and D. `K <: S` adds K to L(S). `D <: S`, now at equal
level 1, installs S in U(D). D still has no lower at this point.

O's completion then inserts `Function(A,S)` in L(o) and replays it against
the existing `Function(C,D)` in U(o). This invokes the two real children:

```text
C <: A; S <: D.
```

C's existing lower I reaches A, whose upper I admits it. S's existing lower K
reaches D, whose upper S causes `K <: S` replay, again compatible. The cache
for this constrain invocation cuts the repeated variable pairs (`:93–104`);
the resulting bound graph is finite. In particular, no nonexistent high-level
upper edge D->R/j/V is assumed. The distinct-member outer graph is:

| Row | Level | Lower bounds | Upper bounds |
| --- | --- | --- | --- |
| o | 1 | `Function(A,S)` | `Function(C,D)` |
| A | 1 | I | I |
| C | 1 | I | A |
| S | 1 | K | D |
| D | 1 | K | S |

This is an **actual computed native scheme**: `PolymorphicType(0,o)` with the
displayed reachable mutable bounds. It is not merely a proposed int/bool
assignment. `compactType(o)` (`TypeSimplifier.scala`, compactType) follows
positive lower bounds at o and S and negative upper bounds at A. It obtains
a nonrecursive positive root variable o together with one Function whose
domain is A intersect I and result is S union K. No variable-bound-only cycle
occurs on these selected traversals. In this compact output o and S occur
only positively and A only negatively; `simplifyType` removes those
nonrecursive variables in its first simplification loop. The computed output
is therefore the ground scheme:

```text
int -> bool
```

No residual free template or recursive type remains in that displayed scheme.
This is the reference algorithm's output for the fixed integer instance,
not a proved principal public scheme for all overloaded Yulang realizations.
The native intermediate `PolymorphicType` still retains its complete graph;
there was no early simplification of D out of E's live interface.

For a final fresh use of O at ambient level 0, `freshenAbove(0,o)` copies
o/A/S/C/D with **one** memo to distinct level-0 rows and copies both lists;
the S/D bound cycle shares the same new S/D rows. No level-1 anchor exists in
this reachable graph at boundary 0. A fresh Call with an int argument adds
ordinary argument/result constraints and propagates K to the new result.
Another use gets a different map; aliases of that one use share its rows.
This is per-use copying, not a new extrusion event or an intrusion premise.

There is also a direct declarative typing independent of interpreting solver
success as soundness. Under O assigned `I -> K` and inner b:I, the integer
primitive applications have guard K and subtraction I; O's recursive Call
has K; true has K; the reference if instance at j=K has result K. Hence E's
Lambda has `I -> K`. Under outer a:I, the final subtraction has I and E's
Call has K, so O's Lambda has `I -> K`. Recursive T-Let discharges the assumed
O type; nested recursive T-Let discharges E's unused monomorphic assumption.
This uses the original paper §2.2/Fig.3 and §3.5.2/Fig.8, with the same scoped
reference integer environment. It proves this reference term has the displayed
typing, without claiming a global let-polymorphic soundness/principality theorem.

## 6. Source recursion and intrusion qualification

With the frozen Name resolutions, the approved definition-root ownership rule
gives `O -> E` from O's final use of E and `E -> O` from E's recursive Call.
The nested initializer belongs to E. Therefore `{O,E}` is a nontrivial
Value-reference SCC across lexical/inference levels. This source recursion is
real; same-level mutual recursion is unnecessary. No subtype constraint,
Function bound payload, capture, arithmetic constraint or storage edge was
used to derive the SCC.

Native Simple-sub itself has neither this Value graph nor intrusion: it already
completes the instance without either. Its retained operational pairs for the
inner Call's extrusion are `(C,T,+,target=1)` and `(D,R,-,target=1)`. The original
code does not construct an event identity or origin/receiver Value endpoints.
Under the approved occurrence rule, **if an actual source constructor records
this extrusion's endpoints as (E,O)**, both pairs qualify because E/O share
the approved SCC, and the selected successor operation equates C=T and D=R.
The roots themselves are not equated and the type copies are not inserted as
Value vertices. Conversely, freshening e produces no such event.

That endpoint construction is unproved for this exact wrapped occurrence:
the recursive Call is inside the conditional's branch and its argument is an
overloaded subtraction. The approved bare f/g discriminator's origin G and
receiver F do not, by themselves, assign the owners of every nested wrapper.
Neither C's low level, T's association with an operand, nor storing
Function(C,D) on o determines (E,O). An actual event certificate must retain
the actual origin/receiver Values and both pairs through those source
constructors, replay, local publication and independent uses.

For this **fixed native store**, assigning T=C=I and R=D=j=V=V'=S=K is
compatible with the displayed constraints; the argument side A/C/B/B' can all
be I. That is a joint ground compatibility witness, not independent marginal
selection. It is not evidence that the live successor equality operation,
its level changes, future constraints or full source/fresh-use transport
preserve required principality. All those original gates remain OPEN.

## 7. Precise obstruction, economy audit and next bridge

The earlier conditional-prefix note
`2026-10-12-cross-level-odd-even-inference-derivation.md` deliberately left
arithmetic/conditional derivations and final scheme absent. This note closes
those **native integer-instance calculations** with independently found
contracts, actual App consumers and complete replay. It does not repeat the
prefix under newly named missing predicates.

The precise original-source premise still missing is:

```text
Original odd/even source formation with actual Ord/Sub resolution and Branch
  -> the eleven-App native integer instance (or its justified native extension),
preserving the original source judgments, scopes/publications and complete
Call/effect obligations, and constructing the extrusion event's actual Value
endpoints and its two produced polar pairs.
```

The source-elaboration/natural-acceptance part is class B; preservation of
complete typing, Call/effects and qualified equality is class A. Reconstructing
the actual event owners after App-demand creation is class D when those owners
were already known by the source constructor. The smallest next action is an
owner-directed construction/consumer bridge, preserving that known source
certificate, rather than another graph model inferred from bound adjacency.
This audit does not reclassify or close the original parent obligations.

No Yulang code, parser, HIR or runtime was read as a type specification or run
in this assignment. Existing source-admission reports remain separate evidence;
their prior rejection of the exact spelling is neither a language restriction
nor proof of native untypability. The reference term is not a certificate for
current HIR reachability. A source bridge must also retain the original provider,
attachment, witness and residual lineages; those domains do not exist in this
pure reference term and are not discharged by its two-port Function typing.

## 8. Dependency snapshot, checks and commit packet

Source hashes are SHA-256, captured from persistent files with `sha256sum`.
The reference commit `9bae772624c23b52a93c1b226157e16898b4d9db` is provenance
from the existing primary reference records; no Git command checked it here.
The operative dependency pin is the exact file content below. Likewise the
Yulang baseline is the primary's supplied SHA, not a locally queried HEAD.

| Dependency, relative to its named root | SHA-256 |
| --- | --- |
| Reference `shared/src/main/scala/simplesub/Typer.scala` | `f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9` |
| Reference `shared/src/main/scala/simplesub/syntax.scala` | `f26f19f6905d42c247198c45da9b1675b22619dd59749047023efe5f7ee3c60f` |
| Reference `shared/src/main/scala/simplesub/Parser.scala` | `245714abec4475bda3cf15d231932b47ffd778b9dcc5a7fd9ce634b2b0ceaaa5` |
| Reference `shared/src/main/scala/simplesub/TypeSimplifier.scala` | `618b63f63e71c31890eb36cb18be474bfd31732173c159132306f0e14dc37d2b` |
| Reference `shared/src/main/scala/simplesub/package.scala` | `c33b015e51baf32cb42ca48e6452ab005c85ac185a590ec870c19ef198b4fcb2` |
| `/home/momota1029/rust/simple-sub-reference-paper.pdf` | `5ab2bd4122caee17c20134e4cbe8dc8a4848c142de1e576b5fd178aed8787698` |
| Oracle `lib/std/int.yu` | `2d0d9b3bba4a4726dbb7f985e46524eea6b7e794759719a78d31984792b79822` |
| Oracle `lib/std/core/ops.yu` | `cb2c15eca2803a6b5a65e33541dd1213bd5f985c470a7767c17a4d59f77ca8c0` |
| Oracle `lib/std/core/cmp.yu` | `03881a76d3a159a23079ff0a1a87dbca42c4c101df47cd61c8f850fcbb7e33a8` |
| Oracle `lib/std/num.yu` | `631417ef1a85e38564fcc10d17b6eac6f64dfb735bf46d823ef1c7dd015f5e69` |
| Oracle `crates/infer/src/builtin_ops.rs` | `c79a7dfb031bc58598ea6551472be568362f3b34c1b7a1b4c53721e0581c053d` |
| Oracle `crates/infer/src/lowering/builtin_op.rs` | `a3eb2bcdfc9216015d8b7759028dd2c77a2f0a2465128de5b198300498c6cb95` |
| Yulang `notes/design/2026-10-12-intrusion-value-type-association.md` | `0063b88d17104f85182439d80360e42f8f99a5af4793eab70640a66f955ede25` |
| Yulang `notes/design/2026-10-10-parent-copy-scc-intrusion.md` | `6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b` |
| Yulang `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| Yulang `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |

Checks: static `cat`, bounded `rg`, `sed`/`nl`, `pdftotext -layout ... -`,
source SHA-256 capture and final dependency/text-integrity check. Coverage is
the frozen reference term, all eleven App nodes, recursive-let completion,
one two-pair extrusion, one local fresh-use map, final scheme simplification
and a boundary-0 fresh-use construction. Zero tests, builds, reference/runtime
executions, Oracle runs, probes, benchmarks or timing samples. No Git command,
child launch, model override, external contact or compiler/test edit occurred.
Only lightweight static commands ran; no heavy process. CPU/RSS and reasoning
wall time were not measured. No aggregate machine-resource reservation was
claimed; no verification process was started.

Requested runtime: `gpt-6.1-sol/high`, proof leaf. Observed effective model/effort:
unknown; no runtime metadata supplied. `.codex/config.toml` registers prover,
defaults Sol/high, and `.codex/agents/prover.toml` omits model/effort pins.
Those files are routing evidence, not proof that an override or reload ran.

Commit packet:

- Exact changed/leased path: `notes/theory/2026-10-12-cross-level-odd-even-simple-sub-derivation.md`.
- Baseline: `e37a937d02c88400a381e08253d0bfd7ac45a473`; changed dependency hashes:
  none detected in the final check of this snapshot; pinned-commit equality
  and branch integration remain the primary's responsibility.
- Review: unreviewed research; no self-certification or Yulang theorem closure.
- Checks already run: static original-source/rule derivation, primitive-owner
  inspection, complete native replay trace, source hashes and text integrity.
- Proposed checkpoint: `research: derive native cross-level odd-even integer typing`.
- Shared-record deltas left to primary/curator: record the complete native
  integer-instance scheme/pairs, distinguish it from the exact overloaded
  source bridge, retain the O/E cross-level source SCC, and keep event-owner,
  intrusion preservation, required principality, full Call/effect and F5 gates
  OPEN. No shared record was edited.
- One next action: establish the scoped operator/Branch-to-native bridge at
  its source constructors, including the actual extrusion event endpoints and
  both produced pairs. Writes stop at submission for independent review.
