# Odd/even with occurrence-qualified intrusion at demand extrusion

Date: 2026-10-12
Status: unreviewed conditional operational derivation; research only
Yulang baseline: `7b18d2a3f8d88b2b5541c6fed2069f2b694c2e82`
Reference baseline: `9bae772624c23b52a93c1b226157e16898b4d9db`
Exclusive output lease: this file; leaf, no further delegation

## 1. Frozen statement and interpretation boundary

Preserve the original source:

```yulang
my odd n =
    my even n = if n <= 0 { true } else odd(n - 1)
    even(n - 1)
```

O/E are distinct definition Values and a/b distinct formals. Inner `n`
resolves to b, outer `n` to a, inner `odd` to O, and final `even` to E.
O's recursive type row o is monomorphic throughout its initializer. E publishes
at boundary 1 inside that initializer; O publishes at boundary 0. This is
lexically nested recursion, without a sibling recursive group or polymorphic
recursive use. No source Value, formal, independent use frame, or provider is
identified by the equalities below.

Freeze the eleven-App integer reference term and shared primitive objects
I=`IntType`, K=`BoolType` from
[the complete native derivation](2026-10-12-cross-level-odd-even-simple-sub-derivation.md)
§§1–2. Its Ctx includes the reference builtins and the contracts
`le:I -> I -> K`, `sub:I -> I -> I`. The actual AST is:

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

The approved definition-root origin decision, integrated at `c0b67771d`,
selects (E,O) for the inner recursive Call's demand extrusion. Definition-root
incidences give O→E and E→O, so this event qualifies its actual polar pairs
`(C,T,+,1)` and `(D,R,-,1)`. C's parent T is the subtraction result, **not B**.
The endpoint decision is now an accepted premise; its actual compiler emission
and transport are not established here.

**Claim.** For this one fixed reference term and Ctx, apply precisely C=T and
D=R as type-variable identity immediately after this demand's negative
extrusion produces both pairs, before completing the demand insertion and
the later conditional App. Interpret identity by the leveled bound quotient
specified in §2, and otherwise use the original generation, guarded storage,
opposite-bound replay, freshening and simplification. The interpretation also
discards the suspended comparison cache and resumes the canonical demand in
a fresh cache as specified in §2; retaining its canonicalized key would skip
the required insertion. Under these explicit premises the finite run completes;
E's actual use copies exactly e/B/V; O publishes the graph in §5; its compacted
and simplified output is `int -> bool`, equal to the unintruded output.
The statement also holds under any injective renaming of fresh identities.
It does not quantify over another term, primitive resolution, SCC schedule,
intrusion encoding, arbitrary future constraints or source elaboration.

Claim class: **conditional finite operational derivation**, not an established
Yulang soundness/principality theorem, general preservation theorem, or
execution of an intrusive reference implementation. The mathematical quotient
is an explicit interpretation of the selected identity operation. Scala
`Typer.scala` contains no intrusion primitive; this derivation does not claim
that its unmodified executable performs the quotient. It supplies more than
a ground satisfiability witness: all subsequent native operations and actual
scheme allocations are derived.

The governing sections are top-level inference principles §§1–5; parent-copy
SCC decision, “Selected operation and compiler responsibility” and
“Definition-root Value ownership”; value/type association, “Approved
extrusion-event qualification” and “Definition-root origin for nested
call-demand extrusion”; Source Generalize §§2–4. The original Scala source
owns the native operations used below. The primary retains the original A/B,
complete Call, effect hygiene, soundness, required principality and F5 gates.

## 2. Equality, levels and the first operational boundary

The reference stores a row's bounds with the invariant that no payload has a
higher level than its owner (`Typer.scala:221–227`). `Variable.level` is
immutable. `Function.level` is a lazy maximum of its ports (`:209–211`).
There is no representative forest, row equality, level merge or quotient
normalization in that implementation.

Two ordinary calls to `constrain` are not a row-identity implementation. At
C.level=1, T.level=2, `constrain(C,T)` takes the right-variable case and adds C
only to L(T); `constrain(T,C)` takes the left-variable case and adds C only
to U(T), replaying T's lowers. C is not redirected to T, its level and bounds
are not unioned with T's, and later `freshenAbove(1,...)` can still copy T
while retaining C. The inequalities have their ordinary constraint meaning;
their insertion does not establish the approved identity or its operational
transport. This note therefore does not substitute those two calls for equality.

For the explicitly interpreted quotient, write X=[C=T], Y=[D=R]. Rewrite
every port, row occurrence, bound and active continuation through this identity
map; combine both lists on each equivalence class. Keep the source occurrence
and signed parent/copy provenance, including the now-reflexive extrusion links.
No other row equality is introduced. Recompute structural levels from the
canonical ports rather than relying on a pre-quotient Scala lazy cache.
T/R retain their original source occurrences inside E; minimum solver-level
metadata is not a rebinding of a source declaration or a change of its logical
scope. Native generalization acts on the resulting canonical rows, as traced
below. Correspondence to Source Generalize's original Desc scopes is separate.

The original copies and o have level 1. Retaining o's generated demand
`Function(X,Y)` on o requires X.level,Y.level≤1. Preserving the greatest
safe original level therefore assigns both quotient classes
min(1,2)=1. This is the level convention of this explicit interpretation,
not a theorem that equality alone uniquely specifies level bookkeeping.
Level 2 on either class would violate the owning demand's invariant; gratuitous
lowering to level 0 is not part of this trace. Every other row retains its
original level. At the actual occurrence cut, §3 shows that these two minimum
levels are sufficient: there is **no inherited high upper on Y** and no
third row needs lowering.

The comparison cache is part of the operational boundary. Each source App
calls `constrain` without an implicit cache (`:68–72`), so the default at
`:88–91` creates a fresh set for that top-level comparison. Recursive calls
within `constrain` reuse its implicit set, including the resumed call at
`:123`. Before extrusion begins, `:100–102` has already cached
`(o,F(T,R))`; this key records an in-process comparison, **not a completed
bound insertion**. At this cut that is the active set's only key: the outer
comparison takes extrusion directly, and `extrude:134–159` has a separate
polar memo and makes no `constrain` calls. Prior Apps' caches are separate.

Canonicalizing that set would turn its key into `(o,F(X,Y))`. Resuming with
that set would return at `:101`, before `:115–117` stores the demand. Keeping
the uncanonicalized key is not a justified solution either: the quotient
explicitly rewrites identities, and Scala supplies no quotient-aware cache
validity rule. The earlier continuation argument omitted this premise.

For **this one occurrence cut**, define the interpreted transition explicitly:

1. Preserve the accepted bound lists and the single suspended demand; apply
   the identity/level/port quotient above. Discard the active comparison set
   `{(o,F(T,R))}` rather than transporting its in-process marker into a
   completed-comparison marker.
2. Replay the snapshot of each quotient class's unioned lower/upper pairs,
   then the lower/upper pairs on P_sub, the only other row with a rewritten
   stored port at this cut, with a fresh native cache `K_eq={}`. Recursive
   replay calls share `K_eq`. Discard this set after replay completes;
   preserve all resulting bounds.
3. Replace the suspended extrusion frame's remainder by
   `constrain(o,F(X,Y))(K_resume)`, with `K_resume={}`. Its recursive calls
   share that set. Return from the suspended source App after this canonical
   demand completes; do not additionally invoke `:123` with the old set.

No ancestor comparison or sibling replay is pending within this App's
`constrain`: the only suspended branch is `:121–123`. The surrounding source
Apps have yet to issue their own comparisons. Thus this explicit transition
accounts for every pending comparison at the selected cut. It is an
**interpretation premise**, absent from stock Scala, and proves no general
cache invalidation or restart theorem for intrusion in other call stacks.
It changes no accepted bound or source obligation and performs no search for
another typing. Identity comparisons still return at `:93`; other variable
pairs are cached before their recursive children at `:100–102`. After this
boundary, all comparisons retain the original case order (`:106–127`).

The current candidate `merge_candidate_rows` (`candidate_intrusion.rs:513–605`)
unions both sides, takes minimum levels, redirects representatives and replays
retained lowers. That is a useful implementation owner, not a proof that it
implements this quotient on this source: its qualification still inspects
bound-derived endpoint components, and the approved occurrence certificate is
absent from its input. The candidate is not used to define the source theorem.

## 3. Complete original prefix and the actual equality event

Write F(u,v)=Function(u,v). Tables show distinct list members; duplicate
insertions are retained operationally and do not change the distinct-member
trace. I and K are the exact shared primitive objects, so their self comparisons
take reference identity success (`package.scala:12`, `Typer.scala:93`).

`typeLetRhs:48–55` allocates o at level 1; Lam `:64–67` allocates A at level 1.
The nested recursive E allocates e and formal B at level 2. E's e is unused
in its own initializer. Monomorphic lookup of o returns o unchanged
(`:62–63,205–207`). The if Name freshens its builtin scheme at level 2, giving
j at level 2 and type F(K,F(j,F(j,j))).

App visits callee, then argument, then allocates its lazy result and adds a
Function demand (`:68–72`). Before the inner `odd` demand:

| App, in traversal order | Native consequences and replay |
| --- | --- |
| `le b` | B<:I; L(P_le)={F(I,K)}. |
| `(le b) 0` | U(P_le)={F(I,G)}; replay gives I<:I and K<:G, so L(G)={K}. |
| `if G` | G<:K stores U(G)={K} and replays K<:K; L(H)={F(j,F(j,j))}. |
| `(if G) true` | U(H)={F(K,Q)}; replay gives K<:j and F(j,j)<:Q; L(j)={K}, L(Q)={F(j,j)}. |
| `sub b` | Another B<:I; L(P_sub)={F(I,I)}. |
| `(sub b) 1` | U(P_sub)={F(I,T)}; replay I<:I, I<:T; L(T)={I}. |

The recursive App now allocates R at level 2 and requests o<:F(T,R).
Its fresh comparison cache becomes `{(o,F(T,R))}` before either level guard.
Its demand level 2 fails the first left-variable guard for level-1 o.
`constrain:121–123` invokes `extrude(F(T,R),false)(1,new polar memo)`.
Function extrusion reverses the domain polarity (`:144`). Allocation and
memoization precede bound traversal (`:146–155`), giving exactly:

```text
C(level 1): L={I}, U={}        T(level 2): L={I}, U={C}
D(level 1): L={},  U={}        R(level 2): L={D}, U={}
extruded demand = F(C,D)
```

There are no further wrong-level variables in the demand's selected bound
traversal. This is the occurrence that receives the approved (E,O) endpoints.
Introduce its two equalities here, before returning to demand insertion:

```text
X(level 1): L={I}, U={X}
Y(level 1): L={Y}, U={}
extruded demand = F(X,Y)
P_sub's stored upper = F(I,X)
```

Under §2's transition, the old active comparison set is discarded. X's
cross-product is I<:X: starting from `K_eq={}`, `:102` records `(I,X)`,
the right-variable case inserts another I in L(X), and U(X)=X replays
`(I,X)`, which now returns at `:101`. Y has no upper, so its self lower
generates no comparison. Replay finishes with `K_eq={(I,X)}` and no
high-level bound: P_sub's rewritten cross-product compares F(I,I) with
F(I,X), producing the identity I<:I and the already completed cached I<:X.
No other stored port contains T/R/C/D at this cut; the two remaining
Function occurrences are the original and extruded suspended demands,
both canonicalized to F(X,Y) and discharged by the one replacement below.
That replay cache is then discarded.

The replacement continuation starts with `K_resume={}`. Since o and
F(X,Y) are distinct and its pair is absent, `:102` records `(o,F(X,Y))`;
F(X,Y).level=1 now satisfies the left-variable guard at `:115`. Line `:116`
inserts U(o)={F(X,Y)}. L(o) is still empty, so `:117` has no lower to
replay. It returns with `K_resume={(o,F(X,Y))}` and completes the suspended
App. Its prior key could not supply this insertion. Thus the interpreted
equality event succeeds with accepted bounds and the original demand retained.
No equivalence with inserting before quotient or retaining another cache is
claimed.

## 4. Conditional completion and actual E publication/use

Every later source App and recursive RHS completion starts its own default
empty comparison set (`:71,52,88–91`). None inherits `K_eq`, `K_resume` or
the discarded suspended set. The caches below list distinct variable-bearing
keys after completion; structurally compared Function pairs and identity
primitive comparisons do not enter the cache (`:93–103`).

The final if App allocates V at level 2 and requests Q<:F(Y,V).
Q's existing lower F(j,j) is replayed, giving **Y<:j** and **j<:V**.

Y.level=1 and j.level=2. The left-variable guard fails, and the right-variable
guard succeeds: insert Y in L(j), leaving U(Y) empty. U(j) is empty at that
moment. Next j<:V, at equal level 2, takes the left-variable case: U(j)={V}
and replays both K<:V and Y<:V. K<:V inserts K in L(V); Y<:V again takes
the right-variable case and inserts Y in L(V), leaving U(Y) empty. Therefore:

```text
j(level 2): L={K,Y}, U={V}
V(level 2): L={K,Y}, U={}
Y(level 1): L={Y},   U={}
Q(level 2): L={F(j,j)}, U={F(Y,V)}
```

The final-if cache is exactly
`{(Q,F(Y,V)),(Y,j),(j,V),(Y,V),(K,V)}`. Each listed pair is first inserted
before its storage/replay; none is present from the intrusion transition.

In particular, identity D=R does **not** force j or V to level 1 in this
occurrence-cut trace: neither is stored as an upper on Y. No unprovided
high-level Y→j/V edge or third-owner replay is inserted.

E completion adds F(B,V)<:e. The right-variable case inserts that Function
in L(e); U(e) is empty. E publishes `PolymorphicType(1,e)`. Its reachable
payload graph consists exactly of e/B/V/Y:

```text
e(2): L={F(B,V)}, U={}
B(2): L={}, U={I}
V(2): L={K,Y}, U={}
Y(1): L={Y}, U={}
```

The E-completion cache is `{(F(B,V),e)}`. Freshening itself invokes no
`constrain` and transports no comparison cache (`:166–188`).

The final Name `even` invokes `freshenAbove(1,e)` at ambient level 1
(`:166–188,199–202`). One unsigned memo copies e, B, V into distinct level-1
e', B', V'. It copies both bound sides; Y stops at the boundary and remains
the same row. It never reaches j, X, P_sub or any demand backward from the
callee root. The resulting frame is:

```text
e'(1): L={F(B',V')}, U={}
B'(1): L={}, U={I}
V'(1): L={K,Y}, U={}
```

This is an actual derived allocation, not an assumed retained constraint or
independently chosen marginal witness. Freshening allocates no extrusion pair
and triggers no new intrusion. The original e/B/V rows remain distinct.

The last three Apps and O completion are:

| Native occurrence | Constraint insertion and complete replay |
| --- | --- |
| `sub a` | A<:I; L(P_outer)={F(I,I)}. |
| `(sub a) 1` | U(P_outer)={F(I,T_outer)}; replay I<:I and I<:T_outer, so L(T_outer)={I}. |
| `even T_outer` | Allocate S(1); insert U(e')={F(T_outer,S)}; replay F(B',V'), giving T_outer<:B' and V'<:S. |
| Argument replay | Equal-level left-variable storage adds B' to U(T_outer); I<:B' inserts I in L(B') and replays U(B')=I, checking I<:I. |
| Result replay | V'<:S stores S in U(V') and replays K<:S and Y<:S. K enters L(S). Equal-level Y<:S stores S in U(Y); its self lower replays the same cached pair and stops. |
| O completion | F(A,S)<:o inserts L(o) and replays U(o)=F(X,Y), yielding X<:A and S<:Y. |

For X<:A, store A in U(X). Its I lower propagates to L(A), whose existing
upper I checks I<:I. For S<:Y, store Y in U(S). Its K lower gives K<:Y;
the right-variable case inserts K in L(Y), then U(Y)=S gives K<:S. S has
upper Y, so K<:Y is repeated in this same cache and returns. All self and
variable cycles are finite; every primitive leaf check is I<:I or K<:K.
No bool/int or Function/primitive contradiction occurs.

For completeness, the remaining source-comparison caches are:

| Comparison | Distinct keys at return |
| --- | --- |
| `sub a` | `(A,I)`, `(F(I,I),P_outer)` |
| `(sub a) 1` | `(P_outer,F(I,T_outer))`, `(I,T_outer)` |
| `even T_outer` | `(e',F(T_outer,S))`, `(T_outer,B')`, `(I,B')`, `(V',S)`, `(K,S)`, `(Y,S)` |
| O completion | `(F(A,S),o)`, `(X,A)`, `(I,A)`, `(S,Y)`, `(K,Y)`, `(K,S)` |

In the even Call, Y's self lower repeats `(Y,S)` after its first insertion.
In O completion, X's duplicate I lowers repeat `(I,A)`; the S/Y cycle
repeats `(K,Y)` after both K insertions. These returns skip only comparisons
whose relevant insertion has already run in this same post-quotient store.
No identity change occurs after §3, so no later key changes meaning or
collides with the pre-insertion marker that caused the original gap.

This covers all eleven Apps (six in the prefix, recursive odd, final if,
two outer subtraction Apps, final even), both recursive RHS completions,
both row identifications, the explicit cache transition, and every newly active
replay path. The finite cache proof concerns this trace; it is not
combined-algorithm termination.

## 5. Complete final store, publication and unchanged output

The distinct-member final store has 19 quotient rows (21 before the two
identifications):

| Row | Level | Lower | Upper |
| --- | --- | --- | --- |
| o | 1 | F(A,S) | F(X,Y) |
| A | 1 | I | I |
| e | 2 | F(B,V) | empty |
| B | 2 | empty | I |
| j | 2 | K,Y | V |
| P_le | 2 | F(I,K) | F(I,G) |
| G | 2 | K | K |
| H | 2 | F(j,F(j,j)) | F(K,Q) |
| Q | 2 | F(j,j) | F(Y,V) |
| P_sub | 2 | F(I,I) | F(I,X) |
| X=[C=T] | 1 | I | X,A |
| Y=[D=R] | 1 | Y,K | S |
| V | 2 | K,Y | empty |
| e' | 1 | F(B',V') | F(T_outer,S) |
| B' | 1 | I | I |
| V' | 1 | K,Y | S |
| P_outer | 1 | F(I,I) | F(I,T_outer) |
| T_outer | 1 | I | B' |
| S | 1 | K | Y |

Every payload level is at most its owner's. No row besides X/Y changes level;
the table is a direct certificate for this claim. Equality has affected actual
identity, bound ownership, guarded case selection and the E-use map, even
though the final displayed output agrees with the unintruded run.

O publishes `PolymorphicType(0,o)`. Both-side payload reachability from o
contains exactly o/A/S/X/Y. Boundary-0 `freshenAbove` copies those five rows
with one memo, including the X upper self edge, Y lower self edge, and S/Y
opposite-bound cycle. Other original and E-use rows are not reachable and are
not identified with this fresh frame. Independent uses get different maps;
aliases of one use share its map. The copied payloads all have level 0.

For an ordinary final int Call, replay the copied F(A,S) lower against the
new F(I,Z) demand. I<:A checks the retained I upper; S<:Z propagates the K
lower to Z. This further source Call likewise uses a fresh comparison cache:
with copied rows denoted o_c/A_c/S_c, its keys are
`{(o_c,F(I,Z)),(I,A_c),(S_c,Z),(K,Z)}`. It does not manufacture a high-level
return upper on original Y.
This verifies this one further native use, without arbitrary-client claims.

`TypeSimplifier.scala:49–84` compacts the positive o root through L(o)=F(A,S),
negative A through U(A)=I, and positive S through L(S)=K. X/Y's self bounds
and uppers are outside that selected polarity traversal. The compact type
has positive o, negative A with I, and positive S with K; no recursive type
variable is needed. `simplifyType:181–245` removes these nonrecursive rows
occurring in only one polarity. `coalesceCompactType` then yields:

```text
int -> bool
```

The unintruded trace has the same selected o/A/S graph and the same E-use
copy set e/B/V; its lower anchor D is replaced by Y here. The extra self
bounds are reflexive and do not change this compaction. Hence **acceptance
and the computed reference principal-output candidate agree for the fixed
instance**. This is an output comparison, not a proof that every original
typing is preserved by intrusive inference or that this is Yulang's required
principal public scheme for all overloaded realizations.

There is also the unchanged direct reference typing: assign outer O and inner
E the type I→K, both formals I, all comparison/conditional results K and
all subtraction results I. All eleven Calls, both branch arguments and both
recursive completions type under that one simultaneous choice. X=T=C=I and
Y=R=D=K respect both equalities. This supplements the operational trace; it
does not replace its replay or generalization proof with satisfiability.

## 6. Source/implementation bridge and omitted cases

The earlier reviewed ground-model note applied the same two equalities to
the **completed unintruded store**, after E's use was allocated. There R
already had upper j. Quotienting D/R inherited that high upper on Y, requiring
j/V level closure and an explicit replay at j. This derivation applies the
equalities at the original demand occurrence; R has no upper yet, and future
native guards store Y below j/V without high uppers on Y. These are different
operational cuts. Neither result proves their scheduling equivalence; this
note selects no delayed policy and does not reinterpret the older note as
an occurrence-cut run.

Minimum premises for connecting **this exact trace** to Yulang are:

1. The exact original source must form with its actual Ord/Sub instance,
   literals, Branch and complete Calls, preserving O/E/a/b resolution,
   recursive visibility, source scopes and publication points. Its integer
   elaboration must justify the fixed eleven-App reference instance, including
   effects and checking obligations. The reference has no overloaded roles,
   Branch or effect representation; the earlier grounded integer primitive
   contracts alone do not prove this elaboration.
2. The source constructor must emit the actual occurrence with origin E,
   receiver O, and signed pairs (C,T,+,1),(D,R,-,1), alongside the independent
   approved source-reference SCC. The user selects the endpoints; that does
   not establish emission, preservation or activation in the compiler.
3. Its actual equality consumer must implement type identity, bound union,
   valid levels, canonical structural ports and complete replay at this cut;
   it must also establish a comparison-cache/continuation law that prevents
   the cached in-process demand from suppressing its own resumed insertion.
   The particular fresh-cache boundary in §2 is an interpretation premise,
   not a demonstrated implementation law or an approved caching policy;
   its subsequent E publication and use must consume the resulting live
   graph. An incremental scheduler discovering the SCC later needs its own
   preservation/correspondence proof; this trace does not establish it.

The actual checked owning seams are:

| Owner | Current evidence and remaining premise |
| --- | --- |
| `local_source.rs`, local initializer/Name construction | Retains binder identities, sequential scope and initializer source structure; it does not establish admission of this complete conditional/operator source. |
| `candidate_source.rs:250–327,370–410` | Active recursive local Names Link to the initializer endpoint; later uses install/use local schemes. Apply records retain operands and occurrence, but `owner` is `source.definition_root()`, not a demonstrated nested E event certificate. |
| `shadow_apply.rs:1335–1443` | Constructs a four-port demand, admits the value relation, retains a NativeInterface and forwards callee/invocation effects. No origin/receiver extrusion occurrence is passed here. Complete Call and effect laws are not reduced to the two-port reference Function. |
| `candidate_extrusion.rs:20–35,90–175` | Accepts endpoint/polarity/level, creates real polar copies and retains parent/polarity/target before bound transport. It has no input for (E,O) plus a common event identity. |
| `candidate_intrusion.rs:349–509,513–605` | Qualification uses a graph walked from solver bounds/ports, followed by canonical merge and replay. This is not the approved Value-reference event qualification or a source bridge for this trace. |
| Source Generalize §§2–4 | Requires source-owned declarations, original scopes, active complete clauses and coherent whole frames. Native numerical levels and this graph do not establish its fixed/template classifications or local complete Call laws. |

The first concrete missing operational law for an **actual reference execution**
is an intrusion quotient primitive that canonicalizes mixed-level rows and
their pending ports/bounds, invalidates the suspended comparison marker and
then actually inserts/replays the resumed demand. Canonicalizing the marker
alone fails this exact trace at `Typer.scala:101`. The original
reference has no such operation. This note derives its finite interpreted
consequence rather than claiming it exists. Its first Yulang bridge premise
is exact scoped source formation, followed by the owning event/equality
consumer correspondence above. No source-qualified contradiction was found.

Under the proof-obligation-economy audit, preservation and faithful activation
are A/B; retaining the already known source root and callee on the demand
event addresses D. Another post-hoc ground model would leave those same
premises untouched. The constructive progress here is the previously absent
**occurrence-cut** operation and full continuation, not a new classification
of the parent claim. Attachment, provider, witness and residual lineage are
absent from the reference carrier and remain distinct unproved obligations.

Unverified: arbitrary terms and continuations; general equality levels;
incremental SCC detection and other schedules; recursive/mixed polar memo
transport; existing frame recapture; abnormal paths; Source Generalize and
public projection correspondence; complete Call/effects; global soundness,
required principality, normal progress/termination and production/F5 cutover.
General cache reuse/invalidation, cache equivalence under identity and restart
with multiple active comparison frames are also unverified.
No source restriction, annotation requirement, fixed-anchor reclassification,
new implementation policy or theorem-status promotion is adopted.

## 7. Checks, dependencies and commit packet

Commands were read-only `cat`, bounded `rg`, `sed`, `nl -ba`, and `sha256sum`
on the enumerated sources. Initial baseline inspection also ran `pwd`,
`git rev-parse HEAD`, `git status --short`, and
`git -C /home/momota1029/rust/simple-sub-reference rev-parse HEAD`; both SHAs
matched the packet. Those were read-only Git inspections; no Git mutation
occurred. The reference checkout was not changed. A final leased-note text
and dependency check is recorded in the handoff. Some broad initial captures
truncated; decisive operations and authority sections were reread in bounded
windows. No command output is source-semantic evidence beyond the displayed
actual file bodies and content hashes.

Focused cache repair reread `Typer.scala:48–83,88–159,166–233`, re-derived
the suspended key and every post-quotient comparison cache above, and changed
only this leased note. The initial artifact SHA-256 was
`274954607ea058cb2df3cb50b8f4daaeec8b0b67f34afc6839d08088639c335a`.
At repair inspection Yulang HEAD was
`8d2582f93c659677ebfb277fae1d55d5d159a4b6`; all 15 direct dependency
hashes below still matched the pinned snapshot and the Scala baseline still
matched. The proof baseline remains the primary's `7b18d2a3f`.
The repair used `apply_patch` only on the lease; a read-only `python3` text
integrity check found 15 matching dependency entries, no trailing whitespace
and 18 paired code-fence markers. `git status --short -- <lease>` reported
the note untracked, so `git diff -- <lease>` has no tracked diff to inspect.
No Git mutation occurred; the final artifact hash is supplied in the handoff.

Verification ownership: this leaf for its static derivation and text integrity;
the primary for integration and independent review. Zero reference executions,
computational probes, tests, builds, Oracle runs, benchmarks or measurement
samples. Equality injection did **not** execute the actual Scala implementation.
The optional one ≤60s, ≤12 GiB computation allowance was unused. No heavyweight
process or child was launched. Static command calls completed below 60s;
CPU/RSS and reasoning wall time were not instrumented. No aggregate resource
reservation or performance result is claimed.

Requested runtime: `gpt-6.1-sol/high`, proof leaf. Observed effective model and
effort: unknown, unavailable runtime metadata. `.codex/config.toml` registers
prover with Sol/high defaults; `.codex/agents/prover.toml` omits model/effort
pins. These files do not prove an override or hot reload. No Astra escalation,
delegation, external recipient or user contact was used.

SHA-256 dependency snapshot:

```text
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389 notes/design/2026-10-11-yulang-inference-top-level-principles.md
6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b notes/design/2026-10-10-parent-copy-scc-intrusion.md
28a0c2aa196912e59e9adb9e62e30d171a03fc485d36314db02c5e13b74f6775 notes/design/2026-10-12-intrusion-value-type-association.md
46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38 notes/design/2026-10-08-source-generalize-definition.md
5a4d89e1c22b553767a6e6789199ec7ef54cafd96216bd1c6b00147d1a1672ad notes/theory/2026-10-12-cross-level-odd-even-simple-sub-derivation.md
4b9d43a1af9454dcd569b53eb293b2a342b81c8a3b404e2cd32d12950ce8b443 notes/theory/2026-10-12-odd-even-intrusion-ground-model-proof.md
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49 crates/yu-solver/src/candidate_source.rs
fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0 crates/yu-solver/src/candidate_extrusion.rs
aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0 crates/yu-solver/src/candidate_intrusion.rs
cbd2e0c49a3f1fbe3c5fc78a06d469faedf4aa261525b24a0c9584e9956c2411 crates/yu-solver/src/shadow_apply.rs
906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed crates/yu-hir/src/module/local_source.rs
f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9 /home/momota1029/rust/simple-sub-reference/shared/src/main/scala/simplesub/Typer.scala
618b63f63e71c31890eb36cb18be474bfd31732173c159132306f0e14dc37d2b /home/momota1029/rust/simple-sub-reference/shared/src/main/scala/simplesub/TypeSimplifier.scala
f26f19f6905d42c247198c45da9b1675b22619dd59749047023efe5f7ee3c60f /home/momota1029/rust/simple-sub-reference/shared/src/main/scala/simplesub/syntax.scala
c33b015e51baf32cb42ca48e6452ab005c85ac185a590ec870c19ef198b4fcb2 /home/momota1029/rust/simple-sub-reference/shared/src/main/scala/simplesub/package.scala
```

The association hash differs from the old derivation/ground-model snapshots
because the approved nested definition-root endpoint decision is now integrated.
This packet intentionally consumes that updated authority. No dependency file
was edited by this producer; final recheck and artifact hash are supplied to
the primary. Shared records, compiler code and tests remain primary-owned.

One next action: fresh independent delta review of the repaired cache boundary,
its full continuation and explicit quotient/reference premise before applying it
to the source-construction/equality-consumer bridge.

Commit packet:

- Exact leased/changed path: `notes/theory/2026-10-12-odd-even-qualified-intrusion-derivation.md`.
- Baseline: `7b18d2a3f8d88b2b5541c6fed2069f2b694c2e82`; reference `9bae772624c23b52a93c1b226157e16898b4d9db`; dependency change from historical notes: association hash now `28a0c2aa196912e59e9adb9e62e30d171a03fc485d36314db02c5e13b74f6775`. No producer dependency mutation.
- Review status: conditional research checkpoint repaired after an independent MAJOR cache finding; repaired delta awaits independent review, with no self-certification or parent closure.
- Checks already run: actual constructor/consumer inspection; complete handwritten occurrence equality/replay/generalization/simplification trace; dependency and text checks. No equality-injected reference execution.
- Proposed message: `research: make odd-even intrusion cache continuation explicit`.
- Shared-record deltas left to primary/curator: record fixed-instance completion and unchanged `int -> bool` conditional on the explicit occurrence-cut quotient **and fresh comparison-cache boundary**; identify canonicalized suspended-cache reuse as a failed route. Keep actual cache/continuation correspondence alongside source formation, event/equality correspondence, full Call/effects and all original parent A/B gates OPEN. Update `tasks/current.md` and the relevant theory map only after adjudication. No shared record was edited.

Writes stop at submission for independent review.
