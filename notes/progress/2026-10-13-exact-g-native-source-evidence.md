# Exact Int/Unit named-drop source: native levels, maps and current incidences

Date: 2026-10-13 (task naming); environment date: 2026-10-12
Status: independently reviewed bounded native evidence; no source theorem or implementation authority
Assigned remote baseline: `38bda20257d58069097a3e42c358b6759fb26d58`, `momota1029/yulang`, `research/simple-sub-intrusion`
Reference baseline: LPTK/simple-sub `9bae772624c23b52a93c1b226157e16898b4d9db`
Method: exact syntax/boundary substitution, original-reference finite trace, current producer/consumer audit
Lease: this note and `tools/research_exact_g_native.py`; no delegation or Git mutation

## 1. Decision-relevant outcome and claim boundaries

The fixed source is:

```yulang
my answer = { my f x = { my g y = { my drop z = y; drop (f y) }; my first: int = g 0; g () }; f }
```

As written above it has 97 ASCII bytes, without a terminating newline, with
SHA-256 `00df6ef5a75c6a75f9a7fd5eff3f549d06c3c52e7f6065dea4408ccc77c4d980`. Its
four actual Apps are `f y`, `drop (f y)` and the two independent g uses
`g 0`, `g ()`: four Apps in total. The parentheses around `f y` form Group;
the empty parentheses are Unit. `drop` is a named local with its own
initializer/publication and later Name use. `first` is another local with a
whole-initializer annotation check. The final `f` is a use after f publication.

Three precise results follow from this pass:

1. The current source schedule starts the answer RHS at level 1. f's
   initializer/formal is at 2, g's at 3, drop's at 4. The first g use, in
   first's initializer, is at 3; the second is at 2. The native recursive
   demand crossing into f therefore has target **2**, under that absolute
   convention. Writing `(C,B,+,1),(D,R,-,1)` for this exact source is lawful
   only as an expressly declared relative normalization, subtracting the
   answer RHS's one level. It is not the literal generated absolute target.
2. In the explicitly declared scalar reference analogue, named drop
   freshens its own z description while retaining its capture of y. g's two
   subsequent uses freshen its B/S correlation independently and retain the
   same C. Both actual argument constraints and the first result check reach
   their intended coordinates. The unused `f y` result remains constrained;
   it is not erased. Ordinary inference succeeds in this finite analogue.
   Adding supplied shared-C equality clauses on its actual two use images
   requires `unit <: int` and fails its primitive rule.
3. In the current Rust demand producer, the bare argument Name y selects the
   **formal parameter endpoint B**, not the unused value component allocated
   for that Name. Copy creation records its canonical representative as
   parent. The callee Name f, Group around `f y`, block results and local
   lambda roots do have distinct facades and directed bounds. Those must not
   silently be identified with reference expression results or source Values.

Result 2 is a finite native characterization under declared Unit/Group/check
rules. Result 3 is a static implementation observation, conditional on the
respective native comparisons being reached with the displayed representatives
and levels. Neither is a full Yulang source derivation, a claim of exact
parser/runtime acceptance, complete Call/effect adequacy, lawful source
equality transport, principality, or a source-qualified counterexample.
No equality activation point or SCC-readiness policy is selected here.

## 2. Governing sources and source positions

The first theory inputs read were the four requested notes:

- `notes/theory/2026-10-13-active-root-call-source-construction.md`;
- `notes/theory/2026-10-13-nested-live-root-generalization-derivation.md`;
- `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`;
- `notes/theory/2026-10-12-source-publication-classification-proof.md`.

Their native target-1 history concerns the different original-reference
Record/Bool witness with an anonymous inline wrapper. The exact Int/Unit
named-drop source above is kept separate. Their conditional equality result
is not imported as a theorem about this source. The selected Source Generalize
definition, local self-recursion, parent-copy operation, occurrence qualification,
copied-row ownership and top-level inference principles were read directly.
The adopted Generalize construction consumes authentic source clauses/scopes;
this note does not assign its validating component or repeat the other lane's
registration investigation.

Positions below are zero-based half-open byte intervals in the exact 97-byte
line above. They locate source syntax without pretending to be emitted HIR
identities or resolved occurrence certificates.

| Syntax | Interval | Retained distinction |
| --- | --- | --- |
| answer binder | `[3,9)` | outer definition whose RHS starts at 1 |
| `my f` | `[14,18)` | parameterized local; open native root during inference |
| `my g` | `[25,29)` | nested parameterized local; its own native root |
| `my drop` | `[36,43)` | additional initializer/publication and fresh-use map |
| `drop (` | `[51,57)` | published drop Name as callee |
| `(f y)` | `[56,61)` | Group containing the actual recursive App |
| `f y` | `[57,60)` | actual callee f and bare formal argument y |
| `my first` | `[65,73)` | additional annotated local initializer |
| `g 0` | `[81,84)` | first independent Name use, under first's initializer |
| `g ()` | `[86,90)` | second independent Name use and actual Unit argument |
| final `f` | `[94,95)` | ordinary use after f installation |

The original Typer has `Var`, `Lam`, `App`, `Lit`, `Sel`, `Rcd`, `Let` cases
at `Typer.scala:58–83`. It has no Unit or annotation case. Its builtins at
`:20–32` have int/bool primitives, not a unit builtin. Therefore none of the
checker executions below is reported as execution of the unchanged Scala
implementation on exact Yulang text.

## 3. Absolute levels and which order they describe

HIR retains all five local/source binders and x/y/z introductions:
`local_source.rs:329–374` forms each parameterized initializer with temporary
self visibility, then restores and publishes the same local ID. Its
`:636–700` Name/parentheses branches distinguish resolved Names, Group and
Unit. Its `:710–829` block owner retains sequential bindings and each original
initializer. A Group increments HIR traversal depth, not a polymorphism level.

The candidate source emitter at `candidate_source.rs:245–328` starts with
`Work::Visit(source.body(),1)`, preserves level through Lambda/Apply/Group,
and adds one for each block-local initializer. It installs at the surrounding
block boundary. `:527–555` writes these levels to component and formal rows.

| Native cut | Absolute level / boundary | Relative level after subtracting 1 |
| --- | --- | --- |
| answer RHS and final f Name | 1 / answer boundary 0 | 0 / boundary -1, if extended to answer |
| f initializer, x and f open root | 2 / f boundary 1 | 1 / boundary 0 |
| g initializer, y, `f y`, Group and drop App | 3 / g boundary 2 | 2 / boundary 1 |
| drop initializer and z | 4 / drop boundary 3 | 3 / boundary 2 |
| drop Name use in g body | 3; fresh-use boundary 3 | 2; boundary 2 |
| first initializer and `g 0` | 3 / first boundary 2 | 2 / boundary 1 |
| `g ()`, f's final body result | 2 | 1 |
| recursive demand copies into f | target 2 | target 1 |

Only the subtree beginning with f has a natural nonnegative normalized
boundary-0 notation. Extending subtraction to answer's own boundary gives
-1; this shows that it is a projection of the selected subtree, not the
entire absolute compiler level convention. Subtraction preserves cutoff
comparisons within that subtree. It does not erase named drop, first, their
publication boundaries, the two differing g use levels, or logical telescopes.

There are two different orders here. The **native inference schedule** visits
the latent f body and installs g/drop while f's initializer is still active;
the later f Lambda fact and f installation follow its body constraints.
The **source runtime tree** first forms/publishes the f closure. An actual
later f invocation h enters its body, forms/publishes g at p_g(h), then has
the ordered first and final g-call suffix. A g invocation forms/publishes
drop capturing that invocation's rebound y. drop's bare z entry forces the
whole `f y` argument before returning captured y, when that entry returns.
Native g installation while f inference is active is not runtime g closure
publication before f closure publication. Recursive execution may leave the
suffix pending; no termination or reachability of runtime returns is assumed.

## 4. Declared reference analogue with every binder/boundary retained

Use the original scalar Typer constructors, with these three explicit additions:

- Unit is a distinct primitive of level 0, with the same primitive comparison
  discipline as int. It is not bool or Record.
- Group retains an AST node and infers its child at the same level, returning
  that child's **scalar type**. This is a declared scalar rule. Rust's Group
  uses a bounded facade instead; no equivalence is assumed.
- An annotated local infers its initializer at boundary+1, constrains its
  inferred value below the annotation, then exposes the primitive annotation.
  It does not infer the initializer at the enclosing boundary or delete the
  initializer because the local is unused. This matches only the intended
  scalar check/exposure projection, not all Yulang annotation/effect semantics.

The concrete AST used by the checker is:

```text
typeLetRhs(false, answer,
  Let(true, f, Lam(x,
    Let(false, g, Lam(y,
      Let(false, drop, Lam(z, Name(y)),
        App(drop-call, Name(drop), Group(App(f-y, Name(f), Name(y)))))),
      CheckedLet(first, int, App(g-int, Name(g), Int(0)),
        App(g-unit, Name(g), Unit)))),
    Name(f)), boundary=0)
```

`Let(false,g/drop,...)` is the stock reference's nonrecursive-let constructor
applied to bodies with no self occurrence. Yulang's parameterized form grants
temporary self visibility and the current candidate still has active
initializer facade roots for both. Those facts do **not** prove that its
installed roots are the direct Function expressions in this first analogue.
To expose that difference, a second declared analogue uses the original
`Let(true,...)` constructor for g and drop as well. It keeps extra open
q_g/q_drop roots even though their bodies do not refer to themselves. Both
are analyzed below. Neither is asserted equivalent to all the Rust Name,
Group, Block, contextual or effect facades.

### 4.1 Direct-Function publication analogue: exact finite equations

Let o/A be f's open root and x formal, B the y formal, Z the original z
formal, Z* its fresh image at drop use, R the `f y` result, S the drop App
result, and V0/V1 the two actual g App results. Literal levels are:

```text
o,A @2; B,R,S @3; Z @4; Z* @3; C,D @2.
```

`typeLetRhs`/Lambda/App/freshening at reference `:48–83,166–207` yields:

```text
drop publication: Poly(3, Function(Z@4,B@3))
drop Name use:    Z -> Z*@3; B -> B (captured, at its boundary)
f Name in g:     o -> o (monomorphic, initializer still active)
f-y demand:      o <: Function(B,R)
negative extrusion into o@2:
  (C,B,+,2), (D,R,-,2)
  B <: C; D <: R; o <: Function(C,D)
drop application:
  Function(Z*,B) <: Function(R,S)
  R <: Z*; B <: S
g publication:  Poly(2, Function(B,S))
```

The named-drop fresh-use map is essential: the source z remains at 4 while
its use image is at 3. Replacing named drop by an inline Lambda would remove
that map and change its native introduction/publication history, even if a
smaller scalar inequality projection happened to match.

At g's two independent Names, the coherent maps are exactly:

| Operand | first `g 0`, in first initializer | second `g ()` |
| --- | --- | --- |
| B@3 | B0@3 | B1@2 |
| S@3 | S0@3 | S1@2 |
| C@2 | same C@2 | same C@2 |
| o@2 | not visited by this g-root graph; shared in the original store | same original store |
| R/Z*/D | not reachable from this published Function root | not reachable from this published Function root |

Reachable high B/S and their mutual bound references are copied using one
memo per use; C is stopped at the exact boundary. No fresh f lookup occurs
inside a copied g type graph. The original inner Call constraints remain in
the store despite R not being reachable from the selected publication root.
That root-reachability fact is not a theorem that complete source Call/effect
clauses may be dropped from Source Generalize.

The actual use and consumer relations are:

```text
int <: B0 <: S0 <: V0 <: int;
unit <: B1 <: S1 <: V1;
B0 <: C; B1 <: C;
Function(A,V1) <: o;
opposite-bound replay: C <: A; V1 <: D;
original ignored-result relations: D <: R <: Z*.
```

The first local annotation consumes V0 below int and exposes int for first's
scheme; it does not give a new g use. The first binder is unused but its
initializer/check constraints still run. The second g Name is a separate
instantiation after g publication, not an alias of the first.

After f installation, final Name f is an ordinary boundary-1 freshening at
level 1. In this finite completed graph it freshly maps o,A,V1,D,C to five
level-1 images. Thus o/C are shared **between the two g uses while f is
inferred**, not globally forever after f publication. The final f use does
not remove the already accumulated first/second constraints. answer publishes
the returned f image with boundary 0.

### 4.2 Additional open q_g/q_drop root analogue

Using `typeLetRhs(true,g/drop,...)` adds actual native equations:

```text
q_drop@4 with Function(Z@4,B@3) <: q_drop;
drop publication Poly(3,q_drop);
drop use q_drop -> q_drop*@3; Z -> Z*@3; B -> B;
q_g@3 with Function(B@3,S@3) <: q_g;
g publication Poly(2,q_g);
each g use freshly maps q_g as well as B/S; C remains C@2.
```

This finite run has 25 variables instead of the first run's 20. Its fresh
root maps differ, while its actual `f y` parent pairs still have formal B
and result R as parents and target 2. This is a useful discrimination of
the extra-root omission; it does not certify that either reference analogue
commutes with the candidate's facade and contextual operations.

### 4.3 Equality consistency: exactly which finite relation was checked

The independently transcribed original constrain/extrude/freshen rules
accept the first ordinary finite trace. A separate fresh run is then extended
with supplied equalities on its existing native rows, represented by both
subtype directions. `D=R` alone is consistent in that finite native store.
If the extended relation also asserts `C=B0` and `C=B1`, it requires:

```text
unit <: B1 = C = B0 <: S0 <: V0 <: int.
```

The checker reports precisely `cannot constrain unit <: int`. At the
completed ordinary cut, even inserting C<:B0 already replays the accumulated
unit lower bound on C into first's int consumer. This is the same joined
finite relation, not an assumption that both runtime calls complete.

This extension deliberately supplies use-image equality clauses. It is not
the original Scala algorithm, which has no intrusion, and is not an adopted
candidate operation/schedule. It does not prove that original equality at
initializer B transports to B0/B1 in source frames. The selected operation's
actual activation point and source publication transport remain independent.
No pre-Generalize equality or SCC readiness before F's later source-reference
edge is assumed. Delayed equality affecting only original B/C would be a
different finite presentation; it cannot be identified with this extension
without the owning transport law.

## 5. Current native four-port and facade producer/consumer correspondence

The following names are notation for actual source-owned rows, not additional
source Values. L_f/L_g/L_drop are initializer Lambda component roots, N_f and
N_drop are Name component facades, J is Group's value facade around R, H_g/H_f
are Block final-result facades. Formal B has its own parameter recipe row.

### 5.1 Why the f-y argument parent is B and the callee is a facade

`candidate_source.rs:220–226` selects
`CandidateEndpoint::Parameter(parameters[y])` for Name y. The initially
allocated occurrence value component is not that selected endpoint.
`shadow_apply.rs:1291–1307` turns this endpoint into the parameter-live row.
`candidate_source.rs:391–411` retains that same endpoint as the Apply
argument and `shadow_apply.rs:1312–1328` checks the recipe/source-input
agreement. `:1343–1385` creates the actual negative four-port Function demand
and records its NativeInterface before constraining it at `:1389–1405`.

By contrast, Name f selects a component endpoint and schedules
`Action::Link { endpoint: L_f, target: N_f }` because f is active
(`candidate_source.rs:375–387`). Its execution at `:660–666` and
`candidate_scheme.rs:1336–1344` admits/constrains **L_f+ <: N_f-** with
ordinary provenance. It is a directed bound, not a declaration of equality.
The original `f y` Apply first constrains N_f+, with demand argument B+ and
result R-. The propagated comparison against lower L_f is the source of a
target-2 crossing, when reached. No self-recursive f use captures a scheme
at this point.

For the exact unannotated y and unfused representatives, its demand ports are:

```text
negative Function(B@3 positive,
                  Name(y).effect@3 positive,
                  fresh invocation-effect@3 negative,
                  App(f-y).result R@3 negative).
```

Negative structural extrusion flips both argument ports and retains both
result-port polarities (`candidate_extrusion.rs:224–256`). Besides the
value pairs C/B and D/R at target 2, it can allocate actual effect-parent
pairs for the argument effect and invocation effect. Those effect ports may
not be silently dropped from the actual event's all-produced-pairs contract.
The two-port finite reference projection neither checks them nor says that
they are empty complete-Call interfaces.

`lib.rs:12411–12453` dispatches candidate extrusion using the receiving
row's current level and enqueues the rewritten comparison. Each wrong-level
row creates its copy at the requested target, records parent before selected
bound traversal and memoizes it (`candidate_extrusion.rs:89–126`). The
endpoint was already canonicalized; `candidate_intrusion.rs:171–220`
records the exact canonical row as Parent. Thus the argument pair's parent
is **rep(B)**, which is B if no prior representative change occurred. It is
not the Name(y) facade or Group's result row. Claiming unconditionally that
the original formal ordinal remains the canonical parent after arbitrary
prior merges would be stronger than this source evidence.

### 5.2 Directed facade edges and actual drop use

The relevant unmerged planned incidence is:

```text
active recursive f Name: L_f@2 <: N_f@3
actual f-y App: N_f <: negative Function(B, E_y, Q_fy, R)
Group argument: R@3 <: J@3
drop initializer: positive Function(Z@4, E_entry@4, E_return@4, B@3)
                  <: L_drop@4
published drop Name: fresh(L_drop,boundary=3,use=3) <: N_drop@3
actual drop App: N_drop <: negative Function(J, E_Group, Q_drop, S)
g Block result: S@3 <: H_g@3
g initializer: positive Function(B, E_g_entry, E_g_return, H_g) <: L_g@3
each published g Name: fresh(L_g,boundary=2,use=3 or 2) <: N_g_i
first App result: V0@3 <: int-negative annotation
f Block result: V1@2 <: H_f@2
f initializer: positive Function(A, E_f_entry, E_f_return, H_f) <: L_f@2
```

Group/Block edges come from `candidate_source.rs:430–443,462–471` and
`shadow_apply.rs:1331–1335`, with effect edges admitted separately. Group
stays a facade; only an Ascription peels parentheses at
`candidate_source.rs:229–244`. There is no Ascription around the `f y`
argument in this source. Local first's written binding annotation follows
the distinct LocalAnnotation path, not that peeling rule.

`lib.rs:11233–11366` actually creates Lambda's positive Function: the
unannotated formal is its own negative parameter row and the body Name y
uses the captured positive parameter B. Bare z gets an entry effect even
though its value is unused. entry and body effects constrain the returned
effect. Consequently the ignored argument computation has an actual effect
consumer; it is not erased by unused z. Function comparisons at
`lib.rs:12493–12536` reverse argument value/effect and preserve result
value/effect separately. The scalar consequence through drop is
`R <: J <: Z*` and `B <: S`, with original facades retained. It is not R=B.

g/drop's installer keeps their actual initializer roots and boundaries,
regardless of absence of self Names (`candidate_scheme.rs:1316–1334`).
Their uses capture the live graph and prepare one coherent fresh use at
`:1354–1382`. Local rows satisfy level>boundary and !non_generic
(`:301–321`); expansion stops at nonlocal rows (`:568–572`), and fresh-use
allocation canonicalizes and copies eligible rows to the actual use level
(`:981–1021`). Bounds are restored before the final fresh-root-to-Name link
(`:1500–1518`). This traces an active consumer, not just stored scheme fields.
The static evidence supports retaining B as an older drop capture and C as
an older g coordinate **when their representatives/metadata remain those
displayed**. It does not produce the complete final Rust fresh map for this
exact source after all context replay and current intrusion settlements.

`candidate_effect.rs:1126–1174` checks first's **whole** initializer below
the negative annotation, checks its computation-effect policy, then places
the positive annotation on a fresh exposure root. Only that paired annotation
is installed as first's local interface. This agrees with the finite analogue's
V0<:int consumer; effect checks/exposure-root incidence are outside it.

### 5.3 Actual replay consumer and remaining source qualification boundary

This route uses candidate one-sided bounds, not the legacy bidirectional
row-aging branch. `lib.rs:13744–13751` selects `candidate_apply_value` when
the candidate graph is present. `candidate_extrusion.rs:808–838` chooses
the correct level-directed owner, inserts the bound and invokes opposite
replay. `:763–804` creates the actual comparison from opposite bounds and
drives its contextual replay. Thus L_f's lower occurrence and N_f's later
upper demand have a real constraint transmission route; the parent pair
claim is not inferred solely from matching stored fields.

The current settlement owner at `candidate_intrusion.rs:358–487` still
walks type/effect bounds and Function ports and compares canonical parent/
copy endpoints in that graph. This is not the approved source-Value graph.
`candidate_call.rs:29–45` gives these Apply inputs the encompassing
`source.definition_root()` owner; for this LocalSource that is answer's
module definition owner, while f/g/drop have distinct local IDs. It does not
emit the selected local G/F occurrence association merely by containing
those operands. The approved syntactic origin of `f y` is g: it is in g's
body suffix after drop publication, not in drop's `lambda z.y` body. Resolved
f is the receiver. F references G through its final `g ()` expression. The
`g 0` occurrence belongs to first's separate initializer root and gives
First -> G; it is not another F-owned edge. G references F through this
actual App. Hence the full source graph has F -> G -> F independently of
First -> G. Copying a description supplies no new Value edge.

Native capture/replay above therefore does not establish actual approved
occurrence qualification, source-reference graph readiness at g installation,
an equality clause's complete source scope, or its transport to both incoming
g frames. `candidate_call.rs:88–130` explicitly separates required original
Gen-Call-0/whole-argument/receiver/result/future suppliers from this native
interface. No complete-source failure or all-source absence is concluded
from that boundary. The other lane owns registration/equality/source-law
construction; this note supplies its corrected native incidence target.

## 6. Finite checker, oracle independence, resources and coverage

`tools/research_exact_g_native.py` is a self-contained deterministic Python
transcription of the cited original scalar constructors. It imports no
existing candidate checker or conditional model and reads no expected
compiler output. Its AST is written explicitly from the fixed source;
there is no source parser. Assertions verify the absolute levels, both actual
parent pairs, named-drop capture/freshening, both g fresh maps, first's
initializer level/check, Group retention and final-f freshening. A separate
ordinary run checks the supplied finite equality extension. An additional
open-root analogue checks the root-map difference for self-visible g/drop.

Run, from the snapshot root:

```sh
python3 tools/research_exact_g_native.py
```

Observed: PASS, ordinary direct-Function analogue 20 variables, extra-root
analogue 25 variables; exact parent targets 2; first map at 3 and second map
at 2; equality extension rejects exactly `unit <: int`. The foreground tool
call completed within its 1-second polling interval. No build, Scala
execution, Rust execution, parser test, compiler mutation or source/test
expectation change occurred. No broad search, seed variation, random
enumeration or timing repetition was performed. It covers one fixed AST,
one finite ordinary native history and the explicitly supplied equality
extension, plus the single extra-root variant. It does not verify the source
rules it declares, the full four-port candidate, effects, complete Call,
all schedules, arbitrary histories, source preservation or principal schemes.

The oracle independence is limited and explicit: original operator rules
are grounded in Typer bodies rather than another local model; those same
reference rules are the subject of the native characterization. The Unit,
Group and annotated-let additions are supplied assumptions. The extra-root
run demonstrates differing maps; it is not independent validation of Rust
equivalence. Successful ordinary scalar inference supplies no latent runtime
termination proof. The checker is research evidence, not a production test.

Only one lightweight shell process ran at a time. Zero heavy processes,
builds, child agents or Git mutations. The pass was bounded by the assigned
30-minute ceiling; exact reasoning CPU/RSS/wall time was not instrumented.
The full pinned lib.rs was supplied by the parent during this pass with a
reported exact Git blob check; this worker read/hash-checked it and made no
Git identity claim about the .git-free snapshot on its own. No input was
changed by this worker. Writes stop at this frozen handoff.

## 7. Dependency hashes and one next action

| Direct source input | SHA-256 |
| --- | --- |
| reference Typer.scala | `f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9` |
| HIR local_source.rs | `906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed` |
| HIR module.rs | `943dcab6440ffb70061f08641afa13fa8b36c5689a326d07288b9593e17ba8f5` |
| candidate_source.rs | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| candidate_scheme.rs | `9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1` |
| shadow_apply.rs | `cbd2e0c49a3f1fbe3c5fc78a06d469faedf4aa261525b24a0c9584e9956c2411` |
| candidate_call.rs | `79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35` |
| candidate_extrusion.rs | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| candidate_intrusion.rs | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| candidate_effect.rs | `ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df` |
| candidate_context.rs | `4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987` |
| solver lib.rs | `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94` |
| active-root Call note | `88b1ce77c5d113972a252abb876529d13cbe6a1500e2497b72c22c4577627fbb` |
| nested allocation note | `f72404c661736ee9e0b6226dfc471724795836510c7aa3a0582d209be47f8dd9` |
| intrusion preservation note | `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271` |
| publication classification note | `34acd7db0abe25c0e3e2944c00be9c11a80815bb5bcd79fc37cf38724a105b65` |

One next action: the primary consumes these literal level/binder/facade
incidences in the separately owned complete source-equality transport
construction, retaining the named drop publication and both independent
g-use contexts. It must state whether any target-1 notation is relative,
and preserve actual source event scopes and all four native ports. If an
authentic transport yields the supplied shared-C finite extension above,
the existing authority process must adjudicate that contradiction. This
leaf recommends no compiler change, registration policy or activation schedule.

## Commit packet

- Exact leased paths: this note and `tools/research_exact_g_native.py`.
- Baseline: `38bda20257d58069097a3e42c358b6759fb26d58`; reference baseline above.
- Changed dependencies: none by this worker; parent supplied lib.rs during
  the pass with the reported pinned blob, then it was read and hash-checked.
- Claim/review status at original producer handoff: unreviewed bounded native characterization and current
  implementation observations; no source theorem, principality closure,
  source-qualified counterexample or production authority.
- Checks already run: exact bounded source/consumer reads; manual boundary,
  map and inequality derivation; finite deterministic checker; dependency
  SHA-256 and leased-file whitespace/integrity checks. Zero builds/compiler runs.
- Proposed checkpoint: `research: preserve exact named-drop native levels and incidence`.
- Shared-record deltas left to primary/curator: distinguish absolute target 2
  from relative target 1; keep named-drop capture/fresh map and first's higher
  initializer use; record direct formal B versus f/Group/local facade rows;
  distinguish runtime p_g(h) after f closure publication from active native
  f inference; retain complete Call/effect/equality transport, actual
  qualification/readiness, source admission and all parent A/B gates OPEN.

Subsequent independent bounded review and the First -> G ownership delta
both passed. The reviewed evidence checkpoint is
`0bae7392c350e0d66244aaf8ea2a502ff1d2aa78`. The
[consolidated source verdict and review](2026-10-13-exact-g-source-verdict-review.md)
records the exact scope and frozen hashes. Its original source task remains
NOT SOLVED; this native review is not source preservation or principality.
