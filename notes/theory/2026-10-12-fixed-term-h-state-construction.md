# Fixed recursive core: executable H refinement and immutable-local obstruction

Date: 2026-10-12
Status: independently reviewed source-to-research-machine refinement and exact reference obstruction;
proposed transitions are non-authoritative; no production or parent-gate closure
Assigned baseline: `5e7ffb735fc1a829d03890ebfd353e17ad7ca342`
Branch: `research/simple-sub-intrusion`
Reference: LPTK/simple-sub `9bae772624c23b52a93c1b226157e16898b4d9db`
Exclusive lease: this file; leaf, no delegation or Git operations

Independent review and integration scope: [fixed-term H review](../progress/2026-10-12-fixed-term-h-review.md).

## 1. Result and frozen claim

The decisive addition is section 8: a constructive refinement proof for the
frozen `tools/research_fixed_term_h_machine.py`. Its actual full-cell/row
traversal and specific consumers realize the finite pushforward for this
term from the checker's **empty** initial context. The script executes
pairwise H; section 6 relates that timing to the batch specification.

The unmodified Scala reference cannot perform H: its inner Lambda parameter
and App result remain the original immutable references B and R. A finite
extension with explicit live continuation slots can perform H without changing
any original row's level. This note constructs that extension's transition;
it does not assume H and then call the ensuing run a construction of H.

Fix exactly:

```text
let rec odd = lambda n_outer.
  let rec even = lambda n_inner. odd n_inner
  in even n_outer
in odd
```

Source Values O, E, a, b and the two App-result Values are distinct from type
rows o, e, A, B, R, C, D and S. The original boundaries are 1 for E and 0
for O. The selected occurrence has origin E, receiver O and actual pairs
`(C,B,+,1)`, `(D,R,-,1)`. No equality o=e or source-binder identification
is imposed. The term, event and both pairs are fixed, up to injective renaming
of every allocated identity.

The precise constructive claim is: from the native pre-resumption state below,
the explicitly defined finite transition produces the H postcondition in
sections 4–5 of `2026-10-12-fixed-term-intrusion-quotient-proof.md`, including
its live context, low anchors, structural operands, two raw comparison keys,
and historical polar memo. The same action can be placed pairwise just after
each native selected-bound copy, before its Variable return. Section 6 proves
these timings commute for this exact empty-opposite-bound prefix.

Concurrent remote checkpoint `d12c80b0bf5ea1c55eb24b27fc1de0dfe9b6706a`
added reviewed `2026-10-12-fixed-term-quotient-transition-proof.md` (Q) and
`../progress/2026-10-12-fixed-term-quotient-transition-falsification.md`.
Sections 3–7 retain the specification needed to state the refinement and
substantially overlap Q; they are not claimed as new closure. The new owner
evidence is section 8's concrete handler/field proof, section 2's original
immutable-local obstruction and section 6's exact timing lemma. The reviewed
omitted-Lambda-parameter discriminator is covered by the param-cell read.
No candidate compiler bridge follows from this result.

All new choices are **PROPOSED / NON-AUTHORITATIVE**: source incidence
availability before inference, explicit continuation representation, event
certificate plumbing, low-anchor semantic representation, active-row transport,
and its timing. Only the operation/qualification and original source owners
are already selected. No general equality-preservation, all-source soundness,
principality, progress/termination, complete Call/effects, Yulang correspondence,
arbitrary future-use history or F5 cutover theorem is claimed.

## 2. Actual source obstruction

The scratch reference bodies are byte-exact copies of immutable upstream
[Typer.scala](https://github.com/LPTK/simple-sub/blob/9bae772624c23b52a93c1b226157e16898b4d9db/shared/src/main/scala/simplesub/Typer.scala)
and
[TypeSimplifier.scala](https://github.com/LPTK/simple-sub/blob/9bae772624c23b52a93c1b226157e16898b4d9db/shared/src/main/scala/simplesub/TypeSimplifier.scala).
The scratch retrieval directory is not a repository deliverable. Relevant Typer
lines are recursive roots/publication 48–55, Var/Lam/App/Let 59–83, raw cache 88–103,
variance/insertion/replay/extrusion resumption 106–126, polar copying 134–156,
freshening 166–188 and 199–207, immutable structures/levels 209–233.

During the inner Lambda, line 65 binds `val param` to B at level 2. During
the inner App, line 60's lazy `res` is forced to R at level 2 by line 71;
line 72 returns that same R. Negative extrusion at 122 makes C and D but
does not assign to either constructor-local binding. Therefore line 67
necessarily builds `Function(B,R)`, whose level is 2 by 209–210. The immutable
context map also continues to bind `n_inner` to B (18,66); monomorphic
instantiation returns `this` (207).

This is an exact nonreachability proof in the original transition language,
not an argument from absence of a name such as "intrude". Fresh allocations
return new objects; legal mutable operations update only bound lists,
extrusion/freshening maps and caches. None replaces constructor-local `param`
or `res`, Function children, context-map entries captured by these calls, or
Variable.level (224). By induction over every legal bound-list mutation
between allocation and the Lambda return, those two local references stay
B/R and their immutable levels stay 2. Additional calls to ordinary
`constrain` do not change this induction.

Consequently no such original-rule sequence realizes H's requirement that
the same live inner constructor return `Function(C,D)` at level 1. This
obstructs H for the unmodified representation; it is **not** a source typing
counterexample, or a contradiction to the user-selected equality operation.
The stock term still has the independently derived principal exterior
`Top -> Bot`. Equality of scalar solutions is insufficient to replace the
actual objects used by the level/freshening consumers.

The smallest necessary new capability is replacement/indirection of live
type references at constructor/context/consumer boundaries. This note uses
an explicit finite pushforward rather than presuming that arbitrary Scala
locals automatically canonicalize. "Smallest" here means this unavoidable
capability, not a proved globally optimal implementation or general cost law.

## 3. Explicit state and original-rule prefix

Use a first-order machine state

```text
Sigma = (pc, kappa, Env, Rows, Active, q, K, M, Delta, Use)
```

Its fields have deliberately different types:

| Field | Meaning and transformation domain |
| --- | --- |
| `pc`, `kappa` | Current instruction and finite frames with enumerated **LiveType** slots |
| `Env` | Finite lexical maps of original binder identities to Mono(t) or Poly(boundary,t); type bodies are LiveType |
| `Rows` | Allocated raw row records: immutable ID/level and mutable lower/upper lists |
| `Active` | Raw rows that own future semantic bound reads/writes |
| `q` | Type-row representative map; initially identity |
| `K` | A comparison call's set of **RawPair** snapshots, containing raw immutable structural children |
| `M` | Extrusion-local map **RawPolarKey** `(parent ID,polarity)` to actual allocated copy ID |
| `Delta` | **RawEvent**: source origin/receiver, target level and original produced pairs |
| `Use` | Fresh-use-local unsigned raw-ID map; absent at the H cut |

Raw ID/level, RawPair, RawPolarKey and RawEvent are separate state field
types, not implicit LiveType slots. Transport is undefined on those fields.
They retain history even when a row leaves Active. A historical row's bound
lists are then historical too; no later semantic consumer is allowed to read
them as an active owner. All future semantic owners are explicitly in Active.
This last condition is established below by transporting the complete finite
root set, rather than assumed as an all-source discipline.

LiveType is a finite structural operand: `v | Prim(name) | F(t,u)` for this
term and its unused initial builtins. Constructing F computes maximum child level from
its actual children, as the reference does; a transported F is rebuilt,
never a reused Function object with an obsolete lazy level. The frame tags
needed here are:

```text
LetBody(binder,body,env,boundary)       -- awaits scheme then original body
RecDone(root,boundary)                -- awaits initializer and constrain
LamDone(param,env,level)              -- awaits body and builds F(param,body)
AppDone(result,callee,arg,env,level)   -- awaits comparison, returns result
CompareResume(lhs,rhs,Kref)           -- awaits extruded rhs then constrain
ExtFun(leftResult,rightInput,pol,target,Mref)
ExtVar(parentRaw,copyRaw,pol,target,Mref) -- provenance fields, completed branch
```

`root`, `param`, `result`, `callee`, `arg`, comparison operands,
ExtFun's type operands and environment type bodies are LiveType slots.
ExtVar's completed parent/copy provenance is raw; its returned copy is a
separate LiveType result slot. Boundary/level numbers, resolved binders,
syntax, source owner and K/M references are never type coordinates.
Unforced `lazy res` fields on other term calls are represented by
`Unforced(level)`: no row exists there, so transport leaves them unchanged.

Original inference is defunctionalized only to expose these already existing
locals: the instruction order, allocations, comparisons and publication
rules are those of 48–83. Before any proposed transport the machine is a
literal encoding of this fixed reference call stack, not a new constraint
generation rule.

Let Gamma0 be the initial reference context. Its unused builtin `if` contains
one preallocated row w at level 1 with empty bounds (23–32); all its other
leaves are primitives. Include w in Rows and Active as an unchanged spectator.
It is distinct from all seven relevant rows. The builtins contribute no Name,
constraint or event in this term. The exact source environments are:

```text
GammaO    = Gamma0 + odd:Mono(o)
GammaOA   = GammaO + n_outer:Mono(A)
GammaOAE  = GammaOA + even:Mono(e)
GammaOAEB = GammaOAE + n_inner:Mono(B)
```

At the instant native `extrude(F(B,R),false)` has returned F(C,D) but
`constrain(o,F(C,D))` has not started, the full type-bearing stack is,
bottom to top:

```text
LetBody(O, final odd, Gamma0, 0)
RecDone(o,0)
LamDone(A,GammaO,1)
LetBody(E, even n_outer, GammaOA,1)
RecDone(e,1)
LamDone(B,GammaOAE,2)
AppDone(R,o,B,GammaOAEB,2)
CompareResume(o,F(B,R),K)
returned operand = F(C,D)
```

The already finished Name evaluations have no waiting frame. Their retained
f_ty/a_ty are exactly AppDone.callee/arg. ExtFun/ExtVar frames are gone at
this batch cut; section 6 accounts for their additional slots at pairwise
cuts. This exhausts the original live type locals in the relevant 48–83 and
121–123 activations. Levels in LamDone/AppDone remain the *lexical inference
levels* 2 even when their eventual operand type has level 1.
No replay `foreach` continuation or selected-bound map traversal is suspended
at this cut: the first comparison's opposite bounds and both selected copied
lists were empty. Its sole pending solver continuation is CompareResume.

The complete relevant prefix store is:

| Row | Immutable level | Lower | Upper |
| --- | --- | --- | --- |
| o | 1 | [] | [] |
| A | 1 | [] | [] |
| e | 2 | [] | [] |
| B | 2 | [] | [C] |
| R | 2 | [D] | [] |
| C | 1 | [] | [] |
| D | 1 | [] | [] |

All seven relevant rows and spectator w are initially active; q is identity.
`K={(o,F(B,R))}`;
`M={(B,+)->C,(R,-)->D}`. Delta contains the original `(E,O,1)` occurrence
and its two pairs. No Use map exists yet. B's lower and R's upper lists
were empty at their selected-bound-copy reads; this is the decisive finite
fact used in the construction, not a generic empty-bound assumption.

## 4. Constructing the qualification certificate

**PROPOSED / NON-AUTHORITATIVE phase ordering:** allocate the finite source
Value identities and resolve Names before this type run. For this AST the
approved source ownership rules construct precisely

```text
O -> E,a     E -> O,b
inner App result -> O,b     outer App result -> E,a
```

The nested initializer changes the owning definition to E; the outer body
changes it back to O. The final odd is outside O's initializer. Each edge
targets its resolved original binder; neither copying nor subtype storage
adds or retargets an incidence. The two paths O->E and E->O certify the
same SCC, regardless of the remaining listed edges.

When inner App constructs its demand, its retained source owner is E and
its resolved callee is O. Pass `(delta,E,O)` as provenance for this actual
demand extrusion, record target level 1 when 122 invokes extrusion, and
append each pair when 147 allocates its actual copy. Thus Delta is produced
by specific constructors; it is not reconstructed from matching type IDs,
Function ports or bound directions. The active test consumes this certificate
and the computed source SCC, returning both original pair records.
Freshening has no Delta constructor. This is a concrete producer for this
finite extension; original Scala has neither this producer nor this test.
No new owner law is needed for any ambiguous wrapper in the fixed AST.

## 5. Finite pushforward transition T and its H postcondition

**PROPOSED / NON-AUTHORITATIVE transport rule.** From section 3's exact
prestate, define p on the seven relevant row IDs and spectator w by

```text
p(B)=C; p(R)=D; p(v)=v for v in {w,o,A,e,C,D}.
P(v)=p(v); P(F(t,u))=new F(P(t),P(u)).
P(Prim(name))=Prim(name), with native level 0.
P(Mono(t))=Mono(P(t)); P(Poly(k,t))=Poly(k,P(t)).
```

Perform one finite simultaneous transition, using the *old* lists as input:

1. Set q=p and Active to `{w,o,A,e,C,D}`. For each active anchor v set its
   lower list to the concatenation of `P(L(u))` over old rows u with p(u)=v;
   set its upper list analogously. The order within old lists is preserved;
   choose anchor list first, then absorbed parent list. For this prestate
   all anchor lists and all but two parent lists are empty, so ordering is
   immaterial and no duplicate-elimination policy is needed.
2. Apply P to every LiveType slot enumerated in section 3, every environment
   type body, and the returned F(C,D). Rebuild structural objects. Leave all
   other fields unchanged. Clear the inactive parent bounds after complete
   transfer; retain raw B/R IDs, immutable levels and Delta's direct-link
   provenance. No raw row ID or immutable level changes. Historical bounds
   have no second semantic owner. This is the script's retirement encoding.
3. For each merged class, enumerate all newly combined lower/upper products
   that require propagation. Here `[B=C]` has empty lower and `[R=D]` has
   empty upper. Both products are empty, so no replay is due at this action.
   This is a checked zero-length work list, not silently skipped propagation.
4. Resume CompareResume by calling the native comparison on its returned
   operand F(C,D) under the same K. The transported old rhs slot is no longer
   used for the extrusion retry; this is exactly the return data flow at 123.

The transition is fully defined without presupposing that any future read
canonicalizes. It takes a finite root/list/slot set, rewrites that set, and
then executes the specified consumer. The number of relevant row classes is five,
the number of absorbed rows is two, and the relevant input lists have two entries.
The sixth active class is unchanged spectator w with empty lists.
Environment maps are finite; the only changed binding is `n_inner:B -> C`.
There is no downward-dependency closure or new row allocation in T.

The computed active store *before* resumption is

```text
U(C)=[C]; L(D)=[D]; every other active list empty.
```

In particular the original parent links are included as self bounds by
pushforward. Both bound sides of both classes were processed, including their
empty sides. The transformed LamDone parameter is C; the AppDone result is
D and argument C; GammaOAEB now binds the *same original inner binder* to
Mono(C). All other environments and source identities are unchanged.
CompareResume's live rhs is F(C,D), as is the returned operand. Their
maximum child level is 1, because the objects' actual children are C and D.
B/R retain level 2 in historical allocation records, but are absent from every live
root and every active bound. Thus no future native consumer in this specified
run can accidentally generalize them. This proves root completeness at the
cut; it is not an unproved "all live reads canonicalize" premise.

K, M and Delta still contain the original B/R identities. Since Variable
has raw object equality and uid hash (223–233), and Function compares its
raw children (209), `(o,F(C,D))` is distinct from `(o,F(B,R))`. The cache
therefore admits the resumed key, stores it at 102, and inserts F(C,D)
into U(o) at 116. L(o) is empty. Its return completes AppDone with D.

Exactly the desired H cut is now obtained:

```text
active relevant level 1: o,A,C,D; active level 2: e
unchanged spectator w: level 1, empty bounds
U(o)=[F(C,D)]; U(C)=[C]; L(D)=[D]
all other active lists empty
K={(o,F(B,R)),(o,F(C,D))}
M={(B,+)->C,(R,-)->D}; original Delta and row levels retained
inner App returns D; inner Lam parameter C; inner context n_inner:Mono(C)
```

This is a direct calculation of T's postcondition. Identifying C with X and
D with Y gives every H item of the existing conditional note. The equality
is equality of the live semantic classes, not changed Scala object equality.
K is discarded only on the owning native comparison's return, normally.

If K were transported along with live operands, it would already contain
`(o,F(C,D))`; 101 would skip 116 and U(o) would remain empty. The typed field
separation therefore has an observable necessity in this execution; merely
putting the word "historical" on a canonicalized cache would not implement T.

## 6. Pairwise timing and batch timing commute here

The original H places each action after the direct parent link and selected
bound copying, before that Variable branch returns. At the first cut
(150–151), only C exists, U(B)=[C], and every other relevant list is empty.
Apply the one-class version p1(B)=C. It makes U(C)=[C] and transports
LamDone.param/AppDone.arg/the inner binding to C. AppDone.result remains R.
The completed ExtVar's raw `(B,C,+)` fields and M key remain unchanged.
The current ExtFun stores live leftResult=C and rightInput=R; both are
unchanged by p1. The original `ty` and consumed left input have no remaining
read after the left recursive return, so this machine discards them as exhausted operands.
Their raw history is retained in K/M/Delta, outside the live-slot domain.
ExtFun's complete remaining type-slot set is leftResult/rightInput; its frozen
raw cache snapshot remains F(B,R).

The next native branch depends only on R's immutable level 2, the target 1,
the absence of `(R,-)` in M, and U(R)=[]. None was changed by p1. It therefore
allocates exactly D at level 1, writes L(R)=[D], copies the empty U(R) into
U(D), and records `(R,-)->D`. Apply p2(R)=D after 153–154. It makes L(D)=[D]
and transports AppDone.result to D. The original parent R remains only in
completed raw provenance/cache records; ExtFun receives the returned D and
constructs F(C,D).

These two actions have disjoint row preimages and replace disjoint type
leaves, including inside shared structural slots;
the second native extrusion reads no changed first-class bound. Therefore
their pushforwards commute, p2 p1=p1 p2=p, and their empty product work lists
stay empty. Batch T after native F(C,D) return yields precisely the same
active lists, live slots, raw memo/event records and K. It allocates the same
rows in the same order. This proves equivalence to H's specified pairwise
cuts for this prefix only; it gives no general batching/scheduling law when
selected copied bounds are nonempty or mutually depend on the classes.

Exhaustiveness across the following finite execution is also checked directly.
At the cut the image of every live root/list lies in Active. Native Var
lookup subsequently uses only the transported environments; Lam/App/RecDone
use the enumerated transported slots; bound replay uses only active owners;
freshening reads those active bounds and adds only its fresh image IDs. These
are every constructor/consumer executed in section 7. K tests membership but
never emits its stored historical types as new comparison operands. M and
Delta have no subsequent semantic read in this run. Induction over the listed
steps therefore preserves absence of B/R from live operands. This finite
root argument establishes the transport-consumer bridge; it does not install
an extra all-source canonicalization assumption.

## 7. Subsequent consumers, levels and both fresh-use maps

This section checks the transported finite state remains the owning native
consumer's input. It is not the missing construction proof; T was already
defined and computed in section 5.

| Native owner | Input after T | Consequence |
| --- | --- | --- |
| inner Lam, 67 | transported param C and returned body D | actual F(C,D), level 1 |
| inner RecDone, 52 | F(C,D) <: e | L(e)=[F(C,D)], no upper replay |
| inner publication, 55 | boundary 1, root e | Poly(1,e), original boundary unchanged |
| outer even Name, 63/202 | freshenAbove(1,e), use level 1 | one e' at level 1; C/D retained |
| outer App, 71/116–117 | e' <: F(A,S) | U(e')=[F(A,S)], replay F(C,D) |
| Function replay, 106–108 | F(C,D) <: F(A,S) | A <: C; D <: S |
| D lower replay, 117 | D <: S from L(D)=[D] | identical raw pair already in this call's cache; stops |
| outer Lam/RecDone | F(A,S) <: o | L(o)=[F(A,S)], replay F(C,D) |
| Function replay | F(A,S) <: F(C,D) | C <: A; S <: D |

Every comparison endpoint/bound in the last four rows has level 1. No
further extrusion occurs. U(C)=[A,C], L(D)=[D], U(D)=[S], U(S)=[D],
U(A)=[C]. e/e' remain distinct roots; U(e)=[], L(e')=[F(C,D)]. The row
bound-level invariant 221–227 holds even on inactive historical B/R: their
cleared lists are empty; accepted links moved to C/D. No original row's immutable
level was lowered; the sole level-2 live root is e, storing a level-1 bound.

The E-use unsigned memo is exactly `{e->e'}`. No B'/R' can be allocated:
the only live bound visited is actual F(C,D), and both children satisfy
`level <= lim` at 168. No event/pair or Value incidence is created by this
map. This is actual consumer calculation, not merely semantic relabeling.

Outer publication is Poly(0,o). Its final Name creates a *different* unsigned
memo. The allocated order is o0,A0,C0,S0,D0: lower o first visits A and its
upper C; C's reversed upper traversal encounters its self then A, both
memoized. S then visits D; D's lower self and upper S reuse memo entries.
Finally upper o visits already memoized C0/D0. The map is

```text
{o->o0,A->A0,C->C0,S->S0,D->D0}
L(o0)=[F(A0,S0)]; U(o0)=[F(C0,D0)]
U(A0)=[C0]; U(C0)=[A0,C0]
L(D0)=[D0]; U(D0)=[S0]; U(S0)=[D0]
```

All five fresh rows have level 0. e/e' and historical B/R are unreachable
from o's active bounds and are not visited. q may remain a historical map
for the original IDs; no equality is added among distinct fresh-use frames.
For the new IDs it is identity. Each relevant consumer now receives actual
transported objects with correct native levels.

`TypeSimplifier.scala:102–157` gives root vars `{o0}`, argument closure
`{A0,C0}`, positive result `{S0}`, and no recursive compact variable. Its
231–239 single-polarity removal and 308–313 empty polar coalescing give
Theta=`Top -> Bot`. The stock note section 5 independently supplies the
fixed source typing and universal finite-derivation principal order of Theta.
Thus this particular extended execution computes that source principal
exterior. It does not preserve every stock internal assignment; that stronger
claim is explicitly not the original interface-preservation obligation.

## 8. Concrete source-to-executable-machine refinement

Frozen script SHA-256:
`9d08adba56e2bc48a834821b1fe434ce6e39f8d7d90c08ebefd83846d352e50d`.
Repaired companion evidence SHA-256:
`150c4972da8103ea2a2462288307863fe712393154db61b330cec2d491877c3f`.
All Python line numbers below name this exact script. The theorem concerns
`Machine("H", Source())`, not either mutation mode. No target store or
unspecified transport owner is a premise.

### 8.1 Context, observations and projection

`__init__` (19–27) starts `envs=[{}]`. The executable theorem explicitly has
an empty initial context; remove section 3's spectator w. Allocation is then
o=0,A=1,e=2,B=3,R=4,C=5,D=6. Its relation to the default-context stock prefix
is conservative projection: none of this term's five Name occurrences uses a builtin.
Deleting Gamma0's unused entries and disconnected w commutes with every
executed stock constructor, lookup, comparison, level test and copy. Shift
raw IDs injectively to account for the missing prior allocation. Raw equality
and hashing preserve the relevant distinctions. This relates the relevant
stock states; it does **not** say Python accepts primitive-containing builtin
cells. It represents variable/Function tuples only. The abstract P(Prim)=Prim
spectator lift is outside this executable theorem.

Define observation Rho by dereferencing each live frame's operand-cell index
in cells and each environment scheme's body-cell index likewise. Omit dead
cells and report-only snapshots. Rows with retired=None own active bounds;
retired 3->5 and 4->6 record the two classes at this cut. Preserve raw row
IDs/levels, event, cache and map fields in their own historical sorts. Rho is
a field interpretation, not an added canonical-read rule. It relates the
concrete representation to the specification after inactive bounds are
cleared, as already stated in section 5.

### 8.2 Exhaustive operand coverage, including raw-ordinal exceptions

Inspection of every step branch (70–145), constrain (147–190) and copy
(192–233) gives this persistent semantic inventory:

| Family | Cell-index fields read/written as types | Other references |
| --- | --- | --- |
| eval | out | env indexes a map; term is resolved syntax |
| lam_return | param,body,out | no direct type-row ordinal |
| app_arg / app_compare | fun,arg,out | env; result allocated at app_compare |
| app_return | result,out | value is a source Value |
| let_rhs_done / let_publish | root,body,out | env, source owner and lexical level |
| constrain / constrain_return | left,right | cache index, source origin/receiver |
| extrude / freshen | src,out | memo index; extrusion polarity |
| function_return | arg,res,out | no direct type-row ordinal |
| copy_bounds_return | out and every sides entry | **raw type-row parent/target ordinals**, event and polarity |
| environment scheme | body | lim=None or original boundary |

Row bound lists are the other direct type-payload owners. Source IDs, levels
and indexes have distinct meanings by field use; coincident integer encodings
do not make them type coordinates. `run` pops one frame, completes step, then
processes the next (29–35). No suspended host recursion/generator/closure
holds an additional future inferred type.

The raw parent/target exception is discharged at the actual two cuts. Current
copy_bounds_return is already popped when it calls H. For the first action
its fields are parent=B,target=C; for the second parent=R,target=D. Lines
135–141 have already completed all row accesses, written the copy's output
cell and appended the original pair. After H this handler exits with no
further typed access through those ordinals. Both selected side lists were
empty. At the first action the pending R operation is an extrude frame with
src/out cells; it has not yet allocated D or constructed another
copy_bounds_return. The remaining function_return has only cell indexes.
At the second action there is no other pending bound-copy frame. Future
freshening frames use active e/o/A/C/S/D and their new copies, never B/R.
Thus no future raw ordinal consumer escapes the rewrite in this execution.
There is no universal claim that all possible typed frame fields are cells.

H traverses all cells at 260, rather than just `live()`'s filtered roles
(298–301). Before/after displays include Lam formal, App result and App demand;
changed_cells lists all changed indexes. These are **not full cell snapshots**.
Coverage follows from that complete traversal and this handler census, not
from the selected diagnostic display.

### 8.3 The actual H loop realizes the one-class pushforward

`copy` memoizes raw parent/polar keys before child work (209–217), inserts the
native direct link and selects the appropriate opposite bounds (218–224).
B positive gives U(B)=[C] and empty selected L(B); R negative gives L(R)=[D]
and empty selected U(R). copy_bounds_return installs selected lists, writes
the returned-copy cell, records its actual pair and calls H (134–143).
This is **pairwise activation before the Function return**, not batch.

For parent p and anchor c, local q (244–249) fixes None, replaces exactly
`("v",p)` by `("v",c)`, fixes other row leaves and rebuilds Function tuples
from mapped children. Structural induction on the finite tuple proves it
equals the specified one-class P. Bounds are not recursively unfolded by q,
so store cycles do not interfere with this induction.

Lines 251–254 concatenate both parent bound sides into the existing anchor,
clear the parent and mark retirement. Lines 255–257 map both lists of every
row; lines 259–260 map every cell in mode H. For each operand-cell index i,
its observed value afterward is therefore exactly P(old cells[i]); each
class side contains all its old payloads mapped by P. These loop bodies prove
`Rho(after h)=T_pair(Rho(before h))`; the assertions do not serve as premises.
After the first call U(C)=[C]; after the second L(D)=[D] as well. Both lower/
upper products are empty by the computed prefix. Thus line 269's bounded
guard is satisfied; its assertion is not a general proof of union propagation.
Section 6 applies to these actual pairwise calls and relates them to batch Q.

This is a terminating finite imperative action, not an atomic-H oracle.
The calls scan respectively six and seven row records and a finite cells
list whose length cannot change inside h. Each q call strictly descends
finite tuple children or stops at None/a variable, without following row
bounds. Report/snapshot loops also range over finite lists. Thus the action
terminates before the next handler. Later self-bound replay stops at the
native raw cache, and fresheners memoize before following cyclic bounds.

Shared references are preserved: environment stores a body-cell index
(54–58), and the Lambda frame and formal binding share its param index
(83–86). A Name may already have copied the same tuple into a distinct
argument cell (75–77); traversal updates both. Environment maps need no
dictionary changes: unchanged indexes dereference transformed cells. The
slice assignment preserves the cells list and all indexes. The forced lazy
App result is concretely allocated after argument evaluation at 107, captured
by app_return at 109, transformed by H, and read at 114. It is therefore D.
Lambda return independently reads param C and body D at 102 and constructs
actual F(C,D); a repaired context is not substituted for this local read.

Function tuples have no level cache. level (51–52) derives the maximum from
actual child allocation levels; F(C,D) has level 1. H does not call fresh
or assign to levels/row.level. It preserves the same levels tuple object
(239–240,267–268); B/R keep immutable level 2. The historical F(B,R) tuple
therefore still has level 2, while its transported live cell has level 1.

### 8.4 Historical exclusion and authentic source qualification

constrain captures and admits a key before extrusion (148–159,179–190).
H mode never maps those key sets (261–266) or polar memo entries (242,266).
Even when a cell and K formerly referenced the same immutable tuple, assigning
a new tuple into cells[i] cannot mutate K's old tuple. The original B/R
parent keys and C/D copy values remain raw. H does not rewrite event records:
the caller appended actual parent/copy IDs, polarity and immutable target
level at 140–141. Counts, labels, trace strings and diagnostic snapshots are
report-only; no subsequent semantic handler consumes old snapshot operands.

Source.__init__ fixes the AST then resolves/walks it (386–392).
Source.resolve (400–412) retains lexical binder identities; fragment_names
(414–418) restricts Apply membership to Name/App; walk (420–432) changes
ownership for nested initializers and restores the surrounding body owner.
The result is exactly O->E,a; E->O,b and the two App incidences. same_scc
(443–444) tests mutual reachability. eval sets owner=E inside its initializer
(97–98); app_compare passes that owner and resolved direct callee O
(110–112); extrusion stores them with its polar map/event (183–186).
Thus the source-backed eligibility and actual pair inputs to H are built by
specific executable handlers, not inferred from bound adjacency. These are
proposed prepass/event additions with no corresponding original Scala owner.

### 8.5 Consumers and limits of native correspondence

function_return builds the demand from C/D output cells (132–133), and
constrain_return reschedules it under the same K (128–129,66–68). The old
key o<:F(B,R) differs from the new o<:F(C,D). Membership at 157 therefore
fails, 159 adds the new key, and 167–169 inserts F(C,D) in U(o). L(o) is
empty. canonical_cache instead explicitly maps K at 263 and skips insertion.
This derives the H first-App cut from executed code.

Suffix variance/insertion/replay use 164–178. LIFO pushes result before
argument (165–166), hence executes contravariant argument first. Reversed
bound push loops (171–178) similarly execute newest-first replay; queued
operands are cells, not suspended host iterators. This preserves exact native
order, left-variable priority and one cache across recursion for the section
7 comparisons. The variable identity shortcut (150) matches the identity
cases reached here. Rebuilding Function tuples preserves variable sharing
and structural equality, not necessarily host object-reference sharing.
The only Function/Function comparisons reached are F(C,D)<:F(A,S) and
F(A,S)<:F(C,D); their raw child pairs differ because A,C,S,D are distinct
allocations. All other comparisons have a variable operand. Therefore no
same-Function-object comparison occurs, and the reference's all-SimpleType
`lhs is rhs` shortcut adds no missing return in this trace. General Function
object-reference identity remains outside the correspondence.

Completion/publication (117–125) reads transported root/body cells and leaves
limits 1/0 unchanged. Each polymorphic Name creates a new unsigned map
(79–81). copy uses parent-only keys for freshening, records the memo before
children, copies both reversed lists, then restores newest-first order
(209–226,136–137). Consequently E's memo is e->e'; final O's distinct memo
copies o/A/C/S/D once each. The early level test can retain the entire
F(C,D) at 195; this agrees with the specification's retained children.
Freshening creates no extrusion occurrence or Value edge.

compact_interface (318–380) implements only the reached variable/Function
subset; it rejects repeated compact recursion and both-polarity variables.
Section 7 independently calculates its particular compact layer. The source
principal theorem is the stock note's separate argument, not a checker
assertion. Primary reports one rerun exit 0 with report hash
`29a957e5210b034c021b825d9006d36e883ba695b054333338a3d082fd85dcaf`.
This leaf did not execute another run or use successful assertions as proof.

The proved refinement is to this **executable research representation** for
one empty-context term and its exact native prefix/suffix. It does not supply
an implementation bridge to immutable Scala or the candidate compiler. No
arbitrary context, alias history, nonempty product or general algorithm is
certified. All new H/prepass/explicit-cell choices remain non-authoritative.

## 9. Status, residual obligations, checks and commit packet

Constructed and independently reviewed within the fixed-term scope: section 8's concrete executable
handler/field refinement, the immutable-local obstruction and timing lemma;
the overlapping finite state representation,
complete live-slot pushforward, raw-history separation, exact H postcondition,
pairwise/batch commutation for the empty prefix, and native continuation through
the two original boundaries. The unmodified Scala obstruction is a separate
source-level result. No compiler source changed and no current implementation
is asserted to implement this transition.

The original all-source parent gate remains OPEN. Exact residual obligations:

1. Adoption/production implementation of proposed precomputation, certificate
   plumbing and live-reference transport. Section 8 establishes owners in the
   research script only; candidate correspondence is a separate primary lane.
2. Qualified equality preservation and progress for other source terms,
   especially nonempty opposite-bound products, interacting mixed-level
   classes, nontrivial suspended work and cache histories.
3. A general leveled representation/transport rule and its complexity;
   this finite low-anchor construction does not prove downward closure.
4. General sharing, polymorphic fresh-use independence, complete Call/effects,
   source/Yulang admission, abnormal paths, termination and cutover obligations.

The method changed from specifying H/Q to proving concrete full-cell/row
traversal and consumer reads;
the missing general operation is A/B, and retaining source/event facts at
their actual constructors addresses D. No gate is reclassified to evade it.
One next action: derive the actual candidate call/extrusion occurrence and its
complete fixed-source consumer trace, then relate its retained slots to this
proved finite model. Any proposed production representation or schedule still
requires the existing design-authority path.

Checks: static full reads of governing four design documents, the conditional
H note, stock proof, required rules/prover config and decisive reference bodies;
full frozen executable/evidence inspection and concurrent Q/falsification;
hand execution of the two pair actions, batch equivalence, cache discriminator,
complete live roots, level tests, both map traversals and final compact output.
Some combined output captures truncated; decisive content was reread in bounded
windows. The initial snapshot lacked `tasks/current.md`; subsequent remote
records were not used as proof premises. No Git commands, builds, tests, Scala execution, additional executable
probe, measurements, delegation, external/user contact, compiler edits or other
path writes occurred. At most one lightweight command process ran at a time;
exact CPU/RSS and elapsed reasoning time are unmeasured. Requested routing was
generic prover-equivalent Sol/high; observed runtime model/effort metadata is
unknown. This producer does not certify its own result.

Commit packet:

- Exact path: `notes/theory/2026-10-12-fixed-term-h-state-construction.md`.
- Baseline: `5e7ffb735fc1a829d03890ebfd353e17ad7ca342`; reference pinned above.
- Claim/review: independently reviewed concrete research-machine refinement and exact original
  representation obstruction; parent gates OPEN, no authority adoption.
- Checks: static owners and all finite calculations above; zero builds/tests.
- Proposed checkpoint: `research: refine fixed-term H into concrete cell and frame handlers`.
- Shared deltas deferred to primary/curator: record that H has a concrete
  executable finite research realization and cannot occur in unchanged Scala locals;
  retain adoption/source correspondence and all-source semantic gates OPEN.
- Direct dependency hashes are recorded below after the final read-only
  integrity check; no input was edited by this leaf. Writes stop on handoff;
  independent review and all Git integration belong to the primary.

Direct dependency SHA-256 snapshots:

| Input | SHA-256 |
| --- | --- |
| Top-level inference principles | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| Parent-copy SCC decision | `6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b` |
| Value/type association | `28a0c2aa196912e59e9adb9e62e30d171a03fc485d36314db02c5e13b74f6775` |
| Copied-row ownership | `7c170c346eeeabca50afe254425eba0c83995cb5e61bf257290ce2757c78bfbd` |
| Conditional H note | `6d2e79c2113562422d06e8250e6830b60fe8b9006b18746b4f23362ac044e6c1` |
| Stock fixed-term proof | `d6366f55b855647303cd0851cbab46036d8180058157f4eae9a2e3445f00c921` |
| Original Typer.scala | `f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9` |
| Original TypeSimplifier.scala | `618b63f63e71c31890eb36cb18be474bfd31732173c159132306f0e14dc37d2b` |
| Reviewed concurrent Q | `7ed3086921c18bb823b622977a73bc4c1d867c30b64116658194af28ef0582a9` |
| Reviewed concurrent falsification | `05bb046e66b51eb0b091c68723fb46d8f4897b2702d14a5e842c629621373674` |
| Frozen executable machine | `9d08adba56e2bc48a834821b1fe434ce6e39f8d7d90c08ebefd83846d352e50d` |
| Repaired machine evidence, including review metadata | `150c4972da8103ea2a2462288307863fe712393154db61b330cec2d491877c3f` |
