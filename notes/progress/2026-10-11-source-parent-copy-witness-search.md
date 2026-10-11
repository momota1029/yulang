# Higher-order recursive argument: sibling-copy SCC without freshening

Date: 2026-10-11
Status: independently reviewed bounded native source-to-constructor derivation;
the separate Scala comparison is not covered by that review.
Original source/inference and qualifying parent/copy gates: **OPEN**.
Pinned compiler baseline: `faf5853fddccd120734d7a3355a1208e7d597eb3`.
Pinned ordinary reference: `9bae772624c23b52a93c1b226157e16898b4d9db`.
Exclusive lease: this file only; leaf, no children or Git mutations.

## Objective, authority and claim class

Search a distinct supported source construction for a genuine retained Value
extrusion parent/copy SCC, using actual Value payload references. The method is
static chronological tracing of HIR identities, source actions, polar copies,
and the replay consumers. This lane supplies complementary source evidence;
the primary's prover owns the constructive source-Generalize/Call obligation.

Governing sections: `notes/design/2026-10-10-parent-copy-scc-intrusion.md`,
“Direct decision”, “Selected operation and compiler responsibility”,
“Value-reference SCC clarification”, “Retained boundary”;
`notes/design/2026-10-10-local-self-recursive-binding.md`, “Selected source
behavior”, “Proposed source-to-solver seam”, “Required invariants and evidence”;
`notes/design/2026-10-11-yulang-inference-top-level-principles.md` §§1–3,
“Evaluation”, “Authority and integration”. The graph vertices are Value rows;
references include Function Value fields. Comparisons, lexical ancestry,
parent records, evidence and source-call metadata do not create graph edges.
Effect ports retain their separate obligations.

Workflow: `rules/design-authority.md` “Authority order”;
`rules/compiler-engineering.md` “Natural compiler behavior and proof-obligation
economy”, “Deterministic Simple-sub inference”; `rules/research-lab.md`
“One semantic baseline, explicit dependency invalidation”, “Evidence quality
and stopping unproductive loops”, “Writes, artifacts and review snapshots”;
`rules/git-concurrency.md` “Disjoint-file mode”. The `yulang-proofs` skill
supplies constructor/consumer separation. No new language choice is made.

Inputs read: the reviewed ancestor-call note and source audit, and the prior
native Value parent/copy reachability proof. Their general rank result is not
used to derive this finite graph. The earlier untracked
`source-qualified-value-parent-copy-scc` artifact is absent from the pinned
baseline and was not read or used. The primary confirmed that this exact
higher-order argument construction does not duplicate the active prover lane.

**Bounded conditional characterization:** this construction creates both
polar copies of one original call-result parent. Its late recursive Function
replay forms an SCC containing those sibling copies, before any fresh local
use. The original parent remains outside. It supplies neither a qualifying
parent/copy witness nor a semantic counterexample. No all-source conclusion,
intrusion redundancy, soundness, principality or normal-progress theorem follows.

Explicit premises:

1. The displayed source is lowered by the existing parameterized local-binding
   HIR route to the stated Name/Apply/Lambda/Block identities. Exact parsing
   and HIR admission of this program were not executed.
2. The private candidate route starts normally; allocation and identity checks
   succeed, with no extra annotations, injected bounds, shadowing, prior Value
   equality, or reused failed session.
3. The named intrinsic actions and their actual contextual replay children
   complete before dependent actions. Their producer/consumer owners are
   identified below; whole-run termination, contextual eligibility and complete
   Call are not proved by this hypothesis.
4. The inspected four Value-bound arrays and contained Function ports are the
   emitted graph under consideration. Their adequacy for every required source
   dependency remains the original open semantic premise.

Failure of these premises limits the derivation; it imposes no source restriction.

## Fixed source and first owning constructors

```yulang
my host z = {
  my outer x = {
    my g y = outer g;
    x
  };
  outer
}
```

Unlike the previous `outer y; g` candidate, the call argument is the helper's
active own binding and outer returns its own formal. There is no returned-helper
use. The analyzed cut is after outer's Lambda and its named children complete,
before host's final published-outer use. Thus no Value fresh-use reconstruction
occurs in this cut. This is a small source candidate, not a claim of global
syntactic minimality or an executed witness.

HIR `crates/yu-hir/src/module/local_source.rs:329–373` temporarily installs
each parameterized local's self identity before its parameters/body, restores
the lexical stack and then publishes. Name lookup at `:637–647` uses that
stack before module fallback. Therefore the two Names in `outer g` resolve to
active local outer and active local g respectively; `x` resolves to outer's
formal. There is no local mutual-recursive group or polymorphic recursive use.

All solver locators below are under `crates/yu-solver/src/`.

| Coordinate | Owner | Level |
| --- | --- | --- |
| F, X, B | outer Lambda, formal x, body Block | 2 |
| G, Y | g Lambda and formal y | 3 |
| N, K, A | outer callee Name, self-g argument Name, Apply result | 3 |
| C, R, U, V | genuine polar extrusion copies described below | 2 |

`candidate_source.rs:251–305` gives these levels: root traversal begins at 1,
each Block initializer increases once, and Lambda preserves the level of its
body. Parameter Names use their actual parameter endpoints (`:209–216`).
Active local Names emit Link rather than capture/freshening (`:381–388`);
the executor admits those links at `:665–669`. Install follows intrinsic
initializer actions (`:307–327`) and records a live root/boundary without a
Value edge (`candidate_scheme.rs:1316–1334`). G is installed but never used
through its scheme in the analyzed cut.

## Chronological payload construction

### 1. The recursive call genuinely extrudes its argument and result

Link(F,N) physically puts F in N.lower because N has the higher level.
Link(G,K), at equal level 3, physically puts K in G.upper. Both writes use
`candidate_apply_value`, `candidate_extrusion.rs:808–834`.
Actual references: **N → F**, **G → K**. K is a Name occurrence, not yet
an extrusion child of G.

Apply generation retains exact N,K,A (`candidate_source.rs:394–411`).
`shadow_apply.rs:1331–1408` builds and admits negative Function(K,A), with
the actual separate Effect ports and a retained NativeInterface. N.upper
stores that Function without copying its level-3 ports: **N → K,A**.
N's lower F activates F against this demand (`candidate_replay_bound`,
`candidate_extrusion.rs:763–802`). Structural admission extrudes the negative
Function to F's level 2 before insertion (`lib.rs:12412–12454`).

| Recorded creation event | Parent's new physical payload | Copy's selected snapshot |
| --- | --- | --- |
| C = positive copy of K at 2 | K.upper contains C | C.lower initially empty |
| R = negative copy of A at 2 | A.lower contains R | R.upper initially empty |

`candidate_extrusion.rs:83–172` snapshots the selected side, allocates the
copy, calls `retain_extrusion_parent` and inserts the one-sided parent link.
Function variance at `:220–250` makes argument positive and result negative
for this demand. Reconstruction at `:325–355` installs Function(C,R) in
F.upper: **F → C,R**. The original Function(K,A) remains on N.

### 2. Late self Function replay produces the opposite result copy

The g Lambda owner constructs positive Function(Y,A) on G
(`candidate_source.rs:433–447`; `lib.rs:11233–11362`). G already has upper K,
so actual opposite-bound replay installs that Function on K. K already has
upper C, so the subsequent replay admits Function(Y,A) against C at level 2.

This is the decisive new constructor. Positive structural extrusion flips
the argument polarity and preserves the result polarity:

| Recorded creation event | Parent's new payload | Copy's selected snapshot |
| --- | --- | --- |
| U = negative copy of Y at 2 | Y.lower contains U | U.upper initially empty |
| V = positive copy of A at 2 | A.upper contains V | V.lower contains R |

A already has lower R from step 1; the positive extrusion copies precisely
that lower side. R is already at target 2 and is retained unchanged.
`Work::Bound`, `candidate_extrusion.rs:308–325`, installs R in V.lower and
transports its actual bound origins. The resulting Function(U,V) is inserted
in C.lower: **C → U,V**, **V → R**. A is the recorded original parent of
both R and V. These are genuine separate polarity/operation creation events,
not fresh-use copies. No comparison-direction edge or family metadata is used.

Extrusion's raw insertion does not itself enqueue every existing opposite
product. This trace does not assume it adds R → V from A's existing two sides.
The later sibling cycle below uses a different actual replay chain.

### 3. Returning x closes the sibling SCC through actual lower replay

The Block's final Name x uses parameter endpoint X. Its Group relation admits
X against B (`candidate_source.rs:459–467`; `shadow_apply.rs:1327–1330`).
At equal level 2 this stores B in X.upper: **X → B**.

Outer's late Lambda installs positive Function(X,B) in F.lower.
Replaying against F's copied upper Function(C,R) yields Value children
**C <: X** and **B <: R** (`lib.rs:12493–12530`), alongside two separate
Effect children. These direct admissions store X in C.upper and R in B.upper.
C's existing positive Function(U,V) then propagates through actual opposite
bounds to X, from X to B, and from B to R. If B's upper R arrives after its
lower Function, upper replay owns the last child; if before, lower replay owns
it. Either completed named product gives R.lower containing Function(U,V).
No port exceeds the receiver level, so this chain creates no new Value parent.

Replay ownership is concrete: `candidate_insert_bound_with_evidence`,
`candidate_extrusion.rs:445–501`, retains origins before physical append;
`candidate_replay_bound:763–802` selects opposite bounds and their BoundKeys;
`candidate_context_begin_replay`, `candidate_context.rs:2911–2987`, forms
their retained fiber products; the consumer at `:3060–3101` queues typed
children, and structural dispatch owns the actual Function admission.
Execution/eligibility of the whole chain remains premise 3, rather than an
inference from physical lists alone.

At this cut the relevant contracted Value projection is:

| Owner | Referenced rows |
| --- | --- |
| N₃ | F₂, K₃, A₃ |
| G₃ | K₃, Y₃, A₃ |
| K₃ | C₂, Y₃, A₃ |
| Y₃ | U₂ |
| A₃ | R₂, V₂ |
| F₂ | X₂, B₂, C₂, R₂ |
| C₂ | X₂, U₂, V₂ |
| X₂ | B₂, U₂, V₂ |
| B₂ | R₂, U₂, V₂ |
| R₂ | U₂, V₂ |
| V₂ | R₂ |
| U₂ | none |

Function steps are contracted through stored structural nodes. Effect payloads
are separate; their inspected adjacency has no return to Value rows
(`candidate_intrusion.rs:416–468`). Thus **R → Function(U,V) → V → R**
is a genuine sibling-copy SCC. Its reached rows are exactly {R,V,U}; it cannot
return to original A. C reaches {C,X,B,R,U,V}, excluding original K.
U has no route to original Y. None of recorded (C,K), (R,A), (U,Y), (V,A)
qualifies. This is direct enumeration of this fixed graph, not generalization
from rank. The selected qualifier consults the actual creation records
(`candidate_intrusion.rs:477–491`); it does not substitute siblings for parents.

## Source judgment and earliest absent edge

For the ordinary Value preorder, erase only the separate Effect obligations.
The exact unannotated source skeleton is:

```text
λz. let rec outer = λx. (let rec g = λy. outer g in x) in outer
```

Pinned reference `Typer.scala:48–73,106–159` uses the open monomorphic G
directly as argument; native K is its administrative Name interface. The
reference demand F <: Function(G,A) creates positive C from G and negative R
from A. The later Function(Y,A) <: G replay creates negative U from Y and
positive V from A, with V.lower containing R. The outer Function(X,X) demand
gives C <: X <: R and therefore R.lower contains Function(U,V). It has the
same R/V sibling cycle, without native K/B rows and without a fresh use of g.
The reference has no parent records or intrusion implementation.

The original native call judgment is entailed in the Value preorder by

```text
K <: C, R <: A, F <: Function(C,R)
```

because arrow variance gives Function(C,R) <: Function(K,A). Further source
constraints give G <: K <: C <: X <: B <: R <: A and Function(Y,A) <: G,
hence Function(Y,A) <: A: the recursive returned-g Value dependency.
The reconstructed lower Function is related by U <: Y and A <: V, giving
Function(Y,A) <: Function(U,V) <: R <: A. This bounded entailment does not
require A=V, G=K or equality of a parent with its polar approximation.
It does not prove the joint native Call/effect judgment, complete source
acceptance or general extrusion/generalization correctness.

For the candidate claim that R's lower Function returns to original A, the
earliest absent edge is at **positive structural extrusion of Function(Y,A)
into C**: its result field is V, not A. The constructor retains A.upper=[V]
and V.lower=[R], with no V→A payload. The self argument avoids the previous
freshening obstruction but reaches this distinct polar reconstruction seam.
No source-required omitted original-parent edge has been established here;
the displayed source Value inequalities already express the recursive
dependency via the shared approximations. Parent records and NativeInterface
data do not fill the absent edge.

The reference is an independently maintained codebase for these constructor
facts, not an independent oracle for Yulang semantics. Both analyses share the
chosen lexical skeleton, ordinary levels and Value arrow preorder. Native
effects, administrative interfaces, contextual replay and complete Call remain
additional obligations. No supplied-transition checker or runtime oracle ran.

## Coverage, blocker and next action

Coverage: one active outer local, one active helper self occurrence passed as
a higher-order argument, genuine positive/negative result copies, outer formal
return and the completed pre-publication Value replay cut. The source contains
ordinary local installation; it contains no generalized helper use before the
cut. Subsequent live capture/freshening of outer is explicitly untraced.
No annotations, operations, module recursion, deeper binding chains,
non-generic mutations, error continuation, failed-state reuse, seeds/ranges,
mutation variants or executable cases were searched.

What this falsifies: this exact candidate does not force a qualifying
parent/copy SCC merely by passing the active self binding, obtaining two polar
copies, and closing their sibling cycle. It does not falsify the original
existential/all-source obligation or certify the adequacy of emitted payloads.

Precise remaining blocker: establish at its source/semantic owner whether a
supported construction **requires original-parent identity after actual polar
reconstruction**, beyond the generated joint inequalities and live scheme
sharing, and whether every required consumer preserves that dependency.
Repeated family diagrams, another result-copy cycle, or another rank probe
would leave this premise untouched. The requirement is A/B when needed for
correct inference; an unrestricted family converse is C, and reading parent
metadata as adjacency would introduce incorrect reconstruction debt D.

Recommended next action: hand this exact pre-freshening sibling construction
to the existing prover's source-Generalize/Call necessity packet, asking it to
connect the displayed joint inequalities to the original required semantic
dependency. Keep the original theorem OPEN; no further equivalent witness
search is recommended without a newly justified source premise.

## Independent native-source review

An independent `compiler_referee` traced the fixed source through HIR identity
and levels, all four actual Value extrusion events, polarity and Function
reconstruction, replay ownership, the projected Value-reference SCC, and
recorded parent qualification. It found no blocking, major, or minor issue in
those bounded native claims. The review confirms the sibling cycle
`R → Function(U,V) → V → R`, with no original extrusion parent in that SCC,
and confirms the positive reconstruction creates V without a payload edge
`V → A`. It did not review the separate pinned Scala comparison because that
reference path was unavailable to the reviewer. Exact source parsing,
completion of contextual replay, complete Call/effect semantics, and the
universal source bridge remain open.

## Static checks, resources and frozen dependencies

Commands: bounded `cat`, `sed -n`, `rg -n`, `sha256sum`; read-only
`git status --short`, `git rev-parse HEAD`, explicit-path
`git diff --name-only faf5853fd -- <dependencies>`; reference `git rev-parse`
and explicit-path diff against its pin. Compiler/authority/note dependency
comparison returned no paths; reference HEAD equals its pin and Typer comparison
returned no paths. One `git show` confirmed the untracked prior trace is absent
from baseline; its live contents were not consumed. A guessed
`notes/theory/INDEX.md` search locator was absent; no claim depends on it.
Some broad initial captures were truncated; decisive constructors were reread
with narrower captures. These commands are static evidence, not execution.

Only this leased note was authored. No compiler/test edit, build, probe,
Oracle, formatter, benchmark, model-policy change, child launch, or Git mutation
occurred. At most four short read shells ran concurrently initially; zero
heavyweight or compute-probe processes, zero samples. Aggregate utility process
count, peak CPU/RSS and exact elapsed wall time were not measured; no numeric
per-leaf CPU/RAM/time budget was supplied. Independent review is recorded
above and is owned by the primary. This producer does not certify its own
result.

Frozen direct SHA-256 dependencies:

```text
906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed  crates/yu-hir/src/module/local_source.rs
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49  crates/yu-solver/src/candidate_source.rs
fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0  crates/yu-solver/src/candidate_extrusion.rs
c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94  crates/yu-solver/src/lib.rs
9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1  crates/yu-solver/src/candidate_scheme.rs
aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0  crates/yu-solver/src/candidate_intrusion.rs
4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987  crates/yu-solver/src/candidate_context.rs
230ed70cc8575016967cdf16c6c814544b25e45b0fc687d6c89f0d38e8fb5cd6  crates/yu-solver/src/shadow_apply.rs
2f08967e8f0477a1dacda62a211c620cd9cc3b80d476412b4c1e3d60506040c0  notes/design/2026-10-10-parent-copy-scc-intrusion.md
38d42183fdc4f2c0136112d8b305816241d8f449367b473e4de3a5135dc49895  notes/design/2026-10-10-local-self-recursive-binding.md
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389  notes/design/2026-10-11-yulang-inference-top-level-principles.md
e532893e3c2c26aa24695f9b57108ef0ee794ff8c2cefd39fcf309b606ff1871  notes/theory/2026-10-11-ancestor-call-extrusion-scc.md
5930376647e6bde7b20bb72b714174afad4792f1d18fa14aa187d2d1d82dafe5  notes/progress/2026-10-11-ancestor-call-extrusion-source-audit.md
964f85a47142956929147857f69887fea8344989724041994ac534d59668835f  notes/theory/2026-10-11-value-parent-copy-reachability-proof.md
f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9  simple-sub-reference/shared/src/main/scala/simplesub/Typer.scala
```

No dependency was changed by this worker. Writes stop at submission of this
frozen artifact; subsequent review repair requires the primary's new packet.

## Commit packet

- Exact leased path: `notes/progress/2026-10-11-source-parent-copy-witness-search.md`.
- Baseline SHA: `faf5853fddccd120734d7a3355a1208e7d597eb3`.
- Changed dependency hashes: none; direct snapshots above match the pinned
  compiler baseline/reference.
- Review status: independently reviewed bounded native source-constructor
  characterization; separate Scala comparison not reviewed; original parent
  gate OPEN, no implementation authority.
- Checks already run: narrow HIR/solver/reference constructor and consumer
  reads, exact dependency comparisons and SHA-256 capture; no execution.
- Proposed message: `research: trace higher-order recursion through sibling extrusion copies`.
- Shared-record deltas intentionally left for primary/curator: record the
  pre-freshening R/V sibling SCC, actual four parent events, earliest positive
  Function reconstruction seam, and open source-Generalize/Call necessity
  premise. No task/index/authority/theory map/question-board bundle was edited.
