# Active ancestor call: extrusion and returned-helper source audit

Date: 2026-10-11.
Status: **superseded for semantic SCC conclusions**. This bounded native
payload trace did not establish the intended source-value reference graph.
Original source/inference adequacy and authentic parent/copy SCC gates: **OPEN**.
Compiler baseline: `330d5432aff4b1f9655d501e17a9eefb7e75e098`.
Exclusive lease: this file; leaf, no further delegation.

## Objective, authority and method

Audit `my outer x = { my g y = outer y; g }` through actual HIR lexical
identity, candidate source levels, Apply demand, extrusion, local publication,
capture, reconstruction and stored Value references. The primary fixed the
source-local placement explicitly:

```yulang
my host z = { my outer x = { my g y = outer y; g }; outer }
```

This places `outer` under the approved parameterized-local self rule. It is
one ancestor, one helper, one recursive application and one returned helper
use. Removing the helper/application/returned use loses a required part of
this particular family. This is structural minimization, not a claim of
globally shortest syntax or an executed witness.

The governing sections are `2026-10-10-parent-copy-scc-intrusion.md`, “Direct
decision”, “Selected operation and compiler responsibility”, “Value-reference
SCC clarification” and “Retained boundary”; `2026-10-10-local-self-recursive-
binding.md`, “Selected source behavior”, “Proposed source-to-solver seam” and
“Required invariants and evidence”; and `2026-10-11-yulang-inference-top-level-
principles.md` §§1–3 and “Authority and integration”. File names in this
paragraph are under `notes/design/`. References in stored Value payloads
define the graph. Subtype comparisons, lexical ancestry, extrusion provenance,
evidence snapshots and fresh-use transport metadata do not themselves add
Value reference edges.

Rules read: `research-lab.md`, `design-authority.md`, `git-concurrency.md`,
`agent-orchestration.md` and `orchestration-budget.md`. The relevant laboratory
clauses are “One semantic baseline, explicit dependency invalidation”,
“Evidence quality and stopping unproductive loops” and “Writes, artifacts and
review snapshots”; the concurrency clause is “Disjoint-file mode”. The
`yulang-proofs` skill supplies the producer/consumer correspondence discipline.
The primary owns constructive proof dispatch and independent review; this lane
does not re-prove the rank argument or certify its own output.

Latest Value notes pin the compiler baseline above. Read-only `git diff
--quiet BASELINE -- <eight compiler/HIR dependencies>` returned zero for all
listed source dependencies. Inspected HEAD at startup was
`9d2bdce2f9c1cb4d619f4c5889b84ebd5e48c009`; intervening record commits are not
treated as compiler changes. The current accepted Value-reference clarification
has a different hash from the baseline decision file; both hashes are below.

The existing source-qualified recursive-application note already traces a
helper call prefix and a later *application* of that helper. This audit reuses
the same actual owners for that prefix, and isolates the different continuation
that returns `g` directly. It does not claim another independent attack on the
prefix. The returned-ancestor note instead uses `g y = outer`, with no Apply:
that body really retains `outer`; the present body returns an Apply result.

## Claim class and explicit premises

**Bounded conditional source-to-constructor derivation.** For this source
shape and the ordinary schedule below, the recursive call creates genuine
Value extrusion pairs, but the returned helper creates a cycle containing a
freshened result coordinate rather than the original extrusion parent. No
qualifying parent/copy SCC is produced by this traced continuation.

Premises:

1. Parsing/HIR produces the displayed unannotated, parameterized local
   bindings, one Apply and the indicated Name resolutions. Existing HIR
   self-recursion fixtures were read as corroboration; this exact source was
   not parsed or executed.
2. The private candidate route is enabled; ordinary source scheduling,
   allocation and identity checks succeed. All rows begin with ordinary
   generic metadata. No injected mutation, reused failed session, annotation,
   unrelated bound or prior Value equality changes these endpoints.
3. Named Value admissions, restoration and replay children complete before
   the subsequent dependent source action/capture. The code supplies their
   owners, but this note does not prove all contextual replay eligibility,
   complete Call, whole-run termination or successful source acceptance.
4. The current four Value-bound arrays and contained Function ports are the
   graph inspected here. Their completeness as the language's entire required
   source Value-reference relation remains the original OPEN semantic premise.

Failure of a premise limits the derivation; it is not a new source restriction.
This is neither an all-source theorem nor a semantic counterexample.

## Independent review

An independent `compiler_referee` checked the active local identity, source
levels, actual extrusion events, fresh capture, replay owners, projected SCC,
and the stated missing-reference seam. It found no blocking, major, or minor
finding in this bounded derivation. The review confirmed that A* is allocated
as a fresh Value row with the retained shared R, without a Value payload
reference back to original A. Exact parsing, completed contextual replay, and
semantic completeness of the selected Value graph remain unverified; the
original theorem stays **OPEN**.

## HIR identity, source level and chronological owners

Let F be `outer`'s Lambda/initializer row, X its formal, B its body Block,
G `g`'s Lambda/initializer row, Y its formal, N the callee Name `outer`, A the
Apply result `outer y`, and J the returned Name `g`.

| Coordinates | Level | Reason |
| --- | --- | --- |
| host formal and host body; final published `outer` use | 1 | Root schedule starts at 1; Lambda preserves level. |
| F, X, B, J | 2 | host Block's initializer raises level once. |
| G, Y, N, A | 3 | B's initializer raises level once again. |
| C, R, G*, Y*, A* | 2 | Demand extrusion or `g` fresh-use allocation described below. |

HIR `crates/yu-hir/src/module/local_source.rs:320–373` temporarily installs a
parameterized local's self identity before parameters/body, and restores then
publishes afterward. `:637–647` resolves the latest lexical binding before
module namespace lookup. `:819–829` preserves sequential initializer order.
Thus N resolves to the same `HirLocalId` as F while F is active; `g` and `y`
do not shadow `outer`. `y` resolves to the actual Y parameter. J resolves to
published `g`. The final host-body `outer` resolves to published `outer`.

Candidate scheduling `candidate_source.rs:251–305` assigns the levels above
and retains active initializer endpoints. Formal Names use the parameter
endpoint directly (`:210–216`). N emits ordinary Link(F,N), rather than a
LocalScheme capture (`:381–388`); the link runs at `:665–669`. Both g and outer
Install actions follow their intrinsic initializer actions (`:307–327`).

### 1. Real extrusion at the recursive application

Link(F,N) installs F in N's `direct_lower_rows`: N is the higher-level receiver
(`candidate_extrusion.rs:808–834`). Actual reference: **N → F**.

Apply generation (`candidate_source.rs:394–411`) retains actual callee N,
argument Y and result A. `shadow_apply.rs:1331–1362` constructs the negative
Function demand D with Value ports **Y,A**, and records it in the retained
NativeInterface before admission (`:1364–1408`). Effect ports are also present
and remain separate. Admitting N against D at level 3 does not copy Y or A;
N stores D in its upper structural array. Actual references: **N → Y,A**,
contracted through D. The NativeInterface result A is source-call data, not
an additional stored Value-reference edge from F or a copy back to A.

N's existing lower F and new upper D generate replay F against D
(`candidate_extrusion.rs:763–802`). Structural dispatch extrudes the negative
Function at F's level 2 before installing it (`lib.rs:12412–12454`). Function
argument variance is positive here; result variance is negative
(`candidate_extrusion.rs:220–250`). Consequently:

| Genuine event | Physical parent payload | Copy snapshot at creation |
| --- | --- | --- |
| positive extrusion of Y₃ to C₂ | Y.upper contains C | C.lower copies Y's then-empty lower side |
| negative extrusion of A₃ to R₂ | A.lower contains R | R.upper copies A's then-empty upper side |

`candidate_extrusion.rs:83–172` allocates each copy, records its actual parent
at `:121–123`, and inserts the one-sided link. This is real extrusion, distinct
from lexical ancestry or later freshening. Function reconstruction
(`:325–355`) replaces D's Value fields by C,R, yielding D'. F's upper array
stores D', hence **F → C,R**; it does not store the original Y,A fields.
The original D remains on N. No source action puts N into F's payload.

### 2. g's Function and publication expose its Apply result

The Lambda owner builds positive Function(Y,A), because A is g's final body
endpoint (`candidate_source.rs:433–447`; `lib.rs:11233–11362`). The constructor
is inserted on G at level 3 with no Value port extrusion: **G → Y,A**.

Install stores `LocalScheme {root=G,boundary=2}`
(`candidate_scheme.rs:1320–1334`). It inserts no Value reference. Capture for
J starts from G (`:1373–1374`) and expands local rows above boundary 2
(`:300–326,568–609,743–790`). Its relevant Value set is exactly:

```text
local:  G₃, Y₃, A₃
shared: C₂, R₂
G.lower = [Function⁺(Y,A)]
Y.upper = [C]
A.lower = [R]
```

Shared rows retain their session identity and capture stops at them
(`candidate_scheme.rs:570–574`). N and F are not reached from this root: the
callee occurrence points toward F and its demand; the Apply result A stores
R, with no stored callee pointer. Original lexical resolution remains correct,
but does not make the callee a result payload.

`prepare_candidate_fresh_use` (`:1009–1021`) allocates G*,Y*,A* at J's use
level 2 and leaves C,R unchanged. It does not record extrusion parents.
Function reconstruction uses mapped terms (`:1115–1157`); restoration
preserves each captured owner's side (`:1226–1266,1505–1514`). Therefore:

```text
G*.lower = [Function⁺(Y*,A*)]
Y*.upper = [C]
A*.lower = [R]
```

The fresh root is linked to J after restoration (`:1516–1518`). With both at
level 2, the direct row bound is G*.upper=[J]; ordinary replay installs the
positive Function on J. The final Block relation similarly links J to B,
stores J.upper=[B], and replays that positive Function onto B. These are
actual stored references, not arrows chosen from comparison direction.

### 3. outer's late Lambda makes an ordinary cycle

F's Lambda constructor has Value ports X,B. Replaying this positive Function
against F's retained D' decomposes to C against X and B against R
(`lib.rs:12493–12530`). All four rows are level 2. Direct row admission stores
C.upper=[X] and B.upper=[R]. Replaying B's positive Function onto R installs
Function⁺(Y*,A*) in R.lower. Its ports already have level 2, so this replay
creates no new Value extrusion parent.

The complete relevant Value projection at this cut is below. Each Function
step is contracted through its actual structural node. Effect children and
metadata are omitted from the table; the inspected Effect adjacency has no
return to a Value row (`candidate_intrusion.rs:416–468`).

| Owner | Referenced Value rows |
| --- | --- |
| N₃ | F₂, Y₃, A₃ |
| G₃ | Y₃, A₃ |
| Y₃ | C₂ |
| A₃ | R₂ |
| F₂ | X₂, B₂, C₂, R₂ |
| G*₂ | Y*₂, A*₂, J₂ |
| J₂ | Y*₂, A*₂, B₂ |
| B₂ | Y*₂, A*₂, R₂ |
| Y*₂ | C₂ |
| A*₂ | R₂ |
| C₂ | X₂ |
| R₂ | Y*₂, A*₂ |
| X₂ | none |

There is a real **R₂ → A*₂ → R₂** cycle, contracted through the positive
Function on R for the first step. A* is a fresh-use copy of A, not the original
parent of R. C reaches only X. R reaches {R,A*,Y*,C,X}; neither Y₃ nor A₃ is
reachable from a retained copy. Hence neither recorded pair (Y₃,C₂) nor
(A₃,R₂) is in one SCC at this cut. This is direct enumeration of this fixed
constructor graph, not another general level/rank argument.

The final host-body published `outer` use captures F at boundary 1 and allocates
the reached level-2 rows at use level 1. Its Value capture reaches
{F,X,B,C,R,Y*,A*}, without N,G,Y₃,A₃,J,G*. All of these captured Value rows are
local and ordinary generic under the premises; Function fields and stored
bounds are reconstructed using their fresh level-1 counterparts. This
freshening neither records a new extrusion parent nor restores an original
level-3 Y/A reference. The host Lambda receives that returned-use endpoint.
No later caller or unrelated top-level body is included in this cut.

## Earliest missing edge and reference comparison

For an alleged R/A qualifying cycle, **A₃ → R₂** exists. The earliest missing
step in the proposed `R → helper-result → A` return route is the claim that
the returned helper's result port remains A₃. Fresh-use allocation explicitly
replaces it by A*₂ and restores **A*₂ → R₂**, with no **A*₂ → A₃** reference.
The subsequently installed Function on R has A*, not A. Likewise Y is
replaced by Y*, and the argument copy C receives X, not Y₃. Parent metadata,
captured `source_bound` evidence and the original demand on N do not fill
either missing payload edge.

The ordinary reference is pinned at
`9bae772624c23b52a93c1b226157e16898b4d9db`. Only relevant
`shared/src/main/scala/simplesub/Typer.scala` behavior is compared. Represent
the local source skeleton by recursive `Let outer = Lam x (Let g = Lam y
(App outer y) in g) in outer`, at surrounding level 1. No claim is made
that the reference accepts Yulang syntax or has Yulang's effects/Call contract.

`typeLetRhs` allocates recursive outer's open variable at level 2 (`:48–55`);
App returns a fresh result at level 3 and constrains outer with Function(Y,A)
(`:69–73`). Negative Function extrusion flips argument polarity and preserves
result polarity (`:138–159`): Y.upper receives C₂ and A.lower receives R₂,
then outer.upper receives Function(C,R). `freshenAbove(2, Function(Y,A))`
(`:170–194`) creates Y*,A* at current level 2, copies both bounds and stops
at C,R. Constraining outer's inferred Function(X,Function(Y*,A*)) against its
stored demand gives C.upper=[X] and R.lower=[Function(Y*,A*)], with
A*.lower=[R]. The same ordinary cycle excludes original A₃.

The reference has no retained extrusion-parent/intrusion operation. It is an
independent codebase corroborating this bounded polarity-copy/freshening
behavior, not an independent oracle for Yulang source semantics. Both analyses
share the selected lexical scope, level and unannotated App/Function skeleton.
Native administrative N/G/J/B rows and four-port effects remain separate
correspondence obligations. No new reference meaning is adopted.

Literal top-level `my outer x = ...` is a distinct HIR path: `outer` resolves
ModuleDef via namespace fallback (`local_source.rs:637–647`), schedules Module
(`candidate_source.rs:376–380`), and an internal SCC use routes via
`route_candidate_open_use`/`route_internal` (`candidate_scheme.rs:855–889,
938–946`). Published module uses use the graph route. This audit does not
substitute those paths for the source-local self contract or claim their full
owner correspondence. The local host placement avoids that ambiguity.

## Coverage, checks, resources and frozen dependencies

Commands: bounded `cat`, `sed -n`, `rg -n`, `rg --files`, `sha256sum`; read-only
`git rev-parse HEAD`, `git diff --quiet BASELINE -- <explicit dependencies>`,
and `git show BASELINE:<decision> | sha256sum`. Compiler dependency comparisons
returned zero. Reference HEAD equals the pinned reference revision and its
Typer baseline comparison returned zero. No Git mutation occurred.

No parse, executable experiment, test, build, Oracle, mutation, seed/range
enumeration, benchmark, formatter or child launch ran. One initial guessed
reference path did not exist; `rg --files` located Typer and it was read.
Some batched output captures were truncated; decisive constructor sections
were reread narrowly. The leased note is the only authored path.

Coverage: one local ancestor, one helper, unannotated Y argument, returned
helper and the final published ancestor use. Omitted: deeper families,
additional source bindings/callers, annotated formals/ascriptions, operations,
non-generic metadata introduced by other paths, failed-session reuse, complete
module recursion and executable Call/effect eligibility. Exact source parsing,
completed replay, source semantic adequacy, soundness, principality, hygiene,
normal inference progress, production cutover and F5 replacement are unverified.

Resources: one reasoning leaf; zero compute probes/build/test processes and
zero benchmark samples. Short read/hash utilities only. Peak CPU/RSS, total
utility process count and exact wall time were not measured; the assignment
specified no numeric CPU/RAM/wall-time budget. No resource escalation occurred.

SHA-256 direct dependencies at freeze:

```text
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49  crates/yu-solver/src/candidate_source.rs
9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1  crates/yu-solver/src/candidate_scheme.rs
fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0  crates/yu-solver/src/candidate_extrusion.rs
c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94  crates/yu-solver/src/lib.rs
4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987  crates/yu-solver/src/candidate_context.rs
aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0  crates/yu-solver/src/candidate_intrusion.rs
230ed70cc8575016967cdf16c6c814544b25e45b0fc687d6c89f0d38e8fb5cd6  crates/yu-solver/src/shadow_apply.rs
906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed  crates/yu-hir/src/module/local_source.rs
2f08967e8f0477a1dacda62a211c620cd9cc3b80d476412b4c1e3d60506040c0  notes/design/2026-10-10-parent-copy-scc-intrusion.md
38d42183fdc4f2c0136112d8b305816241d8f449367b473e4de3a5135dc49895  notes/design/2026-10-10-local-self-recursive-binding.md
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389  notes/design/2026-10-11-yulang-inference-top-level-principles.md
f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9  simple-sub-reference/shared/src/main/scala/simplesub/Typer.scala
```

The baseline intrusion decision hash was
`8ae4348a93dce6df1852a34b2294ebc5e4e256d8b018c1f6eaad42c502470a8e`;
its current hash records the primary's already accepted clarification.
No dependency was changed by this worker. This file is now frozen for review.

Recommended next action: adjudicate this exact result-identity seam against the
original source adequacy premise. A further witness search must supply an
independently justified original parent reference that survives actual
extrusion/fresh-use reconstruction; another returned-helper diagram or rank
probe would leave that premise untouched.

## Commit packet

- Exact leased path: `notes/progress/2026-10-11-ancestor-call-extrusion-source-audit.md`.
- Baseline SHA: `330d5432aff4b1f9655d501e17a9eefb7e75e098`.
- Changed dependency hashes: only the accepted authority snapshot differs from
  baseline, as recorded above; no worker-authored dependency change.
- Review status: frozen, unreviewed research-only conditional constructor
  derivation; no parent theorem closure or implementation authority.
- Checks already run: narrow source/authority/reference reads, dependency hashes
  and baseline equality checks; no execution or compiler verification.
- Proposed message: `research: audit ancestor-call extrusion and returned-helper identities`.
- Shared-record deltas left for primary/curator: record the genuine (Y,C)/(A,R)
  events, the R/A* ordinary cycle and exact missing original-parent return
  reference; preserve source adequacy and authentic qualifying-pair gates OPEN.
  No task/index/authority/theory/question-board bundle was edited.

## Later graph-definition correction

The user clarified that source-value references such as `host → outer` belong
to the intended graph. This note projects solver-stored bound payloads and
therefore omits semantic source-value adjacency. Its SCC comparison does not
answer the intrusion question. Keep the constructor trace as operational
evidence only; treat its semantic SCC qualification as superseded.
