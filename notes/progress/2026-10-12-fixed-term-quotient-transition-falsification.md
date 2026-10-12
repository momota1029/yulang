# Fixed-term quotient transition: dependency closure and constructor omission

Date: 2026-10-12
Status: independently reviewed research; bounded source-state characterization
and representation discriminator; no established intrusion transition or parent closure
Assigned baseline: `5e7ffb735fc1a829d03890ebfd353e17ad7ca342`
Branch supplied by the primary: `research/simple-sub-intrusion`
Exclusive lease: this file only; researcher leaf, no delegation

## Objective, method and claim boundary

Independently enumerate the dependencies of the two qualified equalities
`C=B`, `D=R` at the extrusion-return cut of the exact fixed term in
[`fixed-term conditional continuation`](../theory/2026-10-12-fixed-term-intrusion-quotient-proof.md),
sections 1–6. Attack the proposed transition without assuming its action H.
The method is a static census of the actual reference constructors, stack
locals, heap fields and subsequent consumers, followed by a minimal omitted
constructor trace. No supplied equality-transition checker is used as an oracle.

The term is exactly:

```text
let rec odd = lambda n_outer.
  let rec even = lambda n_inner. odd n_inner
  in even n_outer
in odd
```

The accepted occurrence has source Value E, receiver Value O and actual pairs
`(C,B,+,1)`, `(D,R,-,1)`. Both qualify through the approved O/E Value SCC.
This packet accepts those equalities and keeps both original lexical scopes,
inner publication boundary 1 and outer boundary 0. It imposes no o=e equality.
Values O/E, formals and Apply results remain distinct source records.

**Result class:** bounded dependency-closure characterization for this
reference execution; a concrete failure of context-only continuation transport.
No counterexample to a complete quotient representation, the approved equalities
or the final source principal interface was found. The conclusion is not a
proof that an actual producer realizes H. Source construction/activation and
representation-to-consumer correspondence remain explicit missing premises.

The census assumes a private successful single-threaded inference of this term
in a fresh reference Typer with its stock builtins, no concurrent external
mutator or previously retained public type aliases, and the exact allocation
prefix supplied by the input. It excludes abnormal/diagnostic paths and arbitrary
future source/use histories. Stock builtins include an unused polymorphic row;
its allocation identity exists, but no Name in this term reaches it. Its bound
content does not enter the dependencies below. No level/sharing policy beyond
the investigated existing level-1 anchors is adopted.

## Governing sections and direct source owners

Authority is the exact selected operation, not candidate implementation law:

- Top-level inference principles sections 1–5.
- Parent-copy SCC design: **Selected operation and compiler responsibility**,
  **Apply-result source-fragment ownership**, **Nested Apply membership**,
  **Definition-root Value ownership**, **Retained boundary**.
- Value/type association: **Approved extrusion-event qualification**,
  **Definition-root origin for nested call-demand extrusion**,
  **Implementation and proof boundary**.
- Copied-row ownership: **Decision**, **Scope and proof boundary**.

These preserve occurrence provenance, scope and sharing, while leaving the
SCC scheduling point and transport representation unselected. The reference
has no Value-graph prepass or equality-state constructor. A candidate owner
audit cannot supply either missing operation by defining its own law.

The source root is
`/home/momota1029/rust/simple-sub-reference/shared/src/main/scala/simplesub/`.
Directly inspected owners are `Typer.scala` in full, `TypeSimplifier.scala`
sections for representation, canonicalization, simplification and coalescing,
and `TyperDebugging.scala` in full. Exact owner locations below use the unchanged
reference files. No compiler production files were edited or executed.

## Cut reconstructed from the native owners

Before the returned Function demand is compared again, the seven relevant raw
allocations are o,A,C,D at level 1 and e,B,R at level 2. Stock direct links are
`U(B)=[C]`, `L(R)=[D]`; all other relevant lists are empty at this cut.
The Function returned by extrusion is `F(C,D)`. The pending comparison cache is
`K={(o,F(B,R))}`; U(o) has not yet received the demand. The polar memo is
`M={(B,+)->C,(R,-)->D}`. The incoming raw Function's lazy level has already
been forced to 2 by the guard that selected extrusion.

There are two useful cuts: after both variable-copy cases have completed and
before `constrain(o,F(C,D))` (`Typer.scala:121–123`), or immediately before each
copy case returns (`:150–156`). The latter also has a transient partial state
after C is produced and before D exists. At that intermediate cut R remains
level 2 and is not yet identified with anything. The rest of the same extrude
Function frame still evaluates its original raw R child and produces D.
Neither direct-link copied-bound map iterates a nonempty opposite list here.
The completed-cut inventory below therefore also names those copy-case locals.

## Complete dependency census for the fixed cut

Read q as the candidate semantic view `q(B)=C`, `q(R)=D`, identity elsewhere.
This notation describes dependencies to be discharged; it does not assume an
owner that computes or applies q. X/Y below are the existing raw C/D anchors.

| Family | Actual retained state and owner | Required treatment or reason no transport is needed |
| --- | --- | --- |
| Resolved source identities | Original term, binders O/E, both formals, both Apply Values; source scope and ownership records | Preserve identities, resolved Name targets and lexical scopes. q acts on type coordinates only. Retain E/O occurrence and actual pair provenance; copying adds no Value edges. |
| Recursive initializer frames | Outer `typeLetRhs.e_ty=o`, inner `e_ty=e`; each has original `lvl` and immutable `ctx` (`Typer.scala:48–55`) | o/e are not union members. Their forthcoming `ty` results must be semantic descriptions; publication remains at 0/1. |
| Suspended Lambda frames | Outer `param=A`; inner `param=B`; pending `body_ty`; immutable contexts include inner `n_inner -> B` (`:64–67`) | A is unchanged. Inner param and every returned body type must consume representatives, including constructor locals independent of the context map. |
| Suspended App frame | Inner `f_ty=o`, `a_ty=B`, forced lazy `res=R`; original demand `F(B,R)` (`:60,68–72`) | f_ty unchanged. Both a_ty and the returned res are live type handles; future semantic consumers must see C/D. The already admitted raw demand remains available for historical K. |
| Other lazy result thunks | Every `typeTerm` invocation declares an unforced lazy `res` except the inner App's forced R (`:60`) | These thunks retain the original inference `lvl` and allocator; they have allocated no row and do not capture B/R as their result. Let/Lam/Var cases in this fixed execution never force them. Preserve their original level context; no q transport or additional allocation is needed. |
| Let/body context frames | Outer root and formal bindings; inner recursive root binding; suspended nested Let (`:81–83`) | Keep source binding names and scopes. Monomorphic scheme/type payloads must have semantic access to representatives. No inner published scheme exists yet. |
| Pending comparison | Incoming `lhs=o`, raw `rhs0=F(B,R)`, K; later local returned `rhs=F(C,D)` (`:88–126`) | Distinguish the admitted raw demand from its returned live demand. Resume the actual returned insertion. Do not turn a key recording in-process work into evidence of its completion. |
| Active extrusion frames | Raw parent `tv`, `pol`, `lvl=1`, allocated `nvs`; Function children B/R and intermediate returned C; M (`:134–156`) | Original parent/polar keys and produced pairs remain raw provenance. Semantic returns are C/D. At this cut the copied-bound `.map` lists are empty; no captured opposite-bound iterator survives. |
| Bound storage owners | B's upper C and R's lower D; empty C/D lists; o/e/A lists empty | Transfer both sides to their semantic class owners without loss: U(X)=[X], L(Y)=[Y]. Original direct links do not require `constrain(X,X)` to synthesize them. Neither union has a lower/upper cross-product here. |
| Structural descriptions and levels | Raw F(B,R), raw returned F(C,D); immutable `Variable.level`, lazy `Function.level` (`:209–227`) | Historical F(B,R) may keep raw children and cached level 2. Live Functions supplied to native level consumers require actual representative children, hence level 1. Do not mutate raw identity/hash/equality under existing map keys. |
| Literal constraint history | K holds raw `(o,F(B,R))`; Variable hash is uid, Function equality compares raw children (`:98–103,212–215,223–233`) | Preserve this literal pair. The native returned key `(o,F(C,D))` is distinct. Its insertion cannot be skipped solely because both demands denote the same semantic class description. |
| Polar memo/history | M uses raw `(B,+)`, `(R,-)` and raw produced C/D | Preserve parent identity, signs, occurrence and target level. Any semantic memo return must resolve its value; rekeying provenance by class is not this record's job. There is no second occurrence or later polar memo use in the fixed continuation. |
| Fresh allocation state | `freshCount`, each raw uid, immutable level, `asTypeVar` lazy field (`:164–165,223–233`) | Equality must not conflate historical uids or allocate an extra type row in this examined transition. The counter continues normally. `recursiveFlag` is not consulted by the selected canonicalization path. |
| Future publication and use maps | No use-freshening map exists at the event; future E use and final O use each create their own unsigned map (`:166–188,199–202`) | Their level tests and map source identities must receive live representatives. Boundary 1 retains C/D and copies e. Boundary 0 independently copies the reachable o/A/C/S/D class graph. No old per-use map has to be repaired at this cut. |
| Future display maps | No CompactType, canonicalization recursion map, co-occurrence map or varSubst exists at the cut (`TypeSimplifier.scala:102–157,185–239,286–319`) | Normalize the semantic input/store before these native consumers start. Their raw internal identities then range only over that one final fresh graph. History K/M does not feed them. |
| Optional debugging helpers | `children/getVars/show/showBounds` are graph readers; `println/assert` depend on dbg (`TyperDebugging.scala`) | They add no already active persistent semantic cache here. Correct representative-aware diagnostics are outside this successful fixed-term census. |

This census includes all TypeScheme/SimpleType-bearing fields of the owning
reference classes, all matched Let/Lam/Var/App recursion frames and all live
constraint/extrusion maps at the cut. The inference state is finite: original
source/contexts and finite stack, seven relevant raw variables plus disconnected
builtins, two Function descriptions and two small maps. There is no native
hidden worklist, provider selection, published term-derived scheme snapshot or
completed fresh-use frame at this event. The untouched builtin scheme remains
disconnected. Native propagation is synchronous recursion.
That is a reference-only fact; it is not an absence claim about Y3.

Closing under future consumers adds inner Lambda completion, recursive e
completion/publication, one E freshener, the second App/S allocation, outer
Lambda and o completion/publication, one O freshener and the display pipeline.
The second App's new locals are generated after the event from its context and
freshened e, so they require no retroactive rewrite. Future bound insertions
must read canonical owner lists; otherwise the census's initial transfer alone
cannot preserve later replay. The reviewed sections 5–6 already derive those
future comparisons and final Top -> Bot conditionally. This census does not
re-prove that result or substitute its transition assumption for the source.

## New minimized discriminator: context repair misses a constructor local

Consider a mutation of the proposed transition that repairs every context
payload, both merged bound stores, the active returned demand, and the App
result, but leaves the suspended inner Lambda's immutable local `param=B`.
Keep raw historical K/M unchanged. The next App return is the semantic Y=D.
The *unchanged native Lambda constructor* then executes:

```text
param = B                       // local retained before the event
body_ty = D                     // granted correctly transported App result
Function(param, body_ty) = F(B,D)
F(B,D).level = max(2,1) = 2
```

`Typer.scala:65` allocates param, `:66` suspends while typing the body, and
`:67` uses that same local rather than looking param up in the repaired ctx.
Thus changing even every immutable context map cannot establish the specified
actual `F(X,Y)` Lambda result. If no later structural normalization is added,
native recursive completion stores raw `L(e)=[F(B,D)]`, differing from the
examined continuation's `L(e)=[F(C,D)]`. This failure happens before freshening;
it does not repeat the earlier raw-versus-candidate freshening discriminator.

The witness needs one nontrivial class, one suspended constructor parameter
and one returned body type. The R/D class can be replaced by any unchanged
level-1 body type to isolate the missing B local. In the actual fixed term both
accepted equalities stay present. Removing the missed local, consuming q at
the Lambda constructor, or normalizing the whole Function before its next
semantic owner eliminates this witness. Each is a different representation
obligation; no choice is adopted here.

This is a minimized **representation/schedule omission**, not a source-typed
counterexample to intrusion. A consistently representative-aware constructor
or downstream consumer can repair it; the raw F(B,D) allocation alone does
not show a wrong final interface. The input's H explicitly includes suspended
Lambda transport, so this mutation does not refute H either. It demonstrates
why an actual owning rule must establish that clause and why context-only
rewriting is insufficient evidence. The known canonical-history-key failure
from the input section 4 was not rerun as a new attack.

## Exact remaining premises and failure conditions

The finite census found no extra fixed-term obstacle outside these owners.
A proposed finite representation could preserve raw historical records while
all listed semantic readers consume representatives. That feasibility statement
does not establish the following source/operational premises:

1. **Source certificate/activation owner:** resolved O/E source incidences and
   the actual extrusion occurrence/pairs are produced and available at the
   selected cut. Fixed source paths prove qualification; the reference contains
   no producer that emits the certificate or invokes equality here.
2. **Continuation owner:** the chosen machine exposes or interprets all live
   context, local and return type slots, including inner Lam.param and lazy
   App.res. A Scala callee cannot rewrite the caller's immutable local just by
   replacing a context map. This requires a justified representation or consumer
   rule, not an asserted heap-wide rewrite.
3. **Semantic/store/level owner:** representative class lists, structural
   descriptions and level access agree at every insertion, replay, monomorphic
   return, publication and freshener. Keeping original source scopes is a
   separate duty from using the low anchor's inference level.
4. **History owner:** raw K/M keys, hashes and parent/polar provenance stay
   stable while live demands and memo values have semantic representative
   access. A raw K entry records admitted/in-process comparison work; equality
   must not turn it into an automatic completed comparison.

With these source-owner premises independently established, the census closes
the dependency list for the exact continuation. Their establishment remains
the constructive lane's obligation; no operation definition is inferred from
the successful conditional trace. Missed constructor slots, stale structural
levels, inactive opposite-bound consumers, premature cached completion,
freshener keys from raw aliases, retargeted Value Names, or publication before
transport completes are explicit failure conditions. Only the constructor-slot
mutation above was derived as a new concrete failure in this packet.

The first, second and third premises are A/B obligations for this examined
execution; source origin/pair provenance should be retained at its construction
owner rather than reconstructed later (D). Another scalar quotient or ground
valuation checker would leave the same source/continuation owner untouched.

## Evidence, coverage, resources and runtime

Independent grounding is actual unmodified reference source, not a second
model implementing H. The fixed term, allocation prefix, qualified event and
reviewed conditional final interface are shared input dependencies. The
reference validates its own existing constructors and retained dependencies;
it is not an oracle for the new intrusion operation. No all-source semantics
or Y3 implementation is validated by the census.

Commands: `cat` of the exact governing documents and direct Typer/debug owners;
bounded `sed`/`rg` source and prior-result windows; `sha256sum` of eight direct
inputs, with a final stability recheck; static artifact whitespace inspection.
One earlier combined read of tasks/current.md and tasks/research-lab.md produced
truncated context; only the relevant association/current slices were subsequently
read. Their full historical bodies are not claimed as inspected. A bounded rg
using an unmatched theory filename glob returned a missing-path diagnostic;
the existing progress owner-audit and earlier falsification note were located.
Those discovery imperfections do not affect the complete directly inspected
Typer body or this exact-cut census.

No executable model/probe, mutation run, seed range, exhaustive search, tests,
builds, Git command/mutation, benchmark sample or production/shared-record edit.
Mutation coverage is one handwritten omitted-Lambda-local trace, not an
experimental pass/fail count. At most one lightweight command process was
active at any time; zero heavyweight processes. The assigned wall ceiling is
30 minutes; exact reasoning CPU, RSS and elapsed-time measurements are unknown.
All writes stopped before this frozen handoff.

Requested routing: configured normal researcher lane; `.codex/config.toml`
names default subagent `gpt-6.1-sol/high`, and researcher has no model/effort
pin. No model override was requested in this packet. Observed effective
model/effort: unknown; no runtime metadata was supplied. No Astra or child ran.

Unverified: actual equality/continuation constructor, external aliases,
arbitrary terms or future use histories, Y3 admission/elaboration and worklist
correspondence, complete Call/effects/providers/attachments/residual lineage,
abnormal handling, soundness, required principality and termination of the
combined all-source algorithm, production integration and F5 cutover.

**One recommended next action:** require the constructive transition to show
representative consumption at the actual inner Lam.param and App.res owners,
along with the immutable-context and raw-history separation, against this
census before reusing the input's conditional continuation.

## Dependency snapshot and commit packet

Independent review: `compiler_referee` PASS, with no BLOCKING, major or minor
findings. The reviewer verified the suspended `Lam.param=B` discriminator and
confirmed it refutes only context-only transport, not the complete quotient or
the approved equalities. The fixed-cut census and missing-premise boundary
were also reviewed; general inference and production gates remain OPEN.

| Direct input | SHA-256 |
| --- | --- |
| Fixed-term conditional continuation | `6d2e79c2113562422d06e8250e6830b60fe8b9006b18746b4f23362ac044e6c1` |
| Parent-copy SCC decision | `6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b` |
| Value/type association | `28a0c2aa196912e59e9adb9e62e30d171a03fc485d36314db02c5e13b74f6775` |
| Copied-row ownership | `7c170c346eeeabca50afe254425eba0c83995cb5e61bf257290ce2757c78bfbd` |
| Top-level inference principles | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| Reference Typer.scala | `f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9` |
| Reference TypeSimplifier.scala | `618b63f63e71c31890eb36cb18be474bfd31732173c159132306f0e14dc37d2b` |
| Reference TyperDebugging.scala | `8f0088c5ff729bb2f787ab2304529c0df5ed0711b29f10bef5398e41cb8a2d6a` |

Commit packet:

- Exact leased/changed path:
  `notes/progress/2026-10-12-fixed-term-quotient-transition-falsification.md`.
- Baseline: `5e7ffb735fc1a829d03890ebfd353e17ad7ca342`, supplied by primary.
  Direct input hashes above; no dependency was edited. Stability checked in
  this lane; baseline-to-file equality and branch integration belong to primary.
- Claim/review status: independent `compiler_referee` PASS for this bounded
  dependency characterization and omitted-constructor discriminator; no theorem
  closure claimed.
- Checks already run: actual owning source/state census, cut reconstruction,
  raw/history versus live-consumer partition, one minimized local-constructor
  derivation, dependency hashes and whitespace check; zero tests/builds/probes.
- Proposed one-line checkpoint message:
  `research: enumerate fixed quotient dependencies and Lambda transport omission`.
- Shared deltas left for primary/curator: record the complete fixed-cut consumer
  census and context-only transport failure; retain source certificate,
  continuation representation, semantic-store/level and history-owner premises
  OPEN. No shared task/index/authority, question-board or theory-status file
  was changed; no parent gate was promoted.
