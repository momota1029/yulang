# Native Simple-sub redesign: equality preservation at the intrusion boundary

Date: 2026-10-11
Status: unreviewed research artifact; conditional algebra and localized obstruction
Parent soundness, required principality and source correspondence: OPEN
Baseline: `1e65dd3d2af604bac2bbbc548503ff4edd398957`
Branch: `research/simple-sub-intrusion`
Exclusive lease: this file only; leaf producer, no delegation or Git mutation

## Frozen objective and theorem

Determine whether the selected qualifying extrusion-parent/copy equality can
preserve supported source typing and required principality in a mathematical
Simple-sub redesign. Ordinary generation, accumulation and propagation remain
native operations. The old Rust candidate supplies constructor/consumer evidence,
not a new definition of the redesign's semantics.

Freeze the original theorem before the local derivations: for every supported,
resolved Yulang program `s`, its actual lexical environment `Gamma`, original
binders and definition boundaries, and every required derivation
`Gamma |- s : tau`, deterministic inference must succeed normally and return
an interface whose scheme subsumes `tau` in the governing scheme order. Every
successfully published interface must have a sound derivation for those same
source scopes. Actual extrusion-created copies retain their actual parents;
when a pair qualifies in the selected Value-reference SCC, solving and later
use equate it. Preserve ordinary recursive sharing, level scoping, independent
fresh uses, complete Call, and effect hygiene. Termination and safe abnormal
publication remain required. Successful suspension retains its constraints and
owned continuation; an invalidated dependent result is not reused.

The scheme-order direction is the ordinary imported direction: `P <=forall Q`
means some substitution of `P` is below `Q`, so the principal scheme belongs
on the left. This note does not replace Yulang's complete typing judgment with
the paper's two-port Function judgment, nor select a new Yulang scheme order.
The parent claim quantifies over the original supported source domain, not over
the smaller pure fragment used by the local algebra below.

Exclusions from established results, rather than restrictions on source:
all-source soundness/completeness, required principal generalization, complete
Call realization, effect/protection semantics, source reachability of a
qualifying pair, complete solver termination, and production/F5 cutover.
No annotation requirement, eager per-constraint satisfiability test, speculative
typing search, independent marginal witness choice, or extra recursion ban is
introduced. This note does not certify itself or promote any parent gate.

## Governing sections and frozen dependencies

The top-level principles, §§1–5, Evaluation, and Authority and integration,
govern proof-derived native operations and necessary abnormal safety.
The parent-copy contract's Selected operation and compiler responsibility,
Value-reference SCC clarification, and Retained boundary govern qualification:
vertices are Value variables, edges are actual references in their values;
neither subtype judgments nor genealogy itself supplies adjacency.
Annotation hygiene §§1,3–4 retains composed polarity, local concrete subtraction,
positive allowance, and original authority through transport. Residual lineage's
Selected policy retains every separately constructed recipe after row equality.
Local self-recursion's Selected source behavior retains one open monomorphic
root during its initializer and later ordinary publication/use boundaries.

Workflow: agent-orchestration, Model routing and Astra escalation / Proof
delegation and decomposition; research-lab, One semantic baseline / Evidence
quality and stopping unproductive loops; design-authority, Authority order /
Natural compiler behavior; compiler-engineering, Natural compiler behavior and
proof-obligation economy / Deterministic Simple-sub inference; git-concurrency,
Disjoint-file mode / Research-only checkpoint fast path. The primary retains
authority, review, shared records and integration.

The original reference is `/home/momota1029/rust/simple-sub-reference` at
`9bae772624c23b52a93c1b226157e16898b4d9db`; mathematical source is the local
`simple-sub-reference-paper.pdf`, *The Simple Essence of Algebraic Subtyping*,
§§3.2–3.5, Figs.6–9, and §§5.1–5.3, Figs.10–12. The independently reviewed
`2026-10-11-parreaux-simple-sub-proof-import.md` records the published theorem
statements and omitted proof premises. The paper's §5 restricts its proof
discussion to non-let-polymorphic inference and supplies sketches, not complete
proofs. Neither let principality nor new intrusion follows by importing §5.

Existing bounded results used without another reconstruction:

- `2026-10-11-simple-sub-rebuilt-core-proof.md`, Native generation and propagation,
  repaired Lemma 1, Polarized extrusion, Level/SCC obstruction, and Generalization
  and instantiation. Initial/bulk pair coverage is explicitly conditional.
- `2026-10-11-simple-sub-value-reference-scc.md`, Reference occurrence relation,
  What the constructors actually store, and Level argument, applicability, and
  remaining bridge. Its uncle/nephew operation trace is not a source-qualified
  direct parent/copy witness.

These notes do not establish the missing successor Value-owner law. The present
delta distinguishes equality entailment from preservation of required typing
witnesses and tests preservation under later constraints.

## Native operational specification and original binders

For the pure reference fragment write a state as variable identities with fixed
levels, lower/upper incidence lists, and pending comparison processing. Type
terms are variables, canonical primitives, Functions and records; a structural
term's level is the maximum level of its variable occurrences. Structural syntax
is finite between variables, but bound references may cycle. No polarity copy
is silently treated as the original binder.

The owning constructors are reference `Typer.scala:48–84`:

| Source constructor | Native output and generated constraint |
| --- | --- |
| Literal | Canonical `Int`; no comparison required at generation |
| Resolved Name | One instantiation of the bound scheme, or the same monomorphic row |
| Lambda | Allocate parameter `a` at current level, bind that exact row, return `a -> body` |
| Apply | Allocate result `b`; submit `callee <= argument -> b`; return `b` |
| Record / projection | Construct field types / submit one-field demand with a fresh result |
| Nonrecursive let | Infer initializer at `h+1`; retain body with generalization boundary `h` |
| Recursive let | Allocate open `a` at `h+1`, expose that exact monomorphic row to its initializer, submit `initializer <= a`, then retain the scheme |

The recursive binder is shared before publication; it is not independently
instantiated at recursive occurrences. Supported Yulang recursion remains
the selected source recursion, including its actual local boundary; this table
does not adopt arbitrary reference AST forms as new Yulang source features.

Propagation at `Typer.scala:88–129` chooses one level-safe storage owner.
For `a <= u`, append `u` to `U(a)`, then process every existing `l <= u`
with `l` in `L(a)`. The dual insertion appends a lower, then processes every
existing upper. A variable-variable comparison need not be stored at both
endpoints. Arrow comparison uses the same arrow pair for reversed arguments
and forward results. Records demand the actual right labels. On a level
violation, extrude the offending term in the appropriate polarity and continue.

This specifies pending propagation rather than solving at generation time.
The existing repaired pair-coverage lemma requires initial coverage, actual
opposite replay for ordinary insertion, and justified coverage for direct/bulk
initialization. An endpoint cache entry is not by itself a completed obligation.
The reference's extrusion and freshening assignments bypass ordinary insertion;
their stored lists do not prove activation or complete replay. A redesigned
asynchronous scheduler must implement that same operation with real retained
continuations and valid dependency dispositions. No scheduler conformance or
termination theorem is asserted here.

Extrusion at target `k`, `Typer.scala:134–159`, memoizes `(parent,polarity)`
before descending. For an above-level parent `p`, allocate a fresh `c` at `k`:

```text
positive: p <= c; copy the positive extrusion of L(p) into L(c)
negative: c <= p; copy the negative extrusion of U(p) into U(c)
```

Arrow arguments reverse polarity. The reference stores the directed
comparisons on `p`. Neither those comparisons nor copy-creation ancestry by
itself establishes a Value-reference edge. Whether either constructed Value
refers to the other must follow from the approved Value constructor/transport
law; that law remains OPEN. The two polarities can produce two distinct
copies of one parent. Repeated occurrences with one polarity share the same
memo image, including through recursive bounds. Retaining the actual parent
record is the selected Yulang addition; it does not erase that polarity
distinction or supply an SCC edge.

Freshening at `Typer.scala:166–203` uses one memo per use for every reachable
quantified original row across both bound sides. Rows at/below the boundary
remain shared captures; rows above it receive one image per original identity.
Different uses have disjoint fresh images. Recursive sharing is preserved by
registering before descent. Coalescing at `239–257` uses polarity-selected
bounds and recursive binders keyed by identity and polarity. The level-safe
renaming property is available from the prior local derivation; universal let
semantics and principality are not proved by that renaming property.

## Equality quotient: an algebraic fact with explicit hypotheses

Freeze a finite pure constraint store `C`. A valuation assigns one shared type
interpretation to each variable in a fixed preorder with sound Function/record
variance and structural substitution. Let `E` be all equalities chosen in one
intrusion step and `q` their identity quotient. Retain every constraint incidence;
the quotient rewrites endpoints and all structural variable occurrences. For
this algebraic proposition only, equality means equality of interpretations.
It does not assert identity of source receipts, attachments or residual recipes.

**Local proposition, derived here and awaiting independent review:**

```text
Sol(q(C))  is in bijection with
{ mu in Sol(C) | mu(a)=mu(b) for every (a,b) in E }.
```

Proof: a quotient valuation `nu` lifts to `mu(a)=nu(q(a))`. Structural
substitution gives `[[q(t)]]nu = [[t]]mu`, so every rewritten comparison has
exactly its old truth value and each equality in `E` holds. Conversely, an
equal valuation is constant on quotient classes and defines `nu`; the same
substitution identity proves every quotient constraint. The two maps are inverse.
One joint valuation is used for all variables and comparisons.

Thus merging rows and unioning their lower/upper collections realizes equality
at the pure constraint level **if** every occurrence is redirected. It does not
prove that adding those equalities preserves required source typings. All newly
formed lower/upper cross pairs still need activation; old within-row coverage
does not cover newly merged cross pairs. Levels and generalized binders are
not present in this proposition's semantic hypothesis and are not proved by it.

For an observation of a whole interface, preservation would need a joint
equal witness with the same observation, not every old valuation to be equal.
At the pure algebraic level, equality of projected solution sets is equivalent
to: every old solution has an equal replacement with the same designated
observation. This follows immediately from the bijection and the inclusion
of equal solutions among old solutions. Arbitrary-model projection equivalence
is a possible stronger characterization; it is not imposed as a new parent gate.

The **required** source version is narrower in its premise and richer in its
conclusion: for every required original typing `Gamma |- s : tau` whose joint
typing witness is represented before a qualifying merge, retain a joint witness
after that merge, with the same `Gamma`, original scopes and complete interfaces,
and the required relation to `tau`. All comparisons, provider/result observations,
effects and future uses share that witness. This is an OPEN preservation
premise, not a theorem obtained by defining a new witness family. Together with
the native soundness/completeness and source interpretation bridges it could
support the original principality induction. Without those bridges the pure
quotient proposition cannot be applied to Yulang's complete judgment.

Universal `C entails p=c` is sufficient at the pure constraint level, but it
is stronger than existence of a preserving equal witness for each required
typing. Conversely, one equal witness at copy creation is too weak to prove
preservation for later constraints or all required typings. These quantifier
distinctions do not change the selected operation or weaken the original goal.

## A direct continuation falsifier for unconditional equality lifting

Use canonical reference primitives with `Int` not below `Bool`, as in the
paper's primitive subtyping. This is a manually derived operation trace through
the actual reference constructors, not a parser run or a source-qualified SCC.

1. Allocate empty `p` at level 1 and submit `p <= Bool`. The left-variable
   branch stores `U(p)=[Bool]`; there are no lowers to replay.
2. Extrude `p` positively to level 0, obtaining fresh `c`. The constructor
   retains comparison meaning `p <= c`, physically appends `c` to `U(p)`,
   and copies empty `L(p)` into empty `L(c)`.
3. Submit `Int <= c`. The right-variable branch stores `L(c)=[Int]`;
   `U(c)` is empty, so this continuation returns successfully.

Final constraints are `p <= Bool`, `p <= c`, and `Int <= c`. All stored
bounds respect their owners' levels. The one valuation `p=Bottom, c=Int`
satisfies them. Initially, assigning `c=p` extended every old valuation at
extrusion creation; after step 3, no equal valuation exists, because equality
would imply `Int <= p <= Bool`. The dual trace starts with `Bool <= p`,
extrudes negatively, then submits `c <= Int`; it has the same obstruction.

This refutes the general shortcut “equal-parent extension at extrusion creation
survives all native later continuations.” It does **not** refute the selected
qualifying operation: this trace has no return reference from `c` to `p`, no
qualifying SCC, and no exact source AST establishing the whole trace. Adding
such a reference by hand would assume the missing construction premise.
The trace identifies why a qualification-specific preservation law is necessary.

The witness must also satisfy all equalities jointly. Pairwise equal lifting
can fail to compose: fixed constraints `Int <= a <= Int` and
`Bool <= d <= Bool`, with unrestricted `b`, permit `a=b` separately and
`b=d` separately but forbid both at once. This second elementary algebraic
example is not extrusion provenance or an SCC witness. It rules out choosing
an independent witness for each merge, provider or interface coordinate.

## Exact first missing premise and original generalization scope

The first source/operational premise is the actual constructor law for the
successor's Value descriptions and their reference occurrences at the selected
intrusion boundary. It must specify the produced references on actual variable
identities through generation, polarity copies, recursive sharing and freshening,
and justify the correspondence to the graph consumed by SCC processing. It
must also explain a qualifying actual parent/copy pair's levels and scope.
This is not supplied by the parent-copy contract's operation alone.

The previous native-level derivation already shows why another ordinary-bound
SCC reconstruction cannot fill that gap: under the declared reference invariant,
each bound-occurrence edge is nonincreasing in level, whereas direct extrusion
creates a strictly lower-level copy. Its parent/copy pair cannot share such an
SCC while levels remain fixed. Same-level uncle/nephew cycles do not fix this
direct-pair gap. This conditional result is not an impossibility claim about
the selected successor graph or mutable representative levels.

After that first premise, the next required semantic premise is preservation
of the original joint typing witnesses under the qualified equality, including
the continuation falsifier's exclusion by actual source construction. No
SCC-to-inequality rule is invented here. A supplied graph law could justify
equality by source semantics or by an established preserving witness argument;
the producer cannot select a new semantics for that purpose.

Generalization has an additional original binder obligation. If `p` is above
boundary `h` and its lower-level copy `c` is at/below `h`, identifying them and
using minimum level makes their representative nongeneric. In native freshening,
`p` formerly received an independent image per use, while `c` remained shared.
The quotient proposition cannot justify that quantifier change. Required
principal preservation must show that independent valid uses retain a common
shared-capture assignment and their complete interfaces after the equality.
Simply freshening the nongeneric representative to recover lost polymorphism
would change its actual capture boundary. Simply freezing the formerly generic
parent can lose a required typing. Neither repair is adopted here.

## Actual owner/consumer bridge inventory

Rust locators refer to the pinned Yulang baseline. They demonstrate responsibility
and actual calls, not redesign conformance or full semantic discharge.

| Responsibility | Owning constructor/consumer | Established inspection and remaining bridge |
| --- | --- | --- |
| Native ordinary generation | Reference `Typer.scala:48–84` | Original rows, lexical let boundary and recursive sharing explicit; no intrusion/effects |
| Native accumulated replay | Reference `Typer.scala:115–126` | Ordinary insertion replays opposites; direct extrusion/freshening assignments need their own coverage justification |
| Yulang Apply source incidence | `candidate_source.rs:394–411` | Retains actual callee, argument, effect/result ports, source/checking occurrences and source input |
| Yulang recursive Name | `candidate_source.rs:381–387` | Active initializer links the original open endpoint; installed locals use the scheme route |
| Demand submission | `shadow_apply.rs:1304–1400,1446–1468` | Checks recipe incidence, constructs four-port negative Function, retains native interface, actively calls value/effect constraining; this is not complete Call |
| Actual copy and parent | `candidate_extrusion.rs:90–158`; `candidate_intrusion.rs:171–220` | Fresh target-level copy, actual parent/polarity/target recorded before copied bounds; provenance excluded from adjacency |
| Bound activation | `candidate_extrusion.rs:763–838` | Ordinary application inserts then begins/drives opposite replay; extrusion's direct insertion at :123 is a separate activation responsibility |
| Qualifying graph | `candidate_intrusion.rs:375–486` | Traverses both Value bound sides, Function ports, Effect rows/views, then compares component IDs for actual parent pairs; equivalence to selected Value-reference paths remains OPEN |
| Equality and subsequent replay | `candidate_intrusion.rs:513–605` | Transfers both bound sides/origins, canonicalizes, takes minimum level/non-generic union, reopens a root and replays lowers; these actions do not prove the qualification's semantic preservation or all transferred scope laws |
| Fresh use | `candidate_scheme.rs:35–83,955–976,1221–1266` | Captures bounds/evidence/four-port structure, recaptures the live root and restores each fresh bound with its joint use/context/evidence maps; complete coverage and original principal scope law remain OPEN |
| Complete Call frontier | `candidate_call.rs:81–130` | Explicit missing suppliers include whole registration, formal introduction/exposure, Gen-Call, argument carrier, receiver and complete result/future interfaces |

The old graph's mixed Effect/Function paths require their Value-reference
interpretation from actual owning values. Merely deleting Effect vertices or
adding subtype directions is not that bridge. The selected operation is not
disabled because the bridge is missing; dependent certification remains OPEN.

Row equality transports every residual recipe and current/future obligation.
It grants no new annotation authority and does not identify attachment,
provider, receipt, witness or recipe lineage. Complete Call still requires
one actual correlated callable/whole argument/entry/result/protection interface;
the pure arrow comparison and four-port demand cannot choose its coordinates
independently. Existing conditional hygiene proofs retain their supplied
owner/profile/transport hypotheses. They are explicit dependencies rather than
conclusions of the pure quotient algebra.

## Economy audit, stopping point and checks

Prior materially different routes were native structural/level derivation and
operation/reference characterization with an uncle/nephew cycle. Both left
the actual Value-owner/qualifying direct-pair premise untouched. Apply the
existing economy audit before another equivalent SCC proof:

- The authentic reference construction/retention obligation is D where the
  producing phase already knows its occurrence and owner. Retain that fact at
  its owner instead of reconstructing it from successful comparisons or IDs.
- Qualified equality's scope and soundness obligations remain A; normal recursive
  progress and required principal generalization remain B.
- Equality for every arbitrary raw solution is a stronger characterization; this
  note neither makes it a mandatory route nor demotes original A/B obligations.

The present algebra and continuation falsifier discriminate a real missing
preservation premise; they do not establish source qualification. Stop here.
No new semantic layer, alternative restriction, third graph reconstruction,
proof-status promotion or executable enumeration is proposed as progress.

Checks already run: read-only branch/HEAD/status and reference-pin inspection;
dependency-scoped `git diff --name-only <baseline> -- <inputs>` returned no
changed named inputs; `cat`, `rg`, `nl`/`sed` source reads; bounded
`pdftotext -layout ... -` section reads; SHA-256 capture below. No code, tests,
builds, Oracle, executable checker, benchmark, Git mutation or child job ran.
Mathematical examples are manual derivations, not observed execution results.
Independent review is pending. Up to five lightweight read commands were
batched in one tool call; no compute wave, heavyweight process or measurement
sample was consumed. Exact OS process count, whole-task wall time, CPU and peak
RSS were not instrumented. The new-file whitespace check
`git diff --no-index --check /dev/null <leased-path>` emitted no diagnostics;
unrelated concurrent notes were left untouched.

Requested runtime: normal proof lane, GPT-6.1 Sol/high by configured role policy;
the role omits model/effort pins and the callable schema exposes `prover`.
Effective runtime model/effort metadata is unavailable here and is unknown.
No Astra execution, override verification or hot reload is claimed.

One next action: obtain from the actual Value constructor owner the frozen
qualifying direct parent/copy reference trace and its level/binder law; then
apply the joint preservation obligation to that trace before a dependent
implementation strategy is treated as proof-supported.

## Dependency snapshot and commit packet

Content SHA-256 at inspection:

```text
parent-copy contract  2f08967e8f0477a1dacda62a211c620cd9cc3b80d476412b4c1e3d60506040c0
top-level principles  edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389
annotation hygiene    503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a
residual lineage      d5c46b74d678028046bdfa0f7fd2b71bb2abfb112987000fe43e0fa5875d5d98
local self-recursion  38d42183fdc4f2c0136112d8b305816241d8f449367b473e4de3a5135dc49895
ordinary proof import cd2b84a84d16be8856766f0514a2f400cf224ac95b6e81e42d4a7a875036e113
prior native proof    08f178b448c711c43938ec26dd438c18bbee5d47ee4d11f1a03d2e88839f6597
reference graph note  8dd8eb55ac9d9df75980182cb5483f9394674a94f77c9d70d12f89b5be0d24e6
candidate_intrusion   aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0
candidate_extrusion   fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0
candidate_scheme      9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1
candidate_source      13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49
shadow_apply          230ed70cc8575016967cdf16c6c814544b25e45b0fc687d6c89f0d38e8fb5cd6
candidate_call        79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35
reference Typer       f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9
reference traversal   8f0088c5ff729bb2f787ab2304529c0df5ed0711b29f10bef5398e41cb8a2d6a
reference paper       5ab2bd4122caee17c20134e4cbe8dc8a4848c142de1e576b5fd178aed8787698
```

Exact leased path: `notes/theory/2026-10-11-inference-rebuild-native-spec-proof.md`.
Baseline SHA: `1e65dd3d2af604bac2bbbc548503ff4edd398957`.
Changed dependency hashes: none observed at inspection; primary rechecks the
frozen dependency cone before review/integration. Claim/review status: unreviewed
conditional pure algebra, manual shortcut falsifier and localized source
obstruction; original theorem remains OPEN. Checks already run: those listed
above; no executable semantic checks. Producer writes stop at handoff.
Proposed checkpoint message: `research: isolate joint intrusion preservation law`.
Shared-record deltas left for primary/curator: link this bounded delta; preserve
the existing Value-owner/qualification owner and OPEN parent status; record
that creation-time equal extension does not prove later joint preservation,
and that level/quantifier changes still require the original principal scope
law. No shared record, authoritative contract or compiler file was edited.
