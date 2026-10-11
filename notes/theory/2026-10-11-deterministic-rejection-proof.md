# Native deterministic rejection: retained errors and the Effect-drain frontier

Date: 2026-10-11
Status: frozen, unreviewed research derivation and bounded source characterization;
original rejection/soundness obligation OPEN.
Baseline: `ffde1f7899bbc3b628d27b9b705318b02a67ee81`.
Exclusive lease: this file only. Leaf assignment; no delegation or Git mutation.

## 1. Frozen obligation and method

The assigned parent question is whether **source-generated inconsistent constraints
can reach an accepted typing/export in native Simple-sub inference**, through actual
generation, accumulation, propagation/replay, levels, extrusion, qualifying
parent/copy intrusion, freshening/generalization, diagnostics and consumption.

The parent ranges over the original supported source domain and complete executions,
including local and module uses and the selected complete Call/effect meaning.
It retains every original source binder, scope, provider, whole argument/carrier,
witness, attachment and residual lineage, and the original shared interpretation
`xi = (nu,K,D)`. Consistency must be evaluated under that original dependent
quantifier/binder tree; this note does not replace it by separately chosen marginal
witnesses, independent port assignments, or an existentially flattened relation.
Required conclusion: an inconsistent source constraint family cannot be consumed as
a valid typing or public typed export. Required principality remains a separate,
unchanged parent requirement. A returned diagnostic research object is not, by
itself, an accepted typing.

No consistency, source-adequacy, reflection, complete Call, or lifecycle premise
is assumed to close that parent. No source restriction, early satisfiability rule,
alternative-typing retry, or reconstruction layer is introduced. No implementation
change is authorized by this note.

Method: inspect actual production constructors/consumers, construct the downstream
error-retention argument, trace one actual primitive application, then attempt to
extend the argument across mixed Value/Effect drains. The decisive localized
frontier is **a Value diagnostic first settled during an Effect-root drain**. The
source observations below do not establish that such a diagnostic is source
reachable, or that it produces a successful export.

Governing sources and sections:

- Authoritative `notes/design/2026-10-11-yulang-inference-top-level-principles.md`,
  Purpose, §§1–5 and Authority and integration: mathematical deterministic
  Simple-sub, necessary error continuation, no inconsistent publication, and no
  general exact-state rollback requirement.
- `rules/design-authority.md`, Authority order and Active withdrawal of Simple-sub
  bypasses; `notes/design/2026-10-10-simple-sub-legacy-withdrawal.md`, Selected
  policy and Mechanism-by-mechanism completion evidence. Retiring a legacy
  prerequisite does not prove full Call, soundness or principality.
- `rules/compiler-engineering.md`, Natural compiler behavior and proof-obligation
  economy and Deterministic Simple-sub inference.
- `rules/agent-orchestration.md`, Model routing and Astra escalation, Proof
  delegation and decomposition, and Information boundaries and assignment packet;
  `rules/research-lab.md`, One semantic baseline, explicit dependency invalidation,
  Evidence quality and stopping unproductive loops; `rules/git-concurrency.md`,
  Disjoint-file mode and Research-only checkpoint fast path.
- Root `AGENTS.md`, `.codex/config.toml`, `.codex/agents/prover.toml`, active
  `tasks/current.md` normal-inference/rejection sections, and
  `notes/design/INDEX.md` governing locators. Shared records are read inputs only.

The ordinary reference is the persistent original checkout
`/home/momota1029/rust/simple-sub-reference`, commit
`9bae772624c23b52a93c1b226157e16898b4d9db`, and the local original paper
`/home/momota1029/rust/simple-sub-reference-paper.pdf`. Its source constraining
throws `TypeError` at incompatible terminal comparisons (`Typer.scala:88–129,161`).
The reviewed import `notes/theory/2026-10-11-parreaux-simple-sub-proof-import.md`
preserves the paper's omitted-complete-proof and non-let-polymorphic proof limits.
That reference supplies no proof of Yulang's collecting diagnostics, four Function
ports, effects, intrusion or scheme-publication extension.

## 2. Constructive downstream result: reported errors exclude graph export

Claim class: direct source derivation, not independently certified theorem.

For every **production synchronous** execution of
`CandidateInference::solve(hir)` at this baseline which returns `Ok(c)`, if a
production diagnostic append occurs on that execution, then
`c.candidate_conflicts()` is nonempty and `c.export(root)` is `Err(ArtifactMismatch)`
for every root. This claim quantifies over successful control flow, not over
assumed consistency. It says nothing about unreported inconsistencies.

Derivation:

1. The production error vector starts empty (`lib.rs:9776`). Production writes
   are appends at `:11212` and `:14117`, rollback truncation at `:9526`, and final
   ownership transfer at `:17523`. The latter is a move into
   `FrozenInferenceData.errors`, not diagnostic erasure (`:17523–17580`).
2. `report_solver_kind` reserves and appends when the occurrence/kind is new
   (`:14085–14125`). Deduplication suppresses a second append only for an existing
   reported key. Successful route commits do not remove errors or reported keys
   (`:9208–9243`). The result does not depend on exact diagnostic text/order.
3. A rollback removes the transaction's suffix of reported keys and errors
   (`:9506–9526`), but its owning transaction returns `Err`, including when
   rollback or subsequent accounting itself fails (`:9244–9258`). This is not a
   path that retries to obtain another typing. `route_candidate_local_run`
   returns that result (`candidate_scheme.rs:1354–1415`);
   `route_incoming` returns the route error or an accounting error
   (`lib.rs:16461–16550`). `execute_candidate_action`, the synchronous source
   schedule, candidate SCC execution and `run_candidate` propagate it with `?`
   or return it (`candidate_source.rs:568–577,661–685`;
   `candidate_scheme.rs:842–914`; `lib.rs:14622–14632,10361–10376`). There is no
   successful `CandidateInference::solve` return after this rollback path.
4. Therefore on an execution that actually returns `Ok(c)`, a production error
   append cannot be removed by rollback. Finalization transfers its vector to
   the owned result. The private result deliberately has no closed types or
   public schemes (`lib.rs:10369–10376`).
5. `CandidateInference::candidate_conflicts` borrows that same vector;
   `export` checks its nonemptiness **before** root and graph lookup
   (`shadow_apply.rs:120–147`). Nonemptiness returns `Err(ArtifactMismatch)`.

The export guard is already present in the pinned baseline. The earlier
`notes/progress/2026-10-11-simple-sub-type-error-rejection-audit.md` is historical
at this consumer: its old absence-of-guard statement must not be applied here.
This note does not edit or recertify that historical artifact.

Private `fresh_use` and `source_call` observations are distinct APIs, and their
lookup bodies do not implement the export guard (`shadow_apply.rs:149–174,186–190`).
They expose research evidence with unresolved semantics; this derivation neither
calls them accepted typings nor proves that all future typed consumers will
enforce the same boundary. Internal SCC graph visibility likewise is not public
scheme publication.

## 3. One actual source-to-rejection bridge

Claim class: bounded static constructive derivation, conditional on successful
ordinary parsing/lowering, allocation/accounting and completion of the inspected
production schedule. No executable run or complete language theorem is claimed.

Source:

```yulang
my bridge x = 1 1
```

The wrapper is a syntactic function binding. No annotation, name trick, expansive
value generalization or negative-formal admission assumption is used. The HIR
LocalSource owner forms Lambda from the parameter (`module/local_source.rs:295–325`),
Apply from the actual argument tail (`:477–559`), and both Integer nodes (`:663`).
The private candidate preflight imposes no literal-callee exclusion
(`candidate_source.rs:82–112`), and the entry permits only the retained source's
covered ordinary unsupported-expression placeholders (`shadow_apply.rs:80–107`).

Let `C` be the callee integer's actual Value row, `A` the argument integer's
actual Value row, `R` the result row, and `F` the fresh negative four-port demand.
All are those of this one source occurrence, not separately selected witnesses.

1. Literal generation emits `Int+ <= C <= Int-` and `Int+ <= A <= Int-`, plus
   their empty computation effects (`candidate_source.rs:332–350`). Postorder
   actions execute these before Apply (`:234–267,374–396,661–685`).
2. Apply retains and validates the same operand/result/cause association, creates
   `F = Function4(A, argumentEffect, invocationEffect, R)`, and actively constrains
   `C <= F` (`shadow_apply.rs:1304–1405`). It does not pre-solve the demand.
3. The Value owner stores the upper `F` at `C` and replays retained opposite
   bounds (`candidate_extrusion.rs:808–831`). The prior `Int+` lower is one of
   those opposite bounds (`:763–805`). Bound insertion retains actual origins
   and a contextual fiber before its physical emission (`:406–565`;
   `candidate_effect.rs:420–473`; `candidate_context.rs:2815–2859`). Their
   first new/new replay constructs a child relation for `Int+ <= F`
   (`candidate_context.rs:2911–2988`).
4. The replay driver with `provenance=None` queues that child's actual typed
   work item; the outer Value drain consumes it. A queued replay outcome is not
   itself completion (`candidate_context.rs:3076–3123`;
   `lib.rs:12226–12293`). Both contexts are ordinary identity for this source,
   and no younger demand child needs extrusion at the current level.
5. Dispatch recognizes `IntPositive` versus `NegativeFunction` as incompatible,
   stores a direct diagnostic witness, and returns normal diagnostic progress
   (`lib.rs:12376–12394,14047–14070`). The replay records the root-to-child
   diagnostic edge at `candidate_extrusion.rs:780–783`.
6. Diagnostic settlement visits the finite root/child delta, seeds the child
   from its direct witness, and extends that witness to the root
   (`lib.rs:13099–13457`, particularly `:13300–13358`). Here the root and
   terminal child have a finite acyclic edge, so no general cyclic-diagnostic
   correctness premise is needed. `Stage::Diagnostics` replays the completed
   **Value root**, which appends `IncompatibleValue { Int, Function }`
   (`:12300–12301,13721–13742,14085–14125`). Settlement clearing its delta does
   not remove the completed root memo.
7. Section 2 then excludes graph export if the overall candidate solve returns
   successfully. An availability error instead returns no candidate object.

This fixed-head demand is inconsistent in the ordinary Int/Function projection;
it needs no complete Call witness to exhibit that necessary failed comparison.
Conversely, eliminating this one contradiction does not validate complete Call
or every source constraint. The whole Yulang source soundness/principality claim
is not inferred from this example.

## 4. Exact active Effect-drain observation

Claim class: bounded unconditional source characterization of successful control
flow at this baseline.

For every successful call to `complete_diagnostic_delta`, `diagnostic_delta` is
empty on return. If it was empty at entry, `lib.rs:13104` returns immediately.
Otherwise the function settles the new Value memos, then calls
`clear_diagnostic_scratch` at `:13457`; its successful return always reaches
`clear_diagnostic_scratch_unjournalled`, which clears the vector at `:13538`.
Journaling moves/records prior scratch when needed, but the live vector is still
cleared before success (`:13507–13539`). An error is propagated before subsequent
successful-consumer behavior can occur.

The actual candidate entry at `lib.rs:11954–11955` goes directly to
`run_candidate_typed_drain`. In its reachable `Stage::Diagnostics`:

```text
candidate_replay_effect_conflicts(initial, occurrence, cause)?
complete_diagnostic_delta()?
if initial is Value(root): replay_witness(root, occurrence, cause)?
if initial is Effect: for each live diagnostic_delta entry: replay_witness(...)?
```

These owners are `lib.rs:12295–12307`. The Effect iteration at `:12303` therefore
has zero iterations. The analogous iteration at `:12099–12100` has the same
order, but the native candidate graph entry bypasses that older body; it is
not an independent live route proving candidate coverage.

`candidate_replay_effect_conflicts` searches actual contextual child edges and
reports **IncompatibleEffect** records (`candidate_effect.rs:659–724`). It does
not search `TypedPairMemo::Value` for direct/completed Value witnesses. Terminal
acknowledgement/return handles (`lib.rs:12564–12635`) do not subsequently perform
the missing Value-witness replay. Thus the empty iteration cannot provide the
Value diagnostic coverage described by its neighboring comment.

Conditional consequence: if an authentic Effect-root drain first settles a
previously unreported incompatible Value witness, and no nested or subsequent
Value-root drain reports it or other diagnostic excludes export, this shown
Effect diagnostics phase alone will not append that Value error. This is a
conditional control-flow derivation, **not a source-qualified counterexample**.
All italicized source/replay/reporting conditions remain to be established.

## 5. Minimal remaining source context and constructive obstruction

The relevant real producer chain is:

```text
Effect-root Transport, empty worklist
  -> settle_candidate_intrusion(None)
  -> qualifying Value extrusion-parent/copy merge
  -> union both bound sides and canonicalize their origins
  -> candidate_replay_bound(Value owner, Positive, lower, parent=None)
  -> queued Value comparison carrying actual replay relation
  -> incompatible Value witness in diagnostic_delta
  -> Effect-root Diagnostics settles then clears delta
  -> empty Value-witness replay iteration
```

Exact owners: `lib.rs:12226–12231`; `candidate_intrusion.rs:355–491,493–605`;
`candidate_extrusion.rs:763–805`; `candidate_context.rs:2911–2988,3076–3123`;
`lib.rs:12376–12394,12295–12307`.

The first entry's source reachability cannot be obtained merely by creating an
Effect cycle. There is a direct sort argument from the actual intrusion adjacency:
Effect rows point only to Effect rows/endpoints, and Allowance/Support views point
only to their Effect tail (`candidate_intrusion.rs:402–448`). A Value Function
node can point into Effect ports, but Effect nodes have no edge back to Value
nodes (`:449–472`). Therefore ordinary Effect changes cannot create a new Value
SCC through an Effect-to-Value path. They may trigger a scan of **already pending
Value changes**; that is the source frontier requiring evidence.

A real owner capable of leaving a Value-side change without starting a Value
drain is fresh bound restoration:

1. An actual `Action::Local` captures its installed local graph and constructs
   one fresh use (`candidate_source.rs:680`;
   `candidate_scheme.rs:1346–1394,981–1028`). Its own sharing, older/nongeneric
   anchors, original contexts, bundles and evidence are retained together.
2. `begin_candidate_fresh_bound` maps one actual captured bound, retains that
   bound's orientation and fresh evidence, and calls
   `candidate_begin_bound_restoration` (`candidate_scheme.rs:1221–1270`).
3. Restoration physically inserts that bound and snapshots its current opposite
   count (`candidate_extrusion.rs:659–679`). If the count is zero,
   `candidate_step_bound_restoration_child` retires the operation at `:716–718`
   without constructing a typed comparison/drain. Storage has changed; no
   automatic all-bound replay or intrusion settlement is implied.
4. The real Local cursor advances to the next captured bound
   (`candidate_scheme.rs:1500–1514`). If that next relevant bound is Effect
   with a nonempty actual replay product, its child starts an Effect-root drain
   with the same Local occurrence/cause (`candidate_extrusion.rs:719–760`;
   `candidate_context.rs:3011–3054`). This gives an actual constructor/consumer
   route to the Effect-drain frontier, subject to the following unresolved
   Value state.

The exact missing premise is now finite and source owned: **does a supported
Local fresh-use restoration sequence produce a qualifying, as-yet-unsettled
Value parent/copy SCC and newly incompatible merged Value bounds at that
Effect-drain entry, without a preceding Value-root diagnostic?** It needs all of:

- An actual level-decreasing Value extrusion with its recorded parent/copy,
  and an actual later reverse Value dependency path. Arbitrary related rows
  are not intrusion candidates.
- A source-captured/fresh-transported Value bound whose restoration changes that
  reverse reachability; the saved zero replay product must really occur.
- The following actual Effect bound/replay child in the captured order. A
  permutation of graph bounds is not a source schedule.
- Incompatible concrete lower/upper Value bounds becoming compared at the
  merge, actual queued child dispatch, and no other error append/report or
  availability failure before the relevant consumer.

The minimal authentic context to inspect is therefore **one Local fresh use of
a Function4 graph containing a real extrusion parent/copy and both Value and
Effect captured bounds**, with the above adjacent restoration/first-drain
ordering. A recursive local function passed to an older captured callable can
produce the required level-decreasing copies, but this is only a starting
source class. The reviewed
`notes/progress/2026-10-10-local-recursive-contextual-source-witness.md` supplies
such source-directed copies and explicitly supplies **no reverse qualifying
path** in its selected fixture. Its negative fixture is also currently
Unsupported. Neither that fixture nor manually built intrusion tests proves
this missing premise. No exact source program satisfying all bullets was
constructed in this static lane.

Alternatively the same owner can discharge the premise negatively: establish
that every production Effect-drain entry is already stable for all Value
parent/copy SCCs, including zero-product fresh restorations. The invariant must
be proved at those constructors and ordered consumers; assuming it in a checker
or observing it in ordinary Apply tests would not suffice.

## 6. Obligation economy, parent relation and next owner

Two distinct routes were inspected: downstream reported-error retention/export,
and source generation plus mixed-drain activation/reporting. The first closes
only a downstream implication. The second localizes an absent report path but
does not prove authentic source reachability. A third equivalent reformulation
would leave that premise untouched.

Economy audit: this is class **A safety/correctness** if the Value mismatch is
source reachable and remains eligible for typed export. It is not class C
optional stronger characterization. The delta keys and completed witnesses are
already known at the diagnostic owner; forgetting their live iteration set is
a possible class D evidence-consumption issue within that A obligation. This
does not prove that a retained set is semantically necessary, authorize a repair,
or establish source reachability. The unknown earlier fact—whether real fresh
restoration reaches the Value SCC—cannot be supplied by fabricating a
certificate or strengthening the source domain.

The original rejection/soundness parent remains OPEN on complete inconsistency
reflection and the actual source/semantic bridge. Complete Call, hygiene,
generalization and required principality are unchanged and unproved here.
The complete Function comparison still carries four jointly generated ports
(`lib.rs:12493–12535`), not an independently witnessed argument/result pair.
The ordinary reference's two-child arrow/throw behavior cannot fill the mixed
drain premise.

One next action for the primary: assign the **Local fresh-bound restoration /
Effect-drain entry owner** a bounded source-qualified reachability or exclusion
packet for the exact sequence in §5, preserving captured order, live levels,
parent/copy records, bound evidence/relations and actual occurrence/cause. This
is the decisive question before claiming an inconsistency counterexample or
using the current diagnostic loop as rejection evidence. The producer requests
no further delegation, execution or repair in this packet.

## 7. Frozen dependencies, commands and resource use

Only static reads and this leased note write were performed. Commands: `rg`,
bounded `sed`/`cat`/`nl`, read-only `git rev-parse`, `git show`, `git status`,
`git diff --name-only`, and `sha256sum`. Decisive truncated captures were reread
in narrow sections. The dependency list below was byte-identical to the pinned
HEAD at inspection; no compiler dependency edit was present. Concurrent
untracked research files were left untouched and are not inputs to this proof.
The lease-scoped `git diff --no-index --check /dev/null <leased-note>` returned
zero and actually checked this untracked artifact; an ordinary tracked diff
check alone would not inspect it.

```text
c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94  crates/yu-solver/src/lib.rs
230ed70cc8575016967cdf16c6c814544b25e45b0fc687d6c89f0d38e8fb5cd6  crates/yu-solver/src/shadow_apply.rs
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49  crates/yu-solver/src/candidate_source.rs
fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0  crates/yu-solver/src/candidate_extrusion.rs
aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0  crates/yu-solver/src/candidate_intrusion.rs
9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1  crates/yu-solver/src/candidate_scheme.rs
4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987  crates/yu-solver/src/candidate_context.rs
ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df  crates/yu-solver/src/candidate_effect.rs
906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed  crates/yu-hir/src/module/local_source.rs
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389  notes/design/2026-10-11-yulang-inference-top-level-principles.md
f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9  reference Typer.scala
5ab2bd4122caee17c20134e4cbe8dc8a4848c142de1e576b5fd178aed8787698  original paper PDF
cd2b84a84d16be8856766f0514a2f400cf224ac95b6e81e42d4a7a875036e113  notes/theory/2026-10-11-parreaux-simple-sub-proof-import.md
e88afa0248a780cdf8d38fc3b1ad7950dd24596e2b301ebf03bd9b5678e41175  notes/progress/2026-10-11-simple-sub-type-error-rejection-audit.md
6db0a0f4c1eeb547e11ddb7b093c8042dc7716f3c1719a9f67cd79c6577a1629  notes/progress/2026-10-10-local-recursive-contextual-source-witness.md
```

Budget: one leaf, 45-minute wall bound, static lightweight source reads only.
Zero Cargo/build/test/probe/Oracle/exhaustive-search processes and zero benchmark
samples. CPU/RAM peaks and exact total wall time were not measured. The primary
remains verification owner. Requested runtime: ordinary Sol/high proof lane;
observed model/effort metadata unavailable, **unknown**. No Astra request,
configuration mutation, hot-reload claim or child launch.

Unverified scope: the §5 authentic source history, every full inconsistency
reflection/semantic adequacy case, complete Call, all effects/protection/lineage,
all-source extrusion/intrusion/generalization correctness and principality,
retained suspension/admission readiness, public consumer/cutover correspondence,
resource-abort implementation beyond the inspected error propagation, and
reference complete proofs omitted by the original paper. No self-certification.

## Commit packet

- Exact lease: `notes/theory/2026-10-11-deterministic-rejection-proof.md`.
- Baseline SHA: `ffde1f7899bbc3b628d27b9b705318b02a67ee81`; changed dependency
  hashes: none at freeze, with direct source hashes above. The artifact hash is
  returned separately so the file need not contain its own hash.
- Claim/review status: unreviewed research derivation/characterization; original
  rejection/soundness parent OPEN; no theorem promotion or implementation authority.
- Checks already run: static owner/call-path inspection, source dependency equality,
  SHA-256 capture and lease-scoped untracked-artifact whitespace check. No compiler
  execution or independent review.
- Proposed checkpoint message: `research: isolate native Effect-drain rejection frontier`.
- Shared-record deltas left to primary/curator: record the baseline export guard
  and the downstream reported-error retention result separately from full
  inconsistency reflection; record the active Effect diagnostics empty iteration
  and the exact Local-restoration source premise in §5; retain all original
  parent/Call/hygiene/generalization/principality gates OPEN. No shared record was
  edited.
