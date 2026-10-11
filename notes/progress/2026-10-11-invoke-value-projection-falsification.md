# `invoke` ordinary value projection: falsification and source-owner audit

Date: 2026-10-11
Status: frozen, unreviewed research characterization; no theorem or compiler gate closure
Baseline: `1876f777358489d01c9755fa63a8d5876aa729a2`
Branch assigned by primary: `research/simple-sub-intrusion`
Method: static source trace and exactness attack; complementary to the constructive prover
Exclusive lease: this file only

## Objective, authority and result

Attack the claim that projecting the actual four-port constraints for
`my invoke f = f 1` onto ordinary value ports yields the reference's lambda /
application constraints and root. This audit uses the current source constructors,
not a supplied graph or a checker assuming their transition rules.

No semantic counterexample to ordinary value inference was found in this one
source spine. This is not a proof. The discriminating finding is that **effect-port
deletion alone does not literally produce the reference constraint list and root**:
the candidate has a literal row with both primitive bounds, a lambda expression
row, and a separate definition root. An explicitly stated treatment of those
administrative rows is necessary for a claim of reference correspondence.

The exact raw-shape claim is refuted by the assigned source itself. The broader
claim of equivalent ordinary value solutions after administrative elimination
is not refuted here. Nor does that equivalence establish complete Call, effect
hygiene, public scheme inference, or production acceptance.

Governing sections: `rules/design-authority.md`, Authority order;
`rules/research-lab.md`, One semantic baseline / Evidence quality / Writes,
artifacts and review snapshots; `rules/git-concurrency.md`, Disjoint-file mode;
`rules/compiler-engineering.md`, Natural compiler behavior and proof-obligation
economy / Deterministic Simple-sub inference; Authoritative
`notes/design/2026-10-11-yulang-inference-top-level-principles.md`, §§1–5.
Accepted decisions preserved: ordinary Simple-sub generates and accumulates
constraints without an already selected provider or per-constraint eager
satisfiability gate; effects are retained; no new source rule, `Fam_delta`,
`EmittedGenCall0`, or fabricated semantic ports are assumed.

## Exact source map and hypotheses

Hypotheses for this finite characterization: successful ordinary source formation
of the written unannotated binding, the actual candidate graph mode selected by
`CandidateInference::solve`, and successful constructor/admission operations.
No assumption that effects are absent is made. This is a trace of emitted
constraints; it is not an enumeration of every final saturated physical slot.

The pinned reference is `/home/momota1029/rust/simple-sub-reference`, assigned
commit `9bae772624c23b52a93c1b226157e16898b4d9db`. Its actual
`shared/src/main/scala/simplesub/Typer.scala:59–74` creates:

```text
Lam(f, App(Var(f), Lit(1)))
alpha := fresh monomorphic parameter
beta  := fresh application result
constrain(alpha, Function(Int, beta))
returned root = Function(alpha, beta)
```

`Typer.scala:105–107` compares Function arguments in reverse and results forward;
`:115–117` inserts the demand in alpha's upper list and replays existing lowers.
The imported theorem note's §§3–4 records this exact calculation. It also
explicitly excludes Yulang effects, source lowering and public publication.

The current candidate owners are:

| Fact | Owner at the assigned baseline |
| --- | --- |
| Source parameter becomes Lambda and lexical binding | `crates/yu-hir/src/module/local_source.rs:286–317` |
| Source call retains callee, argument and source form | `module/local_source.rs:553–563` |
| Candidate selects retained source when present | `crates/yu-solver/src/lib.rs:1125–1135`; `shadow_apply.rs:80–117` |
| Formal Name endpoint is the actual parameter row | `candidate_source.rs:209–217` |
| Literal emits both primitive bounds | `candidate_source.rs:336–345` |
| Apply stores actual formal, argument, result and effects | `candidate_source.rs:394–411`; `shadow_apply.rs:1339–1383` |
| Lambda reads actual parameter and body result | `lib.rs:11233–11261` |
| Lambda builds fresh entry/returned effects | `lib.rs:11267–11338` |
| Lambda Function constrains its expression row | `lib.rs:11342–11362` |
| Expression row links to definition root | `candidate_source.rs:477–495,665–668` |
| Captured root is positive definition row | `candidate_scheme.rs:744–747,891–898` |

Name rows below denote actual owned source rows, not new compiler descriptors.
Let alpha be the lexical parameter, s the integer value component, beta the
application result, ell the lambda expression component, and r the definition
root. Let ae and ce be literal and formal-Name evaluation effects, e the fresh
invocation effect, re the application effect, u the fresh lambda entry effect,
and v the fresh lambda returned effect. The relevant current emission is:

```text
Int+ <= s-; s+ <= Int-
BottomEffect+ <= ae-; ae+ <= EmptyEffect-
BottomEffect+ <= ce-; ce+ <= EmptyEffect-
alpha+ <= Function-(s+, ae+, e-, beta-)
ce+ <= re-; e+ <= re-
u+ <= v-; re+ <= v-
Function+(alpha-, u-, v+, beta+) <= ell-
ell+ <= r-
```

The pure evaluation of the lambda expression is also emitted separately by
`candidate_source.rs:445–447`; it is not its invocation effect. No value
constraint in this emission is guarded by a previously obtained Function lower
on alpha or by an Empty upper on e. The body effect reaches v rather than being
silently replaced with Empty. This does not give a complete semantic effect
interpretation.

## Exactness witness and variance attacks

Deleting effect constraints and ports, while retaining actual value rows, gives:

```text
Int <= s; s <= Int
alpha <= s -> beta
alpha -> beta <= ell
ell <= r
designated root = r
```

The reference has one demand `alpha <= Int -> beta` and designated root
`alpha -> beta`. These are different raw outputs. The literal `1` already
witnesses the extra primitive row; the assigned `invoke` spine additionally
witnesses the root difference. No exhaustive claim about smallest source size
across the language is made.

Under ordinary transitive arrow subtyping, `Int <= s` and `s <= Int` make s
mutually subtype-equivalent to Int. They are not unification. Therefore the
literal seam supplies a natural candidate elimination premise, rather than a
contra-variance counterexample. A stronger claim that every satisfying raw
value assignment identifies r with the Function is false: the value slice
allows `s = Int`, `alpha = Int -> Int`, `beta = Int`, and `ell = r = Top`.
This is only a countervaluation to root equality in the erased slice. It is
not a full four-port model, an executable Yulang typing, or a counterexample
to the reference's ability to give the expression a supertype.

The actual Function constructors validate value polarities `[-,+]` for positive
Functions and `[+,-]` for negative Functions (`term.rs:1126–1165`). Their
decomposition sends upper.argument <= lower.argument and
lower.result <= upper.result (`lib.rs:12493–12520`), agreeing with reference
arrow variance. Both effect ports are emitted as typed child tasks; they have
not been presumed absent. The resuming dispatcher admits/enqueues all four
children (`lib.rs:12643–12666`). No variance reversal was found.

Current candidate scalar insertion is owned by
`candidate_extrusion.rs:808–837`, not the noncandidate branch of
`lib.rs:13744ff`. It installs one ordered bound and replays the opposite list;
`:570–626,763–804` shows the replay directions. At equal level, a row/row
constraint is owned by the left row's upper list. This matches the reference's
ordered left-variable case and prevents incorrectly inferring paired physical
adjacency from the older graph theorem's description.

## Effects, retained consumers and publication boundary

The solver uses one typed drain. Source context processing runs before task
dispatch (`lib.rs:12259–12277`). Function port contexts swap both argument fields
and preserve both result fields (`candidate_context.rs:2557–2608`). A contextual
filter on a value task can return an availability error
(`candidate_context.rs:2753–2759`); therefore generic independence of value
solving from effect checks is not established by simply erasing effect nodes.
This audit does not claim that such a filter is reached by the bare invoke
source. Proving that premise, or full mixed-port solution projection, belongs
to the constructive/source bridge gate.

There are actual internal consumers: source Module actions route an incoming
use (`candidate_source.rs:672–677`), graph freshening restores every captured
bound then exposes the mapped root (`candidate_scheme.rs:970–976`), and
`instantiate_candidate_graph` submits that mapped root into the receiving
component (`:1275–1304`). Capture retains all four Function children and local
value bounds (`:567–615` for value rows). Existing
`tests/candidate_graph_call.rs:326–343` contains the two assigned invoke
fixtures; they were inspected but not run in this packet.

The result can thus feed the private successor's fresh use and subsequent
constraints. It cannot yet be reported as a consumed ordinary public principal
scheme: `finish_candidate` requires `closed_types.is_none()` and empty schemes
(`lib.rs:10368–10373`); `CandidateInference::export` offers only a borrowed graph
and rejects conflicts (`shadow_apply.rs:124–149`). The separate
`CandidateValueObservation::export` at `:696–701` belongs to the older value
observation path and is not a consumer of this graph inference result.

The older `notes/theory/2026-10-10-candidate-graph-call-correspondence.md` is
historical evidence for its own pins. Its §2.2 emission omits the current
`s <= Int` edge, uses an Empty lambda argument-effect child, and conflates the
lambda Function route with r. Its current reuse needs the above source delta;
its previous reviewed claims are not silently promoted to this baseline.

## Evidence limits, dependencies and handoff

Oracle independence: the reference constructors were read directly from the
official pinned implementation; they share no supplied candidate transition
table. The candidate was traced from actual HIR/source collection, admission,
typed decomposition, scalar replay and use/publication owners. Both source
traces are manual and can share analyst mistakes. There is no independent
review or executable oracle result from this lane.

Coverage: one written unannotated invoke binding, current source-carrier route,
and static legacy fallback/consumer locators. No seeds, random ranges,
mutations, runtime runs, Scala/Cargo builds, tests, heavyweight processes or
performance samples. Group/ascription equivalence, annotations, arbitrary
effects, providers, imports, SCCs, levels beyond this spine, intrusion,
generalization, complete Call, coalescing/public simplification and soundness /
principality are unverified. No repeated equivalent probe was attempted.

Commands: `rg`, `sed`, `nl`, `cat`, `sha256sum` for the named owners; a leased
file existence check; `apply_patch` for this note. One initial read-only
`git rev-parse HEAD` confirmed the assigned baseline before source inspection;
no Git mutation. Two exploratory locator commands named a nonexistent HIR
subpath and a malformed sed range; both were replaced by actual file locators,
and neither contributes evidence. CPU/RAM and exact wall usage were not
measured; only short serial read commands ran within the assigned 25-minute
wall budget. The runtime model/effort metadata is unknown to this leaf.

Frozen direct dependency SHA256 values:

```text
candidate_source.rs 13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49
shadow_apply.rs 230ed70cc8575016967cdf16c6c814544b25e45b0fc687d6c89f0d38e8fb5cd6
lib.rs c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94
term.rs 75506948ec8043c9d5b4d0369ae94ed31c940aae0bc930ae1099bc1c758bb615
candidate_extrusion.rs fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0
candidate_context.rs 4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987
candidate_scheme.rs 9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1
tests/candidate_graph_call.rs d7fe99792c9ade837a9ca1a206d2d24aa6cde2fa0c25979dd9f87610615e953b
yu-hir/module/local_source.rs 906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed
yu-hir/shadow.rs 687b49061273974fe874a8479a8db91ba24cc77fe92e6d2b96ae46a3626cf9dc
older graph-call note 56cc8d4d2d0260ffa01a3198a051a6da384f84ceaad209d8886d8c6504497018
imported theorem note cd2b84a84d16be8856766f0514a2f400cf224ac95b6e81e42d4a7a875036e113
top-level principles edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389
reference Typer.scala f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9
reference TypeSimplifier.scala 618b63f63e71c31890eb36cb18be474bfd31732173c159132306f0e14dc37d2b
```

Recommended next action: give the constructive prover this current emission
and require its projection statement to specify administrative-row treatment
and designated-root observation explicitly, while leaving mixed-port solving
and ordinary public scheme consumption separate and OPEN.

### Commit packet

- Exact leased path: `notes/progress/2026-10-11-invoke-value-projection-falsification.md`.
- Baseline: `1876f777358489d01c9755fa63a8d5876aa729a2`; direct dependency
  snapshots above. No dependency edits by this leaf.
- Claim/review: frozen static characterization and raw-shape falsifier;
  unreviewed, no semantic counterexample or gate closure.
- Checks: direct source/locator and SHA256 inspection; note-only integrity
  check recorded in the final report. No executable validation.
- Proposed checkpoint message: `research: audit invoke value projection against current source owners`.
- Shared-record deltas left for primary/curator: record the current literal
  reverse edge and fresh Lambda effect ports; distinguish expression/definition
  roots and internal graph consumption from public scheme publication; link
  this audit as bounded evidence. No shared records edited.
