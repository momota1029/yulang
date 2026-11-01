# R229 upper-insertion owner correspondence — frozen revision 1

## Packet and status

- Sprint: R229 contract revision 2, SHA-256
  `1d3ffff03cdeb6f1bbe06fb3f99fb563ebda3a2eb74b74e8c31ba401a425608a`.
  Revision 1 (`96b6ef8de510e3147f315a84f874ab7af5af2affad42f9d02e59c4c4165ea952`)
  was superseded only to correct the structural-syntax dependency pin. Luna
  notified this worker to pause writes and then explicitly resumed this packet.
- Baseline: `5bfbf47a4b1cc28b0a56c33bc0fdef902b8292cf`, branch `yulang3`.
- Worker/assignment: `/root/r229_upper_insertion_owner_map`; direct launch from
  `/root`, this session. Requested role: researcher; observed model/effort:
  UNKNOWN. No contributing descendants.
- Objective/method: inspect authenticated native physical insertion, restoration,
  replay and live-task dispatch; derive their exact relation to R212's partial
  `CoreState.insertPendingUpper`, without proposing another transition system.
- Claim class: **source-native-evidence**, with one source-qualified operational
  discriminant and a separately labeled candidate abstraction premise. No
  machine-checked theorem, independent review, source-language realization,
  whole-run correspondence, or gate closure is claimed.
- Exact lease and only output:
  `tasks/agent-loop/inbox/abstract-upper-insertion-invariant-r229-owner.md`.

Governing scope: R229 “Parent outcome and exact scope,” “Fixed dependencies and
owner inspection,” lane 2 and stop conditions; R212 definitions at
`AbstractSimpleSubCore.lean:144–189`; top-level inference principles §§1–4 and
§1.1; design-authority “Authority order”; research-lab's source-evidence and
independent-review boundaries; git-concurrency “Disjoint-file mode.” Accepted
meaning remains unchanged: this is an upper-only partial abstract operation,
not complete mixed Function/effect resolution or accepted solver execution.

## Authenticated inputs

SHA-256 values at inspection and freeze:

| Input | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `crates/yu-solver/src/lib.rs` | `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be` |
| `notes/theory/lean/YulangClosure/AbstractSimpleSubCore.lean` | `023635d283f9a00e906ec965a6eaa5595eab21f2b93f353a1d5ea0ede0bffb6c` |
| Exact restoration callsites, `crates/yu-solver/src/candidate_scheme.rs` | `6072c73bc1a1629f025dcaf61fcbed98c738d93f8993bd81182a391d1ad4d89e` |
| Exact canonicalization adapter, `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |

The last two are narrowly inspected callsite dependencies, not newly approved
semantics. No input was edited. No uncommitted sibling artifact was consumed as
a proof premise. R223 proof development and its pending R229 replacement are
outside this source lane.

## Actual data and operation relation

R212 initial storage allocates `valueLevels.map initial` and
`effectLevels.map initial`, empty lower/upper lists and identity representative
vectors. Its operation takes the pending head, requires a variable lower end,
looks up that variable's representative and physical row, checks **every**
variable occurrence in the full upper term at that occurrence's own kind and
index, and requires dependency level ≤ owner level. It prepends the upper term
and replaces pending with `row.lowerBounds.map replay ++ rest`. It does not
check status, mark terminal acceptance, allocate rows, or perform extrusion.
Function upper terms can have dependencies of both kinds; “same kind” does not
mean every nested Function port has the outer value kind.

Native `ValueBounds`/`EffectBounds` (`lib.rs:4257–4287`) separate direct row IDs
from exact non-variable endpoints, independently on each bound side. Levels and
representatives live elsewhere. `candidate_insert_bound_with_evidence`
(`candidate_extrusion.rs:702–874`) canonicalizes both ends, requires an allocated
same-kind owner row, selects one of eight physical lanes, obtains admission
and emission capacity, journals the row and **appends** one entry at the old
lane length (`:724–725`). A subsequent physical readback reconstructs the exact
`BoundKey` from the actual addressed lane; it must equal the canonical intended
key (`:856–860`) before capture registration/emission.

Thus an individual successful visible append retains one occurrence, including
an equal existing endpoint: this helper contains no duplicate-elimination
branch. Abstract lists prepend and native lane vectors append; native row/nonrow
splitting also loses a unified chronological order unless additional evidence
is used. A literal list equality is unjustified. A multiset projection can
ignore these order differences, but needs an independently defined, justified
endpoint-to-full-term decoder. Native endpoint keys are not R212 `Term` values.
The helper does not itself perform R212's recursive dependency-level check.

## Write-before-replay and exact replay domain

1. `candidate_apply_value` (`:1115–1144`) and `candidate_apply_effect`
   (`:1147–1170`) canonicalize, return immediately for equal canonical endpoints,
   choose an owner/side, call insertion, and only then call replay. Row/row
   comparison chooses the lower endpoint's upper side when upper level ≤ lower
   level; otherwise it chooses the upper endpoint's lower side. These native
   operations therefore include a lower-insertion case excluded by R229.
2. For an inserted upper (`Polarity::Negative`), `candidate_opposite_count`
   counts direct lower rows plus exact non-variable lowers for that owner's
   kind (`:877–901`). `candidate_opposite_bound` reads direct entries first,
   then exact entries, canonicalizing the result (`:902–936`). Replay creates
   `lower = existing opposite`, `upper = inserted bound`, using Value or Effect
   live tasks according to kind. For positive insertion the ends reverse.
3. Ordinary `candidate_replay_bound` (`:1070–1112`) saves the count once and
   reads each opposite by live index, retaining contextual replay input keys
   and, for value tasks, diagnostic edges. The replay driver's internals were
   not inspected; this report establishes the called task and visible ordering,
   not the driver's preservation laws or queue-completion semantics.
4. Restoration `candidate_begin_bound_restoration` (`:966–985`) asserts an idle
   worklist, reserves restoration storage, completes the insertion, canonicalizes,
   then saves the opposite count and operation. `candidate_step_bound_restoration_child`
   (`:1004–1067`) retires at the saved count, completes an active child before
   advancing, or rereads the **live canonical owner** and saved index before
   starting the next child. Earlier children can append bounds or redirect
   representatives; the code explicitly anticipates this. This is not a copied
   snapshot of abstract lower terms.
5. Restoration is an actual non-test route: `candidate_scheme.rs:4508–4517`
   freshens then drives each bound restoration; `:4969–4993` chooses owner/side
   and passes FreshUse evidence; `:5430–5444` retains/steps a local-use cursor.
   The convenience wrappers at `candidate_extrusion.rs:942–964` are `cfg(test)`;
   they are not the evidence of the non-test call route.

R212's replay map and native replay agree on the *orientation* of a negative
upper insertion. They differ in storage ordering, runtime evidence, live
representative rereads and child execution. In the **proved-empty-lower**
subdomain targeted by R229, the abstract replay list is empty. Corresponding
native direct/exact lower lanes would also give count zero, provided that
correspondence is established. R229's abstract proof alone cannot establish
that native premise.

## Live-task dispatch prevents an automatic equation

`lib.rs:210–229` gates candidate modules on `shadow-apply-candidate`;
`candidate_graph.is_some()` selects their runtime route (`:14106–14108`,
`:13830–13841`, `:16302–16304`). `LiveConstraintTask` has Value and Effect
variants (`:4290–4293`) in one typed worklist.

Candidate drains perform transport, context execution, then dispatch
(`:14446–14464`). They may settle intrusion when the queue becomes empty
(`:14413–14416`). Dispatch can skip a current memoized pair; the candidate
current test additionally uses the admitted relation and intrusion generation
(`:13593–13603`, `:14553–14567`). Effect application is skipped when the context
already consumed the task (`:14557–14560`). Value dispatch can canonicalize and
requeue, replay a retained extrusion rewrite, diagnose incompatible shapes,
decompose structure, or extrude a nonrow endpoint before applying the row rule
(`:14569–14631`, `:14811–14903`). Four Function ports produce both Value and
Effect children (`:14905–14932`); this syntax does not establish the semantic
joint Function/effect resolver.

Canonical adapters call the native representative owners
(`lib.rs:11925–11930`, `:13577–13582`;
`candidate_intrusion.rs:293–297`). Their existence does not prove identity
representatives across native runs. R212's one queue-head operation models
none of these dispatch guards, contextual transports, diagnostics, children,
representative changes or accepted return conditions.

### Smallest direct operational discriminant

Take kind value; one allocated row at level 0; identity representative; one
source-Value vertex with birth 0 and no references; and exactly one demand
`var 0 <: var 0` with origin = receiver = 0. No effect rows, publications or uses.
This is a valid R212 input. Evaluating the defining clauses by hand:

- The pending head is variable-lower, representative lookup is 0, and its sole
  upper dependency has level 0 ≤ 0.
- `insertPendingUpper` returns `some` with pending empty and row 0's upper list
  equal to `[var 0]`; there is no replay because its lower list was empty.
- The analogous native **direct `candidate_apply_value` call**, on canonical
  `ValueRow(0), ValueRow(0)`, returns `Ok(0)` at `:1120–1121` before insertion.
  The effect version has the same early return at `:1154–1155`.

This refutes a raw equation identifying R212 upper insertion with native direct
apply while preserving the physical upper-bound multiset. One row and one
demand suffice; zero rows cannot admit the variable lookup and zero demands
cannot take the operation. This is a source-body derivation, not an executed
native fixture or source-program counterexample. It does not refute R229's
abstract invariant. Restoration directly invokes insertion and does not have
this self-pair shortcut, so the witness is not a restoration counterexample.

## Claim boundary and missing premise

A candidate local bag simulation would need explicit hypotheses: both stores
related by a total allocated endpoint decoder; matching row identities and
metadata; canonical representatives stable; full upper dependencies at permitted
levels; dispatch actually reaches one negative append; matching demand ownership
and multiplicity; empty matching lower lanes; and all invoked evidence/capture
helpers preserving the chosen projection. Under those hypotheses, the visible
append and empty replay describe the same added upper clause up to permutation.
These are **candidate bridge premises**, not facts proved by this inspection.
No source-to-abstract equation follows here, including for successful native
sessions. In particular, self-pair elision and memo/context consumption require
an explicit simulation or stuttering relation rather than literal equality.

Parent application: this evidence bounds how R229 may be described and supplies
an exact countercheck against promotion to native conformance. The constructive
lane owns proofs over successful R212 histories. A future separately leased
source bridge must establish native projection, dispatch coverage and the
admissible elisions; Luna owns its admission. Original parent delta remains 0.

## Checks, coverage and resources

Commands were read-only `git rev-parse HEAD`, `git status --short`, `cat`, `rg -n`,
`nl -ba ... | sed -n ...` and `sha256sum`, followed by writing this exact leased
note. Reads covered the R212 initial/insert definitions, both native insertion
kinds and all eight physical lanes, apply/replay/restoration branches, exact
fresh-use restoration callsites and the live-task seams cited above. Inputs
were rehashed after writing. No Rust/Cargo/test/Lean process, executable checker,
random seed, bounded enumeration, mutation or benchmark was run. No oracle is
claimed: Rust bodies and Lean definitions were compared directly, sharing only
the pinned contract and selected terminology. A checker assuming these rules
would not prove their source correspondence.

Unverified: helper implementations for context/replay/evidence/capture,
representative union/find laws, complete source generation and term decoding,
restoration failure recovery, native acceptance/publication, structural effect
subtyping, R223 theorem types/axioms, and the constructive R229 module. Fallible
calls occur before and after physical append, including readback/capture/sample
operations; this report makes no rollback or failed-call equivalence claim.
No search was started or left incomplete. Local tool calls were lightweight,
single-process reads; CPU/RAM peak and precise wall-time are unmeasured, with
completion within the 900-second lane limit. No build/cache output was created.

Recommended next action: review this frozen owner evidence together with the
constructive lane's frozen R229 proofs, retaining the partial-abstract scope and
leaving native simulation as a separate obligation.

## Stopped-writing receipt and commit packet

Worker state: STOPPED after revision 1 submission; no descendants or unresolved
child leases. This note is the complete output. Its final byte hash is supplied
in the submission message because embedding that hash would change these bytes.
No further writes are authorized by this receipt; repairs require a new revision
coordinated through Luna. Review status: **NOT_RUN**, producer evidence only.

- Exact leased path: `tasks/agent-loop/inbox/abstract-upper-insertion-invariant-r229-owner.md`.
- Baseline SHA: `5bfbf47a4b1cc28b0a56c33bc0fdef902b8292cf`.
- Dependency delta: only contract rev1 → rev2 as recorded above; authenticated
  Rust owners and R212 source unchanged; narrow callsite hashes recorded above.
- Checks already run: baseline/status reads, declaration/callsite inspection,
  all stated input SHA-256 checks; no compilation or tests.
- Proposed checkpoint message: `research: map R229 upper insertion to native owner ordering`.
- Shared deltas intentionally deferred to Luna/curator: record source evidence
  received and review pending; preserve root/package counts and native bridge
  OPEN; do not promote R229 to native or whole-solver correspondence.
