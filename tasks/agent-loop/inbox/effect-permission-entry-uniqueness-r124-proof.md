# R124 existing R39 schedule application — revision 2

Status: **FROZEN / WRITES STOPPED / independent review pending**.
Outcome class: conditional application of existing mathematics to bounded
authenticated source evidence. No new theorem, model, whole-language instance
or source-qualified counterexample is delivered.

Session `EFFECT-PERMISSION-ENTRY-UNIQUENESS/20261102-R124`; assignment
`R124-ENTRY-UNIQUENESS-PROOF`, revision 2; sole author
`/root/r124_entry_uniqueness_proof`, registered lean_prover leaf. The initial
primary task and subsequent explicit resume on the frozen source receipt are
the activity receipts. Requested/effective model and effort UNKNOWN. Only
this exact leased handoff is changed; no descendants or scratch paths.

Sequential correction authorized by the primary after independent review:
revision 1 SHA-256
`aa77b36f11d725aadd5b72b5bc936c525c42e2545d4fbcc91680e524a0cf97d2`.
Its claim that a repeated Work::Visit allocates a fresh registration was wrong.
The correction below distinguishes preallocation per emitter from lookup per
Visit; all other claims and open gates retain their prior scope.

## Authority and authenticated inputs

Baseline `8914838a21ab2dcf62ccf14dddcec3ea91fd8446`, branch `yulang3`.
Contract SHA-256 `aca5c91ba535c9e2342bcd593bb6e8cffc062a506966f2777fcb818526fbc82e`;
manifest r1 `2f7648717daf58a5132291d395a9eb84f7d78ad5305fc87068505ae31d68cf57`.

| Frozen dependency | SHA-256 |
| --- | --- |
| R124 source r1 | `8a29f9eb9ba2ca7d5c45a2838ac81195887937d66b33776f3b8a8c2003d66d16` |
| R123 source r1 | `c2fe62592f85a8f6bbf3e5b1eecb29fdef26cb031a2894c0a417db1ab64c679a` |
| R123 proof r1 | `689588906f07efcf1908fca05d74e868eee5835b026582d79bf4cf8106b2ee90` |
| R123 outcome | `1ae9b4cc859bdc953c36fd65c592baaaa1f42c7146c555c69eab6f847209c240` |
| Corrected R39 Lean at `1f5835c276143537ec58ed81db96c7c108cea8e7` | `748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e` |

These hashes were independently recomputed. The source handoff was read in
full only after its freeze. Its eight manifest source pins are authenticated
by the source lane; I did not duplicate its Rust investigation or read dirty
source. The actual corrected R39 module was read using immutable `git show`.
Root AGENTS.md, preserved operating map, goal-driven rules, handoff protocol,
design authority, Lean skill and sources/execution references were consulted.

Original parent: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`
§§1,3,5, over every supported original source, lawful finite construction
history and actual retained extrusion occurrence, preserving original source
typing/principal coverage, scopes, complete Call/effect evidence and one shared
lawful strategy. The immutable Value birth-level induced-SCC correction is
`notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6. The immediate effect
policy is `2026-10-10-annotation-effect-hygiene-integration.md` §§1–1.2:
annotation permission, constraint-derived inflow and actual subtraction are
distinct, and unknown dependencies remain. Its §6 retracts the displayed
callback output; it supplies no expected result. Top-level inference
principles §§4–5 permit safe disposal of a private failed attempt and impose
no unconditional rollback/retry goal. No research draft changes that authority.

## Source result actually consumed

For one successful batch collection and ordinary single `execute`, the pinned
`SccPlan::build` constructor and freeze guards partition collected definition
roots without repetition or omission. Capture-order DFS and the source-root
execution loop execute each retained SCC member once, until early error stops
the execution prefix. This discharges R123's particular missing SCC-owner
source premise; it is static source derivation awaiting independent review,
not a checked Lean scheduler theorem.

For authentic retained carriers without `InterpolatedString`, the frozen
source induction traces all child creation and Work expansion branches.
Fresh child slots have one retained execution edge and one construction task;
metadata edges do not add visits. Thus a structurally reached annotated Lambda
emits its Entry once, if collection succeeds and its outer effects row exists.
Together with R123's source formation and action-order evidence, this excludes
the audited SCC repetition and ordinary traversal repetition routes for that
bounded first execution. It does not alone establish all PRE-state absences:
all writers, state interpretation and any required reuse facts remain separate.

Interpolation has a precise remaining premise. Each lowered interpolation
piece consumes the next CST node and checks that node's key against the
selected retained part. Injectivity of keys for distinct consumed nodes would
exclude selecting the same part/body twice, regardless of upstream piece
enumeration. The actual key constructor
`crate::source_identity::try_source_keys` / `source_keys` is outside the pinned
manifest. No collision or authentic duplicate has been exhibited. Nested
annotated bindings in interpolation bodies remain covered by this open edge;
the bounded non-interpolation result must not become a supported-language
restriction or be reported as an all-carrier result.

Global semantic member uniqueness across arbitrary multi-HIR world assembly
is also unestablished. The source lane distinguishes module member insertion
from the per-indexed-schedule execution loop. Its ordinary member/expression
schedule observations do not prove that all world inputs carry unique semantic
identities. No malformed repeated-world vector is promoted to a source witness.

## Existing R39 declarations and exact application

All names below have prefix `YulangClosure.ComputationPermissionEntryR39.`.
The actual module quantifies arbitrary `{Id : Type} [DecidableEq Id]` and
finite tables over complete branded identities. Its relevant definitions and
unchanged theorem signatures are:

```text
Valid e a f r :=
  f.owner = a.annotation.owner ∧ f.role = .computation ∧ f.scope = a.scope ∧
  e.recipes[f.recipe]? = some f.parameter ∧
  ownerLookup e.owners a.occurrence = some f.owner ∧
  sourceLambda e f = some (a.occurrence,f.parameter) ∧
  f.recipe ∉ e.occupiedDomains ∧
  a.registration ∉ e.retainedRegistrations ∧ r.variables.length ≤ 1

prepare_exact (e) (a) (f) (r) (port) :
  prepare e a = some (f,r,port) ↔
  e.formals[a.registration]? = some f ∧ a.annotation.row = some r ∧
  f.entry = some port ∧ Valid e a f r

constructed_entry_publication (e) (a) (f) (r) (port) (s)
  (hf : e.formals[a.registration]? = some f)
  (hr : a.annotation.row = some r) (hp : f.entry = some port)
  (valid : Valid e a f r) (nonempty : r.concrete ≠ []) :
  ∃ p, prepare e a = some (f,r,port) ∧ permissionFor a f r port = some p ∧
    p.concrete = r.concrete ∧ p.entry = port ∧
    publish a f r port true s = some
      ⟨s.permissions ++ [p], s.links ++ symbolicLinks a r port, s.inflow⟩

duplicate_or_domain_rejected (e) (a) (f)
  (hf : e.formals[a.registration]? = some f)
  (occupied : f.recipe ∈ e.occupiedDomains ∨
              a.registration ∈ e.retainedRegistrations) :
  prepare e a = none
```

Neither `Valid` nor `prepare` contains schedule uniqueness. `Inputs.schedules`
is used only by the explicitly historical `legacyScheduleGuard`; authentic
owner-local Lambda lookup replaces that invalid guard. Thus no R124 uniqueness
fact can be inserted as a newly required mathematical premise of R39.

For each actual invocation reaching the local publication point, project the
same PRE graph, actual action, registration and outer computation row to
`e,a,f,r,port,s`. The constructor's passed guards then supply the absence
conjuncts alongside the other identity/row equations. Under those concrete
equations, `(prepare_exact e a f r port).mpr ⟨hf,hr,hp,valid⟩` gives preparation,
and `constructed_entry_publication` constructs one shared permission witness.
`exact_row_retained` exposes every retained coordinate and literal equality of
the full ordered concrete row, preserving repeated members. Empty or
symbolic-only rows use `empty_concrete_local_case`; they construct no concrete
permission while retaining existing symbolic links. This is a written
application of existing mathematics, not an executed new proof term or an
established concrete Rust interpretation.

Publication denotes the local push after readiness, not whole-call `Ok`:
the later resource sample can fail after append. No rollback, empty vector on
`Err` or universal state-reuse law follows from these declarations.

## Multiplicity, rejection and progress

A repeated Work::Visit to the same source Lambda within one emitter reuses
the same preallocated registration and recipe. The immutable
`candidate_source.rs` 1098–1118 expression scan allocates them before traversal;
the Lambda Visit looks up the recipe at 1282 and FormalEntry registration at
1326. Repeated visits could therefore emit multiple Entry actions for that
same registration. If the first action retains its permission, a later such
action has the duplicate-registration membership premise, subject to the
same-PRE interpretation. This is one reason all-carrier Visit uniqueness
matters to ordinary progress. R124 establishes no reachable duplicate.

Repeated `emit_candidate_source` calls or distinct carriers instead allocate
fresh registration/recipe ranges. Such repeated emission is not automatically
rejected by `a.registration ∈ e.retainedRegistrations`, which compares the
actual integer of that invocation. R39 contains no semantic-occurrence
deduplication claim. A same-source duplicate across emitters cannot simply be
sent to the replay rejection theorem without its actual membership premise;
global multi-HIR semantic identity uniqueness remains the separate open edge.

For any actual replay of the same registration, whether from repeated Visit
or another replay route, if that registration is retained in the invocation's
PRE permission vector, or its
recipe has a domain, the corresponding exact PRE projection gives `occupied`
and `duplicate_or_domain_rejected` applies. A prior empty/symbolic-only row
does not itself retain a permission, so replay rejection cannot be inferred
merely from the fact that Entry was dispatched earlier. Ordinary cursor
advance and single execution exclude the audited replay routes; direct
internal calls, manual restart, later execute/reuse and undo remain outside
that result. No authentic replay counterexample was found.

Successful-publication soundness quantifies over invocations that reach the
publication point and uses the guards that actually passed. It does not need
a theorem that every dispatched Entry must pass. Ordinary inference progress
must additionally show that a supported natural input does not fail because
of erroneous scheduling or earlier incompatible publication. R124 narrows
that latter obligation through real SCC and non-interpolation source facts,
without closing either parent claim or changing their quantifiers.

## First remaining premise and owners

For the direct R39 application, the first missing edge remains the concrete
same-PRE Rust-to-R39 interpretation, owned by source-to-Lean correspondence
intake at the batch/HIR and graph-state owners. Required equations include:
`occupiedDomains` membership equals actual `formal_domains` key membership;
`retainedRegistrations` equals the registration projection of the same actual
permission vector; `s.permissions` interprets that vector with full coordinates,
row order/multiplicity and complete effect/type-argument identities. Formal,
recipe, owner-local Lambda, occurrence, annotation, scope, entry port and
symbolic endpoint equations must commute with that same projection. R39
Inputs and State are separate structures; consistency is not automatic.

Stable requests for the primary:

- `R124-SAME-PRE-INTERPRETATION-1`: reuse R123's request at the actual constructor
  input. Required output is concrete projection/commuting equations; falsifier
  is an authentic state/key/owner mismatch. No new conditional model is needed.
- `R124-INTERPOLATION-KEY-INJECTIVITY-1`: if extending the progress derivation to
  every admitted carrier, authenticate the actual source-key owner and apply
  the existing consuming-node equality checks. Required evidence concerns
  distinct CST interpolation nodes in an admitted retained carrier; falsifier
  is an authentic key collision or repeated part selection that passes them.
- `R124-WORLD-MEMBER-IDENTITY-1`: only if the selected progress claim needs
  global multi-HIR semantic identity uniqueness, trace actual world assembly
  and map insertion. Arbitrary abstract duplicates do not meet that burden.

R121's indexed consumer read remains another open correspondence edge. Nested
callback `[Result]` rows do not become the outer computation row. Concrete
inflow propagation, provider arrival, Catch/residual subtraction, native
simulation, original A/B preservation/shared strategy, whole-language
soundness, principal coverage, normal progress, termination and production
remain OPEN. R111 resource gate and NO_SAFE_CODE_SLICE are unchanged.

## Verification, resources and cessation

No theorem or Lean source was authored. Fresh Lean/Lake execution, versions,
goals, diagnostics, printed types, axiom audits and skill checker are **NOT
RUN**, as the fixed packet explicitly forbids execution. The signatures above
come from actual immutable definitions. Inherited R39 revision-2 receipts,
already distinguished by R123, report complete axiom list
`[propext, Quot.sound]` for `prepare_exact`, `prepare_of_valid`,
`constructed_entry_publication`, `exact_row_retained`,
`duplicate_or_domain_rejected` and `empty_concrete_local_case`. These are
historical receipts, not R124 kernel/axiom checks.

Existing R39 represents arbitrary finite exact keys, owner-local Lambda and
other expressions, empty execution schedules, full ordered concrete rows,
zero/one symbolic variable and the local generated-link trace. It supplies no
concrete whole-language instance, all-carrier execution theorem, native
propagation, failed-state restoration, actual subtraction or consumer proof.

Actual commands: bounded `cat`, `sed`, `rg`, immutable `git show`, `sha256sum`,
read-only Python/hashlib extraction and clock lookup; one apply_patch wrote
this handoff. Hash comparisons exited 0. Broad batched policy output was
truncated, then original parent/correction and relevant definitions were read
through focused output. Initial bounded intake ended WAITING with no writes;
the primary explicitly resumed this same lease after source freeze. No new
budget is asserted beyond the primary's fixed finite allocation; no heavy
process, build, test, checker, generated/cache output, environment/storage
probe, installation, network, descendant, nested CLI or Git mutation occurred.
CPU/RSS were not measured.

Revision-2 correction additionally read only immutable
`candidate_source.rs` at `852ab889cee2f4cfe04da3a1e8c9dd96f9758845`,
lines 1085–1130 and 1278–1336, confirming allocation before traversal and lookup
inside Visit. One apply_patch corrected this sole handoff; no Lean execution
or other file write occurred. Independent delta review remains pending.

**All writes STOPPED at revision 2.** No background process or descendant
remains. Sole artifact is this handoff; independent review and primary
integration remain pending.
