# R122 immutable-source entry pre-state receipt — revision 1

Status: **FROZEN / WRITES STOPPED / independent review pending**.
Assignment `/root/r122_entry_source`; source-evidence leaf, sole author, no
descendants. Requested/observed model and effort UNKNOWN. Actual primary
NEW_TASK and this turn establish activity; no role configuration establishes
an execution receipt. Sole changed/leased path is this handoff.

Sprint `EFFECT-PERMISSION-ENTRY-PRESTATE/20261102-R122`, contract SHA-256
`b0611e6bfaf5633887fcf566faeaeb5c7f29d7b8d68e6b09fece50fddb6cdcf7`.
Method: immutable Rust writer/guard/schedule inspection and explicit conditional
derivation, compared with existing R39 inputs. No new model or declaration.

## Baseline, authority and dependencies

Source line numbers below refer only to these immutable blobs:

| Input | Commit | SHA-256 |
|---|---|---|
| `crates/yu-solver/src/candidate_source.rs` | `d177c46ec61fcadd70a3d587c2f8934f6bc91f46` | `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a` |
| `crates/yu-solver/src/candidate_effect.rs` | `1f5835c276143537ec58ed81db96c7c108cea8e7` | `477b7fe56beb9eb08a2ff46ecee93785aee25b1d929d19578ea29f4c37a2bf26` |
| `notes/theory/lean/YulangClosure/ComputationPermissionEntryR39.lean` | `1f5835c276143537ec58ed81db96c7c108cea8e7` | `748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e` (manifest; read, not independently rehashed here) |

Independently rehashed frozen handoffs match the manifest: R39 Rust
`c32634e3ef4a973883a25b6115e77adab9e0229d077c970f84d72e4ad7f1f142`, proof
`aa8a9a8aae5f4b42779bcf752e5e8b5f6bb1e4474b5f4d49254fc58a03b4d5de`, outcome
`508511fe154775d9ec2ea906da594364f4a650255f86b01d3bd85ba575d32c25`; R114 source
`807cd75ad2b7eb1b4e24543b4502434366f3c59522eec60226c915eaf1115a75`, proof
`9bb5464cb99eefb26c519e98663844a9064f1861a9e5a2cbd50076b92c919e5f`, outcome
`3ef95f7af7c1c1e6d6cdb4873b1070d01ec2ee40a5e88115815480553761cfc3`.
No dependency changed. R114 inspected a DIFFERENT effect blob; its later
permission binders and line numbers are not silently imported into this blob.

Read root operating instructions; research-lab and preserved baseline;
design-authority (Authority order, Approval and implementation gate);
git-concurrency (Integration ownership, Disjoint-file mode); sprint skill and
`yulang-proofs` source-bridge instructions. Children do not dispatch or own Git.
Governing meaning remains original preservation §§1,3,5 and annotation hygiene
§§1–1.2, with inference principles §§1,3–5: permission is separate from inflow
and actual subtraction; the outer computation row is separate from nested
Function result permissions; safe termination may replace abnormal recovery.
No selected semantics, supported-source quantifier or parent gate is changed.

## Exact result and derivation

Outcome class: **bounded source characterization plus conditional derivation**.
Both R39 absences are directly enforced for a guard-passing entry invocation.
This is not a derivation that every reachable dispatched entry passes its
guard, and no source-qualified counterexample has been established.

Let `S` be the actual graph effect-algebra state at invocation of
`candidate_formal_entry_annotation(j, a, o, scope)`; let `f` be the actual
`batch.candidate_calls.formals[j]` and `p = f.recipe_position`. Hypotheses:
the graph exists, the registration lookup succeeds, the referenced immutable
batch/HIR lookups are defined, and execution passes the composite rejection
guard at effect:1632–1642. These are program-path hypotheses, not asserted
global invariants. Before this guard the body only reads the row, clones the
registration and reads HIR/identity data; it makes no graph mutation.

The guard rejects when

```
S.formal_domains.contains_key(&p)
  || S.formal_entry_permissions.iter().any(|q| q.registration == j)
```

Consequently passage implies `p` is absent from the actual domain-key set and
`j` is absent from the actual permission-registration projection in the
INVOCATION PRE-state. This uses the negative guard, never a later successful
lookup or post-state absence. It also holds immediately before the permission
literal at effect:1651: intervening work reads `entry_effect`, allocates/copies
the concrete vector, and does not mutate either collection. Any call returning
`Ok(())` necessarily passed this guard. Allocation/resource/constraint failure
can prevent success despite valid absences.

This result requires no first-entry reachability theorem. Conversely, the
guards alone do not prove absence before an arbitrary rejected call. Arbitrary
malformed states are not source counterexamples.

## Registration, owner and action correspondence

1. **Birth (source:1104–1118):** a Lambda appends its exact parameter identity
   at fresh recipe position `p = parameter_recipes.len()`, and appends a formal
   at fresh registration `j = candidate_calls.formals.len()`. It retains exact
   source owner, owner-local Lambda expression index, parameter identity,
   recipe and scope. Outer `annotation.ty.effects.is_some()` selects
   Computation; native root and entry effect begin `None`. Recipe and
   registration are different indices: root parameters and record fields can
   consume recipe positions without formal registrations.
2. **Initialization (source:2303–2325):** checks recipe/formal identity and
   `native_root.is_none()`, obtains the positive Parameter endpoint, allocates
   a fresh effect at the recipe's level for Computation, and writes native
   root and entry into the same registration. Neither collection under audit
   is written here. Reinitialization is rejected for already initialized
   registrations; a partially failed initialization has no rollback body here.
3. **Authentic source owner (source:1043–1071):** emission requires pointer
   identity with that HIR's retained LocalSource, matching receiver/root kind,
   HIR-owned occurrences and consistent occurrence-to-owner mappings. This
   does not establish all upstream HIR formation restrictions.
4. **Planning (source:1280–1353):** `BeginLambda`, optional `RecordParameter`,
   optional `UnitParameter`, then `FormalEntry` if outer effects exist, then
   `FormalAnnotation`, followed by defaults/body work. Annotation+unit returns
   an error before admitting a complete schedule. Ordinary annotated scalar
   formals therefore have Entry before Annotation. Completed actions are
   stored in the selected root/expression/member schedule (2215–2257).
5. **Dispatch (source:2402–2464):** waits leave the current action unexecuted;
   Execute selects the actual `actions[frame.next]`, clones it and invokes
   `execute_candidate_action`. Entry dispatch passes its registration and
   actual annotation/occurrence/scope; Annotation passes the recipe. The cursor
   advances only after successful execution. Local publication is a distinct
   stage and cannot itself act as an Entry/Annotation dispatch.
6. **Direct identity checks (effect:1623–1643):** actual row exists and has at
   most one symbolic variable; registration is Computation; annotation owner,
   scope, recipe/formal, occurrence owner, owner-local Lambda and exact Lambda
   formal all match; entry exists. The lookup uses `f.lambda` in the owner's
   LocalSource, never in the separate expression schedule vector. This reuses
   R39's corrected lookup domain.

## Writer/clear inventory in the complete leased blobs

| Owner in corrected effect blob | Membership change |
|---|---|
| `State` derived Default, 137–144 | Fresh map/vector are empty; no evidence here that every actual graph uses that constructor. |
| `candidate_record_parameter`, 1697–1733 | Reject existing recipe; insert its negative domain at 1731; append new recipe key to active route undo if present. |
| `candidate_unit_parameter`, 1736–1753 | Same check, domain insertion at 1749, optional undo key. |
| `candidate_formal_annotation`, 1756–1839 | Reject existing recipe at 1761; publish nested permissions and insert negative formal domain at 1817; journal new key if present. |
| `candidate_formal_entry_annotation`, 1622–1695 | Reject occupied recipe/registration; for nonempty concrete row append one entry permission at 1681. Does not insert a formal domain. Empty concrete rows append nothing; symbolic tail relations remain separate. |
| `State::checkpoint`, 361–386 | Save permission-vector length; start an empty domain-key undo list. Taking a checkpoint does not clear current membership. |
| `State::rollback`, 388–397 | Remove exactly journaled domain keys; truncate entry permissions to checkpoint length. Neither operation inserts a member. |

Identifier searches across both whole pinned blobs found no other production
write/clear/assignment to these collections. `candidate_source.rs` contains no
direct collection writer. Reservations/byte accounting are not membership
writes. Test-module references were inspected as source text only and are not
evidence of normal execution. The domain field is `pub`; the entry-permission
field is private. Thus these two files cannot certify an exhaustive repository
writer inventory for domains, whole-State replacement, graph installation or
transaction restoration. State-brand initialization does not imply emptiness.

## Ordering falsifier and lifecycle boundary

**Record-pattern candidate:** if one authentic Lambda has both
`record_pattern = Some(fields)` and an outer effect annotation, the planner
emits `RecordParameter(p)` BEFORE `FormalEntry(j)`. A successful record action
inserts `p`; the entry then rejects at its domain guard. The local preflight
(source:623–628) checks annotation row cardinality and value shape, and contains
no record-pattern/annotation exclusion. However emission requires authentic
HIR LocalSource, not a manually constructed record. No exact HIR lowerer or
handoff establishing that combination's source admissibility is present in
the R122 manifest/read lease. Therefore this is an **unproven source-admissibility
possibility**, not a source-reachable obstruction or a minimized supported
source counterexample. No source syntax witness is invented. In R39 terms the
occupied input would force `prepare = none`, but actual reachability is open.

**Normal order:** on a first ordinary scalar schedule with initially absent
keys and no intervening external writer/reentrant action, Entry precedes the
same recipe's Annotation. Annotation therefore cannot already have published
that domain from this earlier prefix. These italicized lifecycle premises
remain conditional: the source walk alone does not establish a global
first-execution/no-reuse invariant for every authentic source.

**Repetition:** normal successful stepping moves forward, so it does not
repeat an action in one retained frame. Successful end clears `source`
(source:2437); `begin_candidate_source` starts at zero and checks only existing
frame, local capture stack and Lambda depth (2369–2374), not completed schedule
identity or prior domains/permissions. It has no seen-registration registry.
Consequently an externally permitted rerun of a completed same schedule could
encounter a domain from its prior Annotation, and a nonempty concrete entry
permission from its prior Entry. FormalAnnotation can precede a later Entry
across such reruns. No authorized source caller enabling that rerun is proved
inside this read set, so this is a caller obligation, not a counterexample.

**Failures/retry:** Entry pushes permission before its fallible final resource
sample (effect:1681,1690); Annotation/record/unit likewise have a fallible sample
after domain insertion. No collection rollback is local to those bodies.
`step_candidate_source` does not increment the cursor on `Err` (2453–2454), so
a direct retry of a failed-after-publication Entry can see an existing
registration. It is then rejected before another append. A domain-publishing
action's repeated call is similarly rejected. Earlier constraint/allocation
failure can occur before publication; it does not by itself prove full state
restoration. Entry's empty-concrete case has no entry-registration marker.

The synchronous wrapper clears only the source frame on drive error
(source:2358–2367); it does not clear domains, permissions, Lambda depth or
capture stack. Thus a failed inner Lambda may also leave nonzero depth and
prevent restart. This prevents treating every failure as a freely repeatable
trace. Route undo is optional at insertion sites; actual checkpoint capture,
transaction boundaries, frame restoration, graph discard and permitted retry
owners are outside these files. Existing rollback code supports restoration
WHEN the correct checkpoint/journal is installed and applied; it does not prove
that the real caller does so, or that it should retry rather than stop.

**First missing global edge:** prove at the actual graph/schedule caller owner
that an authentic schedule reaches each Entry for the first time on a suitable
state, and that failed or completed state is never reused without the relevant
invariants. This includes graph construction, external domain writers,
checkpoint/journal ownership and authentic HIR pattern/annotation formation.
R114 assumes successful initialization/actions and explicitly omits all-caller
reachability; its receipt supplies no missing universal premise. Inference
principles permit safely discarding/stopping a failed private attempt; they do
not establish that this particular caller implements that policy.

## Exact mapping to existing R39 `Valid`

Use actual PRE-state projections, with exact branded IDs preserved:
`occupiedDomains = keys(S.formal_domains)` and
`retainedRegistrations = map (.registration) S.formal_entry_permissions`.
Map `a.registration = j`, `f.recipe = p`; map recipes, formals, source owners
and owner-local Lambda from the very same batch/HIR used by this call. A finite
list representation must preserve precisely these membership tests; no actual
Rust-to-Lean projection equality is supplied by this source inspection.

Under those explicit equations, guard passage supplies precisely R39
`f.recipe ∉ occupiedDomains` and `a.registration ∉ retainedRegistrations`.
The other guard clauses supply its owner/role/scope, recipe identity,
ownerLookup, sourceLambda and row-variable-bound fields. The actual table,
row and entry lookups supply the additional premises of `prepare_exact` /
`prepare_of_valid`. If either member is present, `duplicate_or_domain_rejected`
matches the rejection path. No source-wide success is inferred from these
finite-model theorems. Nonempty concrete rows and subsequent successful
publication are separate conditions for `exact_row_retained`.

## Commands, coverage, resource receipt and next action

Commands: `cat`/`sed` for the exact rules/contracts/frozen receipts;
`rg --files` for the initially missing manifest locator; immutable
`git show COMMIT:PATH` piped to bounded `rg -n`, `sed -n`, `head` or
`sha256sum`; handoff `sha256sum`; `apply_patch` for this sole leased output.
The first guessed manifest name lacked `-r1` and returned exit 1; the exact
manifest was then found/read. Initial output truncation was followed by narrow
source/handoff reads. No compiler, checker, test, build, cache, environment or
storage probe, scratch/copy, Git mutation, dirty/quarantined Rust read, network
or descendant. Seeds, enumeration ranges and executed mutations: none.

Coverage: every identifier occurrence in the two pinned blobs and all production
writer bodies, planner/preflight/init/dispatch bodies listed above. This is not
whole-repository caller coverage. Oracle independence: the evidence comes from
actual immutable source branches, independently of R39's supplied transition
model. Its shared assumptions are Rust control-flow/container semantics and
the stated exact identity/projection equations; no separate runtime/source
oracle validates HIR admission, external caller policy or buildability.
Failure of a guard, unknown graph initialization, external mutation/reuse,
changed pinned bytes or missing projections prevents a global application.

Budget ≤300 seconds, lightweight read processes only; no heavyweight process.
Exact CPU, peak RSS and elapsed/remaining wall time were not measured. No
background process or descendant remains; **all writes stopped at revision 1**.
No independent review or theorem closure is claimed. Parent effect hygiene,
soundness, principality, termination, native consumer and production stay OPEN.

Recommended next action: primary lease the exact immutable HIR constructor and
graph/schedule transaction caller owners to discriminate the record-pattern
case and prove or refute first-entry/no-unsafe-reuse; reuse the guarded R39
derivation without adding another assumed transition model.

## Commit packet

- Exact leased/changed path: `tasks/agent-loop/inbox/effect-permission-entry-prestate-r122-source.md`.
- Baseline SHA: `d177c46ec61fcadd70a3d587c2f8934f6bc91f46`; corrected effect/proof baseline `1f5835c276143537ec58ed81db96c7c108cea8e7`; dependency hashes above, none changed.
- Review: frozen, independent review pending; guarded source derivation only; universal action-prestate reachability OPEN.
- Checks run: immutable source searches/body inspection, exact source/receipt SHA-256 comparisons; no executable verification.
- Proposed message: `research: distinguish R122 guarded entry absence from source reachability`.
- Shared-record deltas left to primary/curator: record both direct guards as reusable conditional evidence; retain first-entry/reuse/HIR admissibility and original parent gates OPEN; dispatch exact missing owners. No shared file changed.
