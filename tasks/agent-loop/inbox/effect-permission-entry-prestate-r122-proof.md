# R122 existing-theorem application — revision 1

Status: **FROZEN / WRITES STOPPED / independent review pending**.
Outcome: conditional application of existing R39 mathematics; **no authenticated
concrete Rust-to-Lean instance and no universal entry-prestate theorem**.

Sprint `EFFECT-PERMISSION-ENTRY-PRESTATE/20261102-R122`; contract SHA-256
`b0611e6bfaf5633887fcf566faeaeb5c7f29d7b8d68e6b09fece50fddb6cdcf7`;
input manifest SHA-256
`9976ec1017181a8a5396db74b0ea4a03c6ccda31c272b24c831e136d1cc796d3`.
Assignment `/root/r122_prf`; sole author, no descendants. Actual primary NEW_TASK
and this turn establish activity. Requested/observed model and effort UNKNOWN.
Sole leased and changed path is this handoff; no Lean/source declaration changed.

## Original claim, correction and frozen inputs

Read root AGENTS.md and preserved instructions, goal-driven sprint rules, exact
contract/current state/handoff protocol, yulang-lean-proofs and both references.
Original parent is `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`
§§1,3,5: every supported original source and lawful finite history, actual
retained extrusion pairs, original source typing/principal coverage/scopes/full
Call/effect evidence and one joint lawful strategy. Current qualification is the
immutable Value birth-level induced SCC rule in
`notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6. No source feature or
quantifier is removed. Research manuscripts do not establish semantic authority.

The immediate policy is Authoritative
`notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1–1.2:
permission, constraint-derived inflow and actual subtraction remain distinct;
unknown symbolic dependencies survive. Its §6 retracts the claimed callback
output; that example is no oracle. Inference principles §§1,3–5 preserve ordinary
Simple-sub and permit safely stopping/discarding a failed private attempt;
they do not prove that an actual caller implements the necessary lifecycle.

R39 revision 2 corrects registration.lambda from an execution-schedule index to
the exact owner's LocalSource expression index. Definition-backed sources with
empty expression schedules remain represented. Current manifest-authenticated
R39 outcome additionally records the staging-placement error and corrective
commit; the historical full working blob is not the committed source baseline.

| Direct dependency | Revision / SHA-256 |
| --- | --- |
| candidate_source.rs | `d177c46ec61fcadd70a3d587c2f8934f6bc91f46` / `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a` |
| candidate_effect.rs | `1f5835c276143537ec58ed81db96c7c108cea8e7` / `477b7fe56beb9eb08a2ff46ecee93785aee25b1d929d19578ea29f4c37a2bf26` |
| ComputationPermissionEntryR39.lean | `1f5835c276143537ec58ed81db96c7c108cea8e7` / `748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e` |
| R39 Rust / proof handoffs | `c32634e3ef4a973883a25b6115e77adab9e0229d077c970f84d72e4ad7f1f142` / `aa8a9a8aae5f4b42779bcf752e5e8b5f6bb1e4474b5f4d49254fc58a03b4d5de` |
| Current corrected R39 outcome | `508511fe154775d9ec2ea906da594364f4a650255f86b01d3bd85ba575d32c25` |
| R114 source / proof / outcome | `807cd75ad2b7eb1b4e24543b4502434366f3c59522eec60226c915eaf1115a75` / `9bb5464cb99eefb26c519e98663844a9064f1861a9e5a2cbd50076b92c919e5f` / `3ef95f7af7c1c1e6d6cdb4873b1070d01ec2ee40a5e88115815480553761cfc3` |
| R121 outcome | `0e910bde2b5c3bc552a09a9c19172f3c9cf492628b673b9b50f72c09aab400b1` |
| R122 source handoff revision 1 | `a9191683817369d96c94c74ffe737825ab83e7ee5a5ca3ee2eb491574ff20612` |

These hashes were actually checked with immutable `git show ... | sha256sum`
or named frozen-record `sha256sum`. No dependency changed. The historical R39
outcome inside commit 1f5835c has hash `b162fda9a5f410c1031c6018854b30bca411dda75adbf72840f52a95d883b6a1`;
the current outcome above contains the corrective integration receipt and is
the manifest-selected record. R114's different effect blob and later binders
are not silently imported into R122's corrected source.

## Exact existing theorem surface

All names below have prefix `YulangClosure.ComputationPermissionEntryR39.`.
Source declarations quantify arbitrary `{Id : Type} [DecidableEq Id]` and
finite inputs; keys denote full branded identities, not names or unbranded
ordinals. Written definitions read at the pinned revision are:

```text
Valid e a f r :=
  f.owner = a.annotation.owner ∧ f.role = .computation ∧ f.scope = a.scope ∧
  e.recipes[f.recipe]? = some f.parameter ∧
  ownerLookup e.owners a.occurrence = some f.owner ∧
  sourceLambda e f = some (a.occurrence, f.parameter) ∧
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
```

The frozen R39 revision-2 handoff contains actual printed fully qualified types
and complete axiom results: `prepare_exact`, `prepare_of_valid`,
`constructed_entry_publication`, `exact_row_retained`,
`duplicate_or_domain_rejected` and `empty_concrete_local_case` each depend on
`[propext, Quot.sound]`. These are **inherited R39 receipts**, not fresh R122
execution. Its recorded final audit used Lean 4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, exit 0, input SHA-256
`859b12edafd5ef094d5de3fe95ec0ec7cf207f5e95088784a23f2d86c8a97d1f`.
R39's rejected proof goals and post-success Python axiom-parser failure remain
in that immutable handoff; this packet supplies no replacement receipt.

## Source facts and exact application boundary

The frozen R122 source handoff was received, read and rehashed before this
handoff froze. It supplies the complete two-blob writer inventory and lifecycle
analysis; the following application preserves its conditional boundaries.

For the actual invocation of `candidate_formal_entry_annotation(j,...)`, let
the actual registration have recipe position p. Corrected effect:1622–1642
performs no graph mutation before its composite rejecting guard. Passage
therefore establishes in the **invocation PRE-state** both
`!formal_domains.contains_key(&p)` and absence of an entry permission whose
registration is j. The same facts still hold immediately before the permission
literal at 1651: intervening vector preparation does not mutate either store.
This derives absence from negative guards; it does not derive it from POST-state
membership or require every rejected call to have absent keys.

| Existing Lean premise | Actual source evidence / remaining interpretation |
| --- | --- |
| `hf` | Successful lookup `formals.get(j)` of this same registration; requires its precise finite-list/index interpretation. |
| `hr` | The action's outer `annotation.ty.effects.as_ref()` succeeds; r must be this exact row, including positions/order/multiplicity. |
| `hp` | This registration's `entry_effect` is present; initialization ownership is source:2303–2325, not a fabricated port. |
| Owner/role/scope/recipe/sourceLambda fields of `Valid` | Actual guard checks and owner-local HIR Lambda lookup. Full branded owner/formal/occurrence identity must survive the interpretation. |
| `f.recipe ∉ e.occupiedDomains` | Direct guard, provided the actual PRE map's key membership is exactly this Lean list membership. Recipe p is not registration j. |
| `a.registration ∉ e.retainedRegistrations` | Direct guard, provided this list is the PRE vector's actual registration projection, with exact same state and j. |
| Symbolic bound | Actual `row.variables.len() > 1` rejection; list/length interpretation remains necessary. |
| `nonempty` | Actual concrete-vector nonempty branch; no symbolic-only or empty source is removed. |
| Actual publication | Fallible preparation and symbolic constraint work must reach the push; theorem's `true` is local readiness, not whole-call success. |

If those precise interpretations were independently established, form the
conjunction `valid` from these actual guard facts. Then
`(prepare_exact e a f r port).mpr ⟨hf,hr,hp,valid⟩` supplies prepare success;
`constructed_entry_publication e a f r port s hf hr hp valid nonempty`
constructs one shared p with the entire outer concrete row and the same port.
`exact_row_retained` exposes all copied coordinates. This is an application
description of existing declarations, **not a newly checked term or a supplied
concrete e**. No new declaration, law parameter, encoding relation or equivalent
model has been introduced to conceal that premise.

**First missing premise for an actual Lean instantiation:** authenticate the
same invocation PRE-state's `formal_domains` key-membership projection and
`formal_entry_permissions` registration-membership projection into the existing
R39 Inputs, together with the same-batch table/index/row/identity interpretations
listed above. No concrete Rust-to-R39 map or established equations are supplied
by the inspected R39/R114/R121 evidence or this source inspection. Owner: primary
source-to-Lean correspondence intake at the actual batch/HIR and graph-state
owners. An arbitrary finite e with empty lists cannot supply this evidence.

## Global pre-state obstruction, cases and parent application

Universal absence before every reachable dispatched Entry remains a different
open obligation. The source lane identifies exact owners: actual graph/schedule
caller and graph installation/replacement, external writers to public
`formal_domains`, checkpoint/journal application and failed/completed-state
reuse, plus authentic HIR pattern/annotation formation. Their exact external
paths are not established by the allowed two-file domain; locating and leasing
them belongs to the primary. R114 assumed successful initialization/actions
and did not close these callers.

Within the pinned blobs, record/unit/formal-annotation actions insert recipe
domains; Entry alone appends registration permissions. Checkpoint saves a vector
length and starts an undo-key list; rollback removes journaled keys/truncates
the vector, conditional on the correct real journal. It does not prove caller
restoration. A failed final resource sample can occur after push without cursor
advance; retry can see a retained registration and reject. Successful stepping
does not repeat in one frame, but the begin function has no completed-schedule
registry, so external permitted reuse needs its own invariant. None is a proved
source-reachable counterexample.

The candidate ordering falsifier is concrete: `RecordParameter(p)` precedes
Entry and inserts the domain if a Lambda authentically has a record pattern
and an outer row. The leased input does not establish that HIR combination's
source admissibility. Therefore no supported syntax witness/counterexample is
claimed. If presence were authenticated, existing
`duplicate_or_domain_rejected` gives model prepare failure; it does not establish
source reachability. Ordinary scalar Entry-before-Annotation order alone cannot
prove the universal first-entry/no-unsafe-reuse invariant.

Represented: arbitrary finite exact keys, owner-local Lambda/other expressions,
complete ordered outer rows including duplicates, empty/variable-only rows,
local permission construction and generated symbolic-link trace. Empty rows
use `empty_concrete_local_case` without a permission. Nested callback `[Result]`
permissions (R35–R37) have different structural ownership and supply none of
these outer-row premises. Omitted from closure: actual propagation/allocation,
all-caller reachability, HIR admissibility, failed-state restoration, concrete
source/native simulation, arriving provider/Catch/residual and production.

R121's later same-record indexed-read equation remains independently missing;
POST membership cannot establish R39 PRE absence. R114 original App/Lambda
admission transport remains open. Applying this local result to the original
parent yields a reusable guarded constructor seam only. Whole effect hygiene,
original A/B source preservation/shared strategy, soundness, principal coverage,
normal progress, termination, source/native correspondence and production all
remain OPEN. Conditional mathematics and inherited kernel acceptance do not
establish those source premises or grant production authority.

## Actual commands, limits and cessation

Commands used: read-only `pwd`, `cat`, `rg`, `sed`, immutable `git show COMMIT:PATH`
and `sha256sum`; `apply_patch` wrote only this handoff. All substantive reads
and final hashes exited 0. Two source-handoff locator searches before its freeze
returned rg exit 1; later receipt/hash succeeded. Broad output truncation was
followed by focused reads. A clock-tool observation was 2026-10-31 22:08:43 UTC;
exact launch-to-stop wall/CPU/RSS telemetry was not measured.

R122 expressly forbids Lean/Lake/build/checker execution; no executable/version
probe, test, compiler, environment/storage probe, installation, cache, scratch,
temporary/generated file, root-import edit, dirty/quarantined source read, Git
mutation, nested CLI, network or descendant occurred. Fresh printed theorem
types/actual axiom audits/goals/diagnostics/checker exits are **NOT RUN**. The
skill checker requires separately authorized execution ownership and is not run
here. No theorem was authored or labeled newly proved.

Budget ≤300 seconds; lightweight read processes only, no heavy process. No
background process or descendant remains. **All writes STOPPED at revision 1.**
Primary owns independent review, actual runtime accounting, record integration
and Git. Next evidence requests: `R122-PRESTATE-INTERPRETATION-1` at same-state
batch/HIR/graph correspondence owners; `R122-FIRST-ENTRY-LIFECYCLE-1` at actual
graph/schedule/journal callers and authentic HIR pattern formation. Repeating
finite guard lemmas cannot discharge either missing owner.
