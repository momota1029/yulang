# R123 existing R39 lifecycle application — revision 1

Status: **FROZEN / WRITES STOPPED / independent review pending**.
Outcome class: conditional application of existing mathematics to authenticated
bounded source evidence. No new Lean declaration, concrete Rust interpretation,
universal reachability theorem or source-qualified counterexample is delivered.

Session `EFFECT-PERMISSION-ENTRY-LIFECYCLE/20261102-R123`; assignment and sole
author `/root/r123_entry_lifecycle_proof`, registered lean_prover leaf, no
descendants. Actual primary NEW_TASK and this turn establish activity;
requested/observed model and effort UNKNOWN. Sole leased/changed path is this
handoff. Primary owns review, status, integration and Git.

## Authority, original claim and authenticated dependencies

Contract SHA-256 `d715f6f26267c7ab14f2451ede516ddba8184b91f899ebf5005f9b5477104623`;
manifest r1 `47adc3f89a2426f46cffdecfed8fa74bfdb0fac42f4deb4722fc94d70f6578aa`.
Baseline `852ab889cee2f4cfe04da3a1e8c9dd96f9758845`, branch yulang3.
Read root AGENTS.md/preserved map, goal-driven rules, assignment protocol,
design authority, yulang-lean-proofs and sources/execution references, exact
contract, manifest, admission, relevant current state, original parent and
correction. No draft supplies semantic authority.

Original parent: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`
§§1,3,5: every supported original source, lawful finite construction history and
actual retained extrusion pair; preserve original typing/principal coverage,
full Call/effect evidence, scopes and one joint lawful strategy. Apply the
immutable Value birth-level induced-SCC correction in
`notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6. Immediate effect
authority is `2026-10-10-annotation-effect-hygiene-integration.md` §§1–1.2:
annotation permission, constraint-derived inflow and actual subtraction remain
distinct; unknown symbolic dependencies remain. The top-level inference
principles §§4–5 permit safe disposal of a failed private attempt and do not
impose restoration/retry as a universal goal.

| Frozen dependency | SHA-256 |
| --- | --- |
| R122 source r1 | `a9191683817369d96c94c74ffe737825ab83e7ee5a5ca3ee2eb491574ff20612` |
| R122 proof r1 | `abd69016f9177a09b7a56cc6c3499aef661cca5db5a08ea0e9cc24cdab294489` |
| R122 outcome | `07b1b56567f03a965d5efbf2cf503bb0835451685e6e2a55c3b4e061724fbe11` |
| R123 source r1 | `c2fe62592f85a8f6bbf3e5b1eecb29fdef26cb031a2894c0a417db1ab64c679a` |
| R39 Lean blob at `1f5835c276143537ec58ed81db96c7c108cea8e7` | `748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e` |

All listed hashes were independently checked. R123 source handoff was received
as FROZEN, read completely and rehashed before this file was written. Its seven
Rust blob hashes are manifest-pinned; that lane authenticated them. I did not
read working-tree Rust or expand the proof lane into source ownership. The
source lane reports the whole constructor section byte-identical to corrected
R39, section hash `8b24470a66f20bbd71ba9bf8a3e18f45c87dd227439f8146e8dbb98c6a935c77`;
its newer full effect blob must not be confused with the R122 full-file hash.

## Exact existing declaration application

All names here have prefix `YulangClosure.ComputationPermissionEntryR39.`.
Read the actual pinned bodies, not merely their historical success receipts.
They quantify arbitrary `{Id : Type} [DecidableEq Id]`, finite tables and full
branded identities. The unchanged relevant signatures are:

```text
prepare_exact (e) (a) (f) (r) (port) :
  prepare e a = some (f,r,port) ↔
  e.formals[a.registration]? = some f ∧ a.annotation.row = some r ∧
  f.entry = some port ∧ Valid e a f r

Valid e a f r :=
  f.owner = a.annotation.owner ∧ f.role = .computation ∧ f.scope = a.scope ∧
  e.recipes[f.recipe]? = some f.parameter ∧
  ownerLookup e.owners a.occurrence = some f.owner ∧
  sourceLambda e f = some (a.occurrence,f.parameter) ∧
  f.recipe ∉ e.occupiedDomains ∧
  a.registration ∉ e.retainedRegistrations ∧ r.variables.length ≤ 1

constructed_entry_publication (e) (a) (f) (r) (port) (s)
  (hf : e.formals[a.registration]? = some f)
  (hr : a.annotation.row = some r) (hp : f.entry = some port)
  (valid : Valid e a f r) (nonempty : r.concrete ≠ []) :
  ∃ p, prepare e a = some (f,r,port) ∧ permissionFor a f r port = some p ∧
    p.concrete = r.concrete ∧ p.entry = port ∧
    publish a f r port true s = some
      ⟨s.permissions ++ [p], s.links ++ symbolicLinks a r port, s.inflow⟩
```

For one actual publication-reaching invocation with registration j and recipe
p, the guard supplies both absences in that invocation's PRE state. With the
same-state interpretations and remaining guard equations, assemble `valid`;
`(prepare_exact e a f r port).mpr ⟨hf,hr,hp,valid⟩` yields prepare success.
`constructed_entry_publication` then supplies one shared permission witness,
including the whole ordered concrete row and the same entry port.
`exact_row_retained` exposes registration, recipe, formal identity, occurrence,
owner, scope, annotation position, row position, port and entire concrete row.
This is a written application of existing declarations, not a newly checked
Lean term or an established concrete e/s.

If an actual dispatch instead finds occupancy, `duplicate_or_domain_rejected`
applies after the same PRE projection and formal lookup. It gives model prepare
failure; it does not supply a reachable-source counterexample. Empty or
symbolic-only rows use `empty_concrete_local_case` without constructing a
permission. Unknown variables are retained in the existing symbolic-link trace.

## What the lifecycle evidence establishes

The frozen source lane exhausts non-test LocalSource Lambda formation branches:
record-pattern parameters have no annotation; annotation-bearing parameters
are identifier parameters with no record pattern. Member/inline paths preserve
that exclusion. Thus the hypothetical same-formal RecordParameter-before-Entry
falsifier from R122 is excluded in these authentic HIR construction routes.
This establishes a source formation fact without restricting the parent domain.

For a supplied schedule, Entry precedes its FormalAnnotation; fresh recipes and
registrations use distinct append indices; frame stepping preserves vector
order and increments only after success. A fresh graph's two stores are empty.
The selected shadow_apply entrypoint owns its session locally, returns an error
on execution failure and does not return a mutable graph/session for reuse.
This supplies actual caller ownership evidence beyond run_candidate's mere
consuming signature.

It does not establish a universal once-per-formal theorem. SCC partition/no
duplicate definition execution depends on unpinned `shadow_scc.rs`; exhaustive
no-shared-Lambda visit uniqueness has not been derived across all expression
builders. End-to-end route rollback delegates to unpinned
`candidate_intrusion.rs`. Other callers and direct internal reuse remain
outside the authenticated conclusion. These are explicit source-owner gaps,
not assumed invariants or demonstrated reachable counterexamples.

The final resource sample can fail after permission append. R39 `publish true`
models that local publication point, not the complete call returning Ok.
`failed_publication_unavailable` concerns model readiness false; it cannot be
used to infer an empty Rust permission vector after Err. The shadow caller's
private-session disposal supports its own error path; no global restoration
law follows and none is required solely to prove local guarded soundness.

## Necessary universal premise and first remaining owner

Successful-entry soundness needs a universal statement over actual supported
source executions: **for each invocation reaching this publication point**, its
actual PRE collections, authenticated batch/HIR and exact action admit the
same R39 interpretation, and its passed guard supplies `Valid`. It does not
need the stronger claim that both absences hold before every dispatched Entry,
including rejected calls. That stronger admission/progress claim remains
relevant if showing that ordinary supported inference never rejects due to
duplicate scheduling or incompatible earlier publication. Neither claim is
silently substituted for the other.

The first direct missing premise is still the concrete same-PRE Rust-to-R39
interpretation. In particular:

- `e.occupiedDomains` membership must equal key membership in this graph's
  actual `formal_domains`, at recipe p.
- `e.retainedRegistrations` membership must equal the registration projection
  of this same graph's retained permission vector, at j. R39 Inputs and
  publication State are independent structures; their consistency is not
  supplied merely by constructing two finite lists.
- The same actual vector must interpret `s.permissions` with all coordinates,
  row order/multiplicity and complete effect/type-argument identities preserved.
  Formal/recipe vector lookups, owner lookup, authentic owner-local expression
  index, annotation row, entry effect and symbolic endpoint identities must
  commute with that same interpretation. Registration, recipe, vector index,
  packed slot and owner are distinct coordinates.

Owner: primary's source-to-Lean correspondence intake at actual batch/HIR and
graph-state owners. Next request `R123-SAME-PRE-INTERPRETATION-1` requires these
concrete equations on the authenticated constructor input; falsifier is an
actual owner/index/state mismatch. Independently,
`R123-GLOBAL-ENTRY-LIFECYCLE-1` needs the exact SCC partition, expression-builder
uniqueness and any actually required undo owners; no new conditional transition
model is proposed. The primary must determine which global fact is required by
the selected acceptance/progress contract before enlarging that proof task.

R121's same-record indexed-read equation remains distinct. Callback nested
`[Result]` rows from R35–R37 do not become the computation outer row. Provider
arrival, Catch/residual semantics, propagation/allocation, concrete native
simulation, original A/B preservation/shared strategy, soundness, principal
coverage, normal progress, termination and production remain OPEN. R111 resource
gate and NO_SAFE_CODE_SLICE are unchanged.

## Verification, represented cases and cessation

No theorem was authored. Fresh Lean/Lake execution, actual goals/diagnostics,
printed types, axiom audits and skill checker are **NOT RUN**, as explicitly
required by this packet. R122 records inherited R39 revision-2 receipts:
`prepare_exact`, `prepare_of_valid`, `constructed_entry_publication`,
`exact_row_retained`, `duplicate_or_domain_rejected`,
`empty_concrete_local_case` each have complete axiom list
`[propext, Quot.sound]`. These are historical receipts, not R123 execution;
no fresh toolchain/version/exit or kernel acceptance is claimed.

Represented by existing R39: arbitrary finite exact keys, owner-local Lambda
and other expressions, definition-backed empty execution schedules, complete
ordered concrete rows including duplicates, zero/one symbolic variable,
empty/symbolic-only permission cases and local generated symbolic links.
No whole-language instance, multiple-variable acceptance proof, all-caller
lifecycle, native solver propagation, failed-state restoration, actual
subtraction or consumer read proof is supplied.

Actual commands: bounded `cat`, `rg`, `sed`, immutable `git show`, `sha256sum`,
one read-only Python extraction of current-state lease/sprint fields and clock
observations; one apply_patch wrote this handoff. Relevant hashes exited 0.
Some batched output was truncated, followed by focused reads of the original
parent and policy. No scratch/generated file, source/Lean edit, cache, build,
test, checker, environment/storage probe, install, network, nested CLI,
descendant or Git mutation occurred. Lightweight synchronous processes only;
CPU/RSS were not measured. Cap 300 seconds; no extra budget claimed.

**All writes STOPPED at revision 1.** Frozen source was consumed before writing.
No background process or descendant remains. Independent review/integration
pending with the primary.
