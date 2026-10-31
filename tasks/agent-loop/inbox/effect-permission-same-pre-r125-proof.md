# R125 existing R39 same PRE application — revision 1

Status: **FROZEN / WRITES STOPPED / independent review pending**.
Outcome: bounded source-to-existing-mathematics application. The same native
permission vector now supplies both PRE projections. Full symbolic publication,
native simulation and parent soundness remain open. No theorem/model added.

Session `EFFECT-PERMISSION-SAME-PRE/20261102-R125`; worker
`/root/r125_same_pre_proof`, registered lean_prover leaf, sole author and no
descendants. Primary NEW_TASK, source freeze and explicit resume are the actual
activity receipts; requested/effective model and effort UNKNOWN. Exact sole
lease and changed file is this handoff. Initial intake ended WAITING without
writes; source was frozen and authenticated before this revision was authored.

## Inputs, original claim and correction

Baseline `bf83716eea816536f3cc1d68b323d1567712dd38`, branch `yulang3`.
Contract SHA-256
`e064495d96385942c79cfacdec5ce7be6b060db7be4f820c79a1096fcc9862cb`;
manifest SHA-256
`fcb027ef75256c3a0d7f5318af669767334818f7f217d8948f9bfb3b83252efa`.
Frozen source handoff revision 1 SHA-256
`0fc58726d0db552c99714926533080d0238cb913f3d898f1b12430b3057e84a3`.
It was read in full and independently rehashed. Corrected R39 Lean at
`1f5835c276143537ec58ed81db96c7c108cea8e7`, SHA-256
`748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e`,
was read through immutable `git show` and independently authenticated. All eleven
prior-evidence hashes in the manifest were independently recomputed and matched.
The source lane authenticated the eleven immutable source/theory pins; this lane
does not claim a duplicate full Rust audit or read working-tree Rust.

Read root AGENTS/preserved map, goal-driven rules, handoff protocol, exact
contract/manifest/admission, relevant current lease, Lean skill and both
references. The original parent remains
`notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1,3,5:
every supported original source and lawful finite history, actual retained
extrusion pairs, original typing/principal coverage/scopes, full Call/effect
evidence and one shared lawful strategy. The immutable Value birth-level
induced-SCC correction is
`notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6. The authoritative
effect policy `2026-10-10-annotation-effect-hygiene-integration.md` §§1–1.2
distinguishes permission, constraint-derived inflow and actual subtraction;
unknown symbolic dependencies remain. Research drafts provide no additional
semantic authority. No accepted feature or quantifier is removed.

## Exact unchanged mathematical surface

All names have prefix `YulangClosure.ComputationPermissionEntryR39.` and
quantify arbitrary `{Id : Type} [DecidableEq Id]` with finite tables/rows.
Actual immutable declarations have these types:

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
```

R39 State permissions, generated-constraint trace `links`, and externally
supplied contribution `inflow` have different meanings. Inputs and State are
independent structures in Lean; their consistency must come from the actual
source witness. No R39 theorem provides that consistency automatically.

## Concrete shared witness and application at t0

Use the source handoff's single actual session S, immutable batch B and graph G.
Its tagged carrier preserves native root/parameter/occurrence/key/scope/effect
identities, symbolic names, and graph-relative effect-row coordinates. Distinct
alternatives stay distinct; `row_G(U)` never denotes U in another graph. This
is a written interpretation of existing arbitrary Id, not a newly declared Lean
type or an identity-injectivity theorem. Native SourceNodeKey/ModuleId equality
implementations are not independently authenticated by this lane; no semantic
collision or all-world uniqueness conclusion follows.

Let R be the actual action registration, K its registration's recipe position,
U its entry effect, and V0 the actual `G.intrusion.effect_algebra` permission Vec
at t0, immediately before the composite guard. Let P project each retained
permission's complete coordinates and ordered concrete row. Source r is the
actual outer computation annotation row. Native usize coordinates R/K and
owner-local Lambda index remain distinct natural indices. Exact native source
identities remain full tagged values, including the root variant and effect
declaration identity; names or bare ordinals do not replace them.

The source derivation supplies, from that very same Vec:

```text
e.retainedRegistrations = map registration V0
s0.permissions          = map P V0
e.retainedRegistrations = map (fun p => p.registration) s0.permissions
```

The last equation follows by field projection/composition. It does not posit
two independently chosen lists with matching contents. Vec reserve may move a
buffer without changing its ordered sequence or graph owner; payload cloning
creates new storage. Neither allocation address nor pointer-start equality is
an input to R39.

The same source handoff fixes the rest of e from B and G at t0: ordered formals
and recipe Vec projections, a key-complete linearization of the actual owner
map, the resolver-selected authentic owner-local LocalSource, and membership
enumeration of that actual graph's formal_domains keys. Map enumeration order
is irrelevant because keys are unique and these fields use lookup/membership,
whereas Vec order and duplicates are preserved. The owner's LocalSource index
is never replaced by an execution-schedule index.

At candidate_effect.rs 1764–1783 of the pinned baseline, successful row/formal
lookups yield hf/hr, passed owner/role/scope/recipe/owner-local Lambda checks
and the two negative membership guards supply each conjunct of Valid, and the
entry lookup supplies hp with port `row_G(U)`. These are t0 facts. The absence
proof does not use POST-state membership, universal schedule admission, or the
later reader. The bound on symbolic variables is the actual row length bound.

Accordingly `(prepare_exact e a f r port).mpr ⟨hf,hr,hp,valid⟩` applies to
these source-derived t0 interpretations. This removes R122–R124's particular
unfixed same-vector PRE witness at the static source-correspondence level.
It is a mathematical application described against authenticated source
evidence, awaiting independent review; no new checked term or concrete
kernel-verified Rust representation is claimed.

## Permission publication and exact remaining boundary

For nonempty concrete rows, the locally prepared record copies all concrete
members in their original order, including repetitions. Every remaining field
matches `build a f r port`. Thus existing `constructed_entry_publication`
with s0 yields one shared mathematical p and the abstract append conclusion;
`exact_row_retained` exposes all copied coordinates. The abstract theorem
does not prove that an actual Rust transition realizes its State conclusion.

The source gives the exact actual local equation at t1→t2:

```text
map P V2 = map P V1 ++ [build a f r port]
```

Here t1 is after successful optional symbolic preparation immediately before
the push, V1 is that same graph's actual Vec at t1, and t2 is immediately after
the push, before final resource sampling. New physical index is V1.length;
registration remains R. These need not coincide. The permission contains the
entire row; no source-derived operation-specific handling license is inferred.

If the symbolic-name vector is empty, no symbolic helper executes and the
source derives V1 = V0. The actual permission transition therefore realizes
the theorem's `s0.permissions ++ [p]` component directly on that branch.
`symbolicLinks a r port = []` there, but a full retained State.links projection
has not been authenticated merely by observing the absence of helper calls.
An empty concrete row appends no permission, as in
`empty_concrete_local_case`; symbolic-only rows still run symbolic preparation.
No empty/symbolic-only or other supported source case is discarded.

For a singleton symbolic name, helpers allocate/read an annotation variable,
admit occurrence slots 45 then 46, and drain real solver constraints before
t1. Source inspection does not authenticate every delegated context/effect
application owner. Consequently V1 = V0 across successful symbolic draining
remains an exact missing frame premise. Selecting s with permissions from V1
would satisfy an abstract theorem for that arbitrary s, but would not prove
the required invocation-PRE s0 transition; this handoff does not make that
substitution. Valid remains justified at t0, without demanding a new t1
absence theorem.

Likewise the two direct requested constraints are not an authenticated
retained State.links trace. A projection to those direct source requests must
preserve full graph-relative endpoints, occurrence and slots, order and
multiplicity, distinguish additional drain constraints, and establish
`L2 = L0 ++ symbolicLinks a r port`. ConstraintStore provenance and term arena
retention/equality owners are outside the pins. A hypothetical trace projection
or simulation law is not supplied as a new assumption to claim closure.

State.inflow permits unchanged external contribution data I. This is compatible
with the abstract publication theorem; it does not identify I with solver
lower-bound storage, which the actual symbolic helper can mutate. Proving that
the selected I represents actual inflow remains separately owned source/native
correspondence. Permission copying alone does not produce arriving effects or
perform Catch subtraction. Final resource failure can follow the local push;
no whole-call success, rollback, atomic publication or reuse law is inferred.

The first remaining full-publication premises are therefore:

- `R125-SYMBOLIC-FRAME-1`: authenticate successful typed-drain/context/effect
  application owners and derive preservation V1 = V0 for this invocation.
  Falsifier: an authentic successful helper path changes the retained Vec.
- `R125-DIRECT-TRACE-1`: authenticate constraint-store/term owners and derive
  the exact retained direct-request trace equation above, with the same graph
  witness. Falsifier: a retained endpoint, slot, order or multiplicity mismatch.
- `R125-INFLOW-INTERPRETATION-1`: only for a claimed actual inflow/native
  interpretation, identify the concrete contribution owner for external I.
  An arbitrary unchanged list does not establish that bridge.

These return to the primary's source-to-Lean correspondence intake. R121's
same-record indexed consumer read is the next separate consumer edge; physical
permission index, action registration and recipe index stay distinct. R124's
interpolation-key and all-world uniqueness/progress edges, original A/B/shared
strategy, soundness, principal coverage, actual inflow/subtraction, termination,
R111 verification-resource gate and production NO_SAFE_CODE_SLICE remain open.
No source-qualified representation counterexample has been established.

## Verification and cessation

No Lean source/declaration or proof term was authored. Lean/Lake execution,
versions, goals, diagnostics, printed types, axiom audits and skill checker are
**NOT RUN**, as the fixed packet explicitly forbids them. Inspected repository
pin is Lean 4.35.0 with no external packages; no tool was invoked to check it.
Inherited R39 revision-2 receipts report complete axiom list
`[propext, Quot.sound]` for prepare_exact, prepare_of_valid,
constructed_entry_publication, exact_row_retained, duplicate_or_domain_rejected
and empty_concrete_local_case. Those are historical receipts, not R125 kernel
or axiom checks. The declarations above are read source types, not fresh prints.

Existing R39 represents finite tables/full identities, authentic owner-local
Lambda versus other constructors, definition-backed empty execution schedules,
whole ordered concrete rows including duplicates, zero/one symbolic variable,
empty permissions and local symbolic links. It omits allocation, actual solver
propagation, provider arrival, Catch/subtraction and whole-language simulation.

Actual work used bounded cat/rg/sed, immutable git show, read-only Python/hashlib
authentication, sha256sum, and one apply_patch for this sole file. Hash commands
exited 0. A README search for R39 names returned no matches; no checker failure
or execution success is inferred. Some broad intake output was truncated and
was followed by focused original claim/correction and actual Lean-body reads.
Waits consumed no writes; source freeze arrived before final application and
the primary explicitly resumed this same lease. No expanded budget is claimed.
CPU/RSS were not measured. No scratch/generated output, source edit, cache,
build, test, checker, install, environment/storage probe, network, descendant,
nested CLI or Git mutation occurred.

**All writes STOPPED at revision 1.** No background process or descendant
remains. Sole artifact is this handoff; independent review and integration
belong to the primary.
