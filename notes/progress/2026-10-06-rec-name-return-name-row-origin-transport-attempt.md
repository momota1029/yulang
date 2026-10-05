# Recursive Name return: Name-to-occurrence origin transport attempt

Date: 2026-10-06
Status: frozen unreviewed research-only partial construction; no gate closure
Method/gate: constructive correspondence at the Name-interface/live-row seam
Baseline: `c0f328adfc67566c90ee25becd99a2552c8941c0`
Lease: this file only; no implementation authority

## Objective and result

For one unused alias `my h = f` after
`my f x = g; my g y = f`, construct transport from the selected source Name
interface to the actual occurrence row `c_h`, preserving occurrence identity
and dependencies. The method constructs the production occurrence map first,
then attempts to attach source origins to that map. It does not repeat the
generic O-classification argument or vary an origin graph completion.

The production map is constructible from current owners. The selected source
Name step preserves a supplied interface and adds no source binder in that
step. The missing link is a provenance-complete realization of that interface
at the distinct live row. Neither a directed constraint nor allocation
provenance supplies that realization. In particular, absence of a new binder
in Name synthesis does not classify a row representing a pre-existing binder,
or erase dependencies on such a binder. No unconditional §22 classification
of `c_h` follows here.

## Baseline and governing inputs

Authority is fixed by the assignment and these exact sections:

- `notes/design/2026-10-02-source-result-synthesis-choice.md` §4:
  `Gamma(x)=I` implies `Synth(name x)=I`, preserving source positions.
  Its inert lookup/transport interpretation is fixed by the assignment and §1.
- `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` §20:
  request opening and witness/binder correspondence are essential; aliases
  retain dependent fields and the same witness. Solvable inference
  existentials differ from hidden request binders.
- Charter §22: an introduced existential is subject to the selected guard
  on every generated/derived comparison. The introduction predicate is a
  premise of that rule, not a conclusion of allocation.
- Charter §23: levels belong to variables; exact variable/extrusion coverage
  and preservation remain open.
- Committed `notes/progress/2026-10-06-rec-name-return-origin-rule-inventory.md`:
  the limited Name-step derivation and the historical/successor boundary.

The committed source-guard derivation note supplies the finite bare-alias
envelope; the committed purefun production reduction supplies its audited
member scheme. Those are research evidence, not extra source authority.
Current HIR/solver/types source was inspected directly. The read-only
`r_origin_production_map` agent report has no dependency file; no contents of
a nonexistent note were assumed. `tasks/current.md`, `tasks/research-lab.md`
and `notes/design/INDEX.md` were used as locators, not semantic premises.
No pending question bundle was consumed.

The eight direct files below matched the pinned baseline at final dependency
inspection. Paths are relative to the repository root.

| Dependency | SHA-256 |
|---|---|
| `notes/design/2026-10-02-source-result-synthesis-choice.md` | `71326de0897159343797d6aec083860ee0f57a1bc04f9c4ae77e579ea0ba5992` |
| `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| `notes/progress/2026-10-06-rec-name-return-origin-rule-inventory.md` | `2f5ac6958addac1b108511493526426702b3b3ec210e90f6bd03221b77260282` |
| `notes/progress/2026-10-06-rec-name-return-source-guard-derivation-attempt.md` | `20b5f791958db4f8a1f9e06863db6e5e95e72bd4f03d9c8f5c4d4f094516becd` |
| `notes/progress/2026-10-06-rec-name-return-purefun-production-reduction.md` | `f4ee1f71bea24c1150c90a274b41bc8fb9f8c2059c797c500a245fd4003f9779` |
| `crates/yu-hir/src/module.rs` | `ed92636de471b4d424a274f3509673c68761d9fa24fa06f07c9afc3bb3b9b7a5` |
| `crates/yu-solver/src/lib.rs` | `a2103c6735d7a4efad00231f973544dda59d42219dbf83439fffc17889168e59` |
| `crates/yu-types/src/lib.rs` | `a3a920847b53e745ef17d43cf920c98a425e0d20c46b68524bd9c1d0b1a3fba5` |

## Production occurrence map and direction audit

Let `u_h` be the HIR occurrence of `f` in `h`'s body. Distinguish:

```text
c_h : live value row for that occurrence
R_h : live value row for h's definition root
r_f : live value row for f's definition root
rho_h : fresh row substituted for the target scheme's recursive binder r0
L_h = P0(Top-, P0(Top-, rho_h+))
```

The following partial correspondence is an implementation fact, under valid
owned artifacts, successful allocation/route completion, normal parsing and
resolution, and exactly this finite envelope:

```text
u_h
  -> ComponentId::Occurrence { occurrence: u_h, kind: Value }
  -> occurrence_component_positions[u_h].value
  -> live_components[that position].ordinal = c_h
```

`yu-hir/src/module.rs:1155` preserves the bare binding body's occurrence;
`:1402` resolves its identifier to f's definition. Solver collection
`:1008` dispatches the resolved Name to `emit_resolved_binding_name` (`:1513`).
That owner makes the occurrence component separately from the definition-root
component and emits `c_h <: R_h`. `DefinitionUse` construction (`:1111–1135`)
retains the same occurrence, its exact value-component position, the parent h,
target f and target-root component. Startup (`:9475` onward) assigns dense
live ordinals without replacing that occurrence. Thus the map retains an
actual occurrence identity; it is not an identification with either root.

The assignment's proposed `c_h <: r_f` is **not a collected constraint** if
`r_f` denotes f's definition root, as it does in the earlier source-guard
note's candidate mutual-group equations. For an internal same-SCC use,
`route_internal_inner` (`:13991`) directs `r_f <: c_h`. This alias is an
external use of f's already finalized component, so the actual route is
`L_h <: c_h`, using the instantiated positive predicate. Its collected
body-to-own-root constraint remains `c_h <: R_h`. Neither route gives the
reverse `c_h <: r_f`, and no endpoint equality is inferred from a subtype edge.

The prior source-guard note's attribution is consistent with these owners:
its `cu_i` is `c_h`, `R_hi` is `R_h`, and `rho_i` is `rho_h`. The incoming
call's three root tasks are

```text
L_h <: rho_h       rho_h <: Top-       L_h <: c_h
```

They are the recursive lower restoration, recursive upper restoration and
target-member predicate route in `instantiate_and_route_closed_inner`
(`:14527–14675`). `route_incoming_inner` (`:14877`) selects f's scheme and
the existing occurrence value component. It allocates `rho_h`, not another
consuming occurrence. The fourth shape `L_h <: R_h` comes from replay against
the existing `c_h <: R_h` direct upper neighbor (`apply_value_task`,
`:12165–12234`). It is not an additional Name-to-target-root comparison.

Before incoming routing, the alias has no other value neighbor, exact bound
or consumer. Hence the prior four-shape attribution needs no repair. This is
a static owner-path check; no new execution confirms an entire trace.
The exact member scheme remains the committed reduction's audited premise;
the existing fixture at solver `:20476` was read, not rerun. Other callers or
later alias generalization are outside this observation boundary.

Types `ClosedValueScheme` (`yu-types/src/lib.rs:631`), `ClosedRecursiveBound`
(`:73`) and their views retain Q/R ordinal structure, bounds and predicate.
The inspected structures provide no §22 source-introduction correspondence.
Solver `LiveVariableOrigin` (`:749`) describes allocation eligibility, and
`fresh_value_at_level` (`:9550`) appends a distinct row. These are exact
implementation facts; neither `Collected`, `Fresh`, the stored level, nor
absence of requests is used as a §22 classification rule.

## Constructive source step and its exact limit

Fix a source derivation `d_name` with the already supplied interface
`Gamma(f)=I_h`. Preserve I_h's source positions, binder identities and all
existing profile/scope/dependency correspondence; do not equate it with an
erased Function shape. Assume this derivation step is exactly selected §4
Name synthesis, without attaching a separate opening or use judgment to it.

Then:

```text
Gamma(f) = I_h
----------------------  selected Name rule
Synth(name f) = I_h
```

The conclusion copies the premise interface. The rule contains no fresh
binder, witness-selection or package-opening premise/conclusion. Therefore
the **new source introductions contributed by d_name** are empty. Existing
binders and dependencies in I_h are preserved. This is a limited derivation
from the selected rule; it establishes neither that I_h contains no
existential origin nor that the separate row c_h has no such origin.

Supplying I_h is a preceding obligation. Production performs closed-scheme
generalization/instantiation, allocates rho_h and restores its bounds before
predicate insertion. Selected Name synthesis starts after its Gamma premise
has been supplied. Applying that rule cannot retrospectively classify those
operations or the source meaning of the recursive binder. The committed
inventory expressly leaves the successor generalized-interface/use judgment
open. The same absence also prevents proving that f's scheme is I_h merely
because their erased shapes match.

The constructive result is thus two maps with an unfilled seam:

```text
source:     supplied I_h --Name copy--> synthesized I_h
production: u_h --component position--> c_h --direct upper--> R_h
                                   incoming L_h inserts here
```

Each displayed production map is fixed independently of the source origin
label. There is no source-to-row origin map between these two lines in the
selected rule.

## Smallest missing transport lemma

The missing lemma is **conservative realization of one supplied Name
interface at its occurrence row**. Its hypotheses and conclusion must be
spelled out before it can classify anything:

1. A valid supplied I_h with explicit source binder/origin and dependency
   correspondence, including the derivation that supplies it from the
   recursive binding's generalized interface at this use.
2. A realization map for this exact u_h which identifies what source endpoint
   or binder, if any, c_h represents, and which source introduction event
   realizes that role. It must also relate the scheme's r0/rho_h to the
   supplied interface. Completeness must exclude hidden opening/introduction
   events; syntactic Name allocation alone is not this premise.
3. Administrative occurrence allocation and the directed predicate/root
   constraints preserve those mapped origins and the entire existing joint
   scope/dependency correspondence through replay. The distinct c_h identity,
   `c_h <: R_h`, restored recursive bounds and caller assignment remain.

**Conditional lemma:** with these hypotheses, the selected Name step creates
no additional source introduction. The mapped origin status of c_h is the
one supplied by hypothesis 2, with pre-existing dependencies preserved by
hypothesis 3. If that map certifies c_h as an administrative endpoint rather
than a represented §22-introduced variable, that certification gives the
corresponding negative classification. If it maps c_h to an existing
introduced binder, Name copying preserves that binder; it gives no exemption.

Proof: apply the selected Name rule to hypothesis 1, retaining its source
positions. Compose this copy with hypothesis 2's realization, and retain the
joint ledger and directed comparisons by hypothesis 3. No fresh source
introduction is present in the Name step to add to the mapped history. The
conclusion is conditional precisely because the realization and its
preservation are unproved; stating them is not proving them.

The narrow c_h blocker is hypothesis 2: **which source-origin role is realized
by the occurrence row?** The independent predecessor blocker is hypothesis 1:
**which origin-bearing interface does generalization/use supply to Gamma?**
Hypothesis 3 includes the remaining variable/extrusion preservation work.
Dropping rho_h from the map, collapsing c_h into r_f or R_h, or projecting
away its dependencies would avoid those questions by losing the required
objects. Pure inertness only constrains execution and does not discharge them.

This is a correspondence/theorem task under the current open proof gates.
The existing selections do not force a new user policy choice at this seam.
If a proposed realization instead introduces existential opening at ordinary
lookup/use, chooses blanket guarding or exemption from allocation provenance,
or adds new source restrictions, that is a new semantic premise for the
primary to resolve and, where it changes meaning, obtain approval. No such
premise is selected by this note.

## Evidence, resources, omissions and failure conditions

Read the three required rules in full. Commands: bounded `cat`, `rg`, `sed`,
`git rev-parse HEAD`, narrow `git diff --name-only BASE -- <eight dependencies>`,
`sha256sum <eight dependencies>` and leased-path status inspection. The narrow
dependency diff was empty. HEAD initially matched the pinned baseline; by final
inspection it had advanced concurrently to
`6ccad95908f23832b8c29f1ee0a728a8ff3c6f32`. The eight dependency files still
matched the pinned baseline, so this branch movement did not change the inputs.
Some batched locator output was truncated; used owner spans were subsequently
read narrowly. This is not an exhaustive search of historical source rules.

No code, tests, builds, probes, formatter, Git mutation, children or interactive
questions. No executable oracle, seeds/ranges, mutation campaign, timing
sample or enumeration. The source-rule deduction is independent of a supplied
toy transition checker. The source characterization and prior production
reduction share the same compiler owners and are not independent oracles for
source adequacy. No independently reviewed theorem is established here.

At most three lightweight read commands ran concurrently; heavyweight process
count was zero. CPU/RAM peaks and total wall time were not instrumented; no
numerical budget was supplied. The only output is the exact leased note.
Full source generalization/use realization, recursive origin classification,
§23 guard/extrusion preservation, principality, diagnostics/failure ownership,
applications/annotations, arbitrary caller inventories and later alias
publication remain unverified.

Failure conditions: authority changes the Name/interface or introduction
meaning; dependency files change; alias lowering acquires another typing
operation; a supplied interface loses its original binder correspondence;
or routing changes its consuming row, restored bounds or direct edges.
The conditional lemma cannot validate its own realization assumptions.

Recommended next action: supply a narrowly scoped, provenance-complete
generalized-interface/use realization for this single alias, then independently
check its c_h role and r0/rho_h correspondence against the retained ledger.

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-rec-name-return-name-row-origin-transport-attempt.md`.
- Baseline SHA: `c0f328adfc67566c90ee25becd99a2552c8941c0`.
- Changed dependency hashes: none; direct hashes are recorded above.
- Review status: frozen unreviewed research-only partial construction and
  conditional lemma; no independent certification or implementation authority.
- Checks already run: authority/source-owner inspection, dependency equality
  and SHA-256 capture, baseline and leased-path checks, final artifact scope
  and whitespace inspection. No executable checks.
- Proposed one-line commit message: `research: isolate Name occurrence origin transport premise`.
- Shared-record deltas intentionally left for the primary/curator: distinguish
  the constructed occurrence map from missing semantic origin realization;
  retain generalized-interface/use provenance and variable/extrusion gates;
  record the direction caveat for `c_h <: r_f` in the assignment. The prior
  source-guard note's four-shape attribution needs no factual repair.

Writes stop after final inspection; this artifact is submitted frozen for review.
