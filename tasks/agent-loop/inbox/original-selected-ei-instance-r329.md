# R329 core — partial endpoint construction, frozen stopping handoff

Assignment `R329-SELECTED-EI-CORE`, revision **1**. Author/runtime identity
`/root/r329_core`; baseline supplied by primary `71c309678`. Requested
model/effort were not included in the received packet; observed model/effort
**UNKNOWN**. No descendants. Primary supplied the even/odd namespace proposal;
the author constructed and checked the declarations. Independent review is
pending. Primary directed freeze and STOP after the limited result.

Contract `tasks/agent-loop/sprints/source-evidence-transport-r329.md`, SHA-256
`168778197ce8fa4fc06b6f8d4cb44f43335b748e38ffee1b45ba0b3d9a6cfe8f`.
Exact writes: `notes/theory/lean/YulangClosure/OriginalSelectedEIInstanceR329.lean`,
this handoff, and `/tmp/yulang-r329-core`. No other path was written.

**The assigned selected EI interpretation/source-child outcome was NOT achieved.**
Outcome class: checked auxiliary endpoint mathematics plus source/dependency
evidence. It is not EI-Intro, a source-qualified counterexample, an original
semantic impossibility theorem, R306 registration, R159 closure, or production
authority. The module name identifies the assigned target, not an achieved
instance. No source parent premise was discharged by the endpoint arithmetic.

## Parent, attempted construction, and actual delta

The unchanged parent is the selected original R315 computed Call `(make 1) value`,
its complete EI-All source interpretation and source-owned child into R306/R293,
followed by the independent original R159 shared ViewLogic admission/checking.
All original independent arms, response/current-world domains, witness/provider
lineages, results and futures remain required. Original intrusion A/B and the
birth-level qualification correction are unchanged.

Read EI §§2–6, source IF §§2–4, R315 source and authenticated native payload,
R310 typed operands, original Inputs/Positive/Meaning and GuardRegistry,
R311's actual incomplete clauses, R321's operation-declaration interpretation,
R293/R306 consumer signatures, and R328 preservation. Lean skill, execution/
source references, proof-portfolio, sprint rules/README and root instructions
were applied. The attempted semantic route was to derive phase clauses from
independent C_f/F/A_e/IF contracts, preserving typed responses, complete ordered
suffix and whole-tuple actions. This route did not produce the complete clauses.

A concrete representation seam was established: `R328.upDecoded` maps **every**
original Endpoint to `.inl`. Therefore no endpoint in that unchanged readout can
name `R328.Selected.sourceInterface`, an `.inr` handle. This is independent of
the future Generated interpretation; it cannot be fixed by choosing a different
numeric endpoint while preserving every old coordinate unchanged.

The module constructs `oldAddress(e) = (2*e.site,e.port)` and
`generatedAddress(e) = (2*e.site+1,e.port)`, proves injectivity, disjointness and
exact left inverses, and constructs a sum-valued interface readout at those
addresses. At the ACTUAL selected request the new source/result coordinates are
`(3,callableImage)` and `(3,synthesis)`, while embedded original check/result
coordinates are `(2,callableImage)` and `(2,synthesis)`; inverse maps recover
the actual original endpoints `(1,callableImage)` and `(1,synthesis)`.
Arbitrary old arm endpoint lists remain disjoint from these new coordinates;
duplicates are allowed, and no original arm list is inferred or defaulted empty.

This readout is **not** a transported `Decoded` environment. The source sites,
contexts, original constraints, registry signatures, logical/runtime updates
and scoped events still require simultaneous renaming. `SourceAssignment.row`,
`CallOwner.subject`/`initialGoal`, `Decoded.logical`, `Runtime.endpoints`, and
`OriginalSourceChecking.Signature` reconstruct or store endpoints. An
interfaces-only update would break these consumers. None was passed to R293.
No assumed catalogue equality or licensed child was inserted.

## Exact remaining work and ownership

1. **Source-interpretation owner:** construct the selected complete phase
   interpretation from the genuine independently typed primitive contracts.
   The earliest original-instance input not supplied by the frozen R315/R321
   evidence is the operation Request/typed-response/live-world interpretation
   into original `s.Observation` and `s.Continuation`, with its complete
   pending suffix and lawful whole-tuple restriction actions. R321 maps the
   tick annotation into `TypedCall` and still assumes a formal prefix; it does
   not supply this original instance. `GuardRegistry.original/declaration/law`
   and the closed dynamic Signature leaves in R311 are separate inputs.
   Genuine independent contracts may be parameters of a future construction;
   final EI membership or a completed Positive callback may not replace them.
   **No missing semantic authority or impossibility of constructing those
   contracts is proved here.** The selected EI source already specifies the
   intended laws. This worker did not complete their formal construction.
2. **Source namespace owner:** finish the simultaneous source/constraint/
   registry/environment transport before treating the fresh addresses as
   source-owned endpoints. The arithmetic allocation alone is insufficient.
   Preserve original meanings through R328, then prove the actual source
   constructor/readout equations. Alternatively, a finite occupied-domain
   route needs an authentic complete inventory, including independent arms;
   the current R297 source syntax inventory does not provide that inventory.
3. **Source contribution owner:** derive the full source packet
   `Evidence (Meaning inputs) (clause inputs (.trace (raw.atInterface
   (state.interfaces source))))` at R293, plus the genuine original
   `DeclContribution` child and catalogue correspondence consumed by R306.
   This remains the same missing consumer premise; it was not discharged.
4. **R159 owners:** retain independent target Checking, admission, all local
   premises, annotations, both original children and one shared extension.

Mutual TODO `R329-SOURCE-INSTANCE-1`: primary/source-semantics to own the complete
original phase/response instance and address transport jointly. Inputs: selected
EI/IF laws, original complete primitive contracts and scoped arm family, fixed
old Inputs. Output: derived Generated guards/form/fields plus authentic source
registration/child. Falsifiers: same-address `.inl` preservation versus `.inr`
registration; unchanged source Site consumers after endpoint-only renaming;
foreign response or result provider; omitted arm; returned/future phase lacking
its earlier receiver trace. This TODO requests evidence, not a new lease.

Reused: R328 old-meaning preservation and source request; R315 actual source;
R293/R306 exact consumer signatures. Rejected: R311 phaseBody as completed EI,
native trace identity as original membership, R321 TypedCall response as an
Original Inputs instance, empty arms, foreign endpoint rewriting, and an
interfaces-only Decoded wrapper. R326's missing-instance finding remains
applicable; this packet does not relabel it as a newly closed source edge.

## Checked declarations and complete audits

All names below have prefix `YulangClosure.OriginalSelectedEIInstanceR329`.
`s : Sorts`, `G View : Type`, and endpoint variables have original `Endpoint`.
Full kernel-printed types (including all implicit binders) and full axiom lists
are frozen in `/tmp/yulang-r329-core/audit.log`; ordered names are in
`theorems.json`, machine-readable complete lists in `axioms.json`.

```lean
original_old (e : Endpoint) : originalAddress (oldAddress e) = e
original_generated (e : Endpoint) : originalAddress (generatedAddress e) = e
old_injective : Function.Injective oldAddress
generated_injective : Function.Injective generatedAddress
address_disjoint (a b : Endpoint) : oldAddress a ≠ generatedAddress b
old_readout (old : Endpoint → s.Interface) (generated : Endpoint → G) (e : Endpoint) :
  interfaceReadout old generated (oldAddress e) = Sum.inl (old e)
generated_readout (old : Endpoint → s.Interface) (generated : Endpoint → G) (e : Endpoint) :
  interfaceReadout old generated (generatedAddress e) = Sum.inr (generated e)
unchanged_readout_excludes_generated
  (old : Endpoint → s.Interface) (next : Endpoint → (extended s G).Interface)
  (preserved : ∀ e, next e = Sum.inl (old e)) (e : Endpoint) (code : G) :
  next e ≠ Sum.inr code
up_decoded_excludes_generated (state : Decoded s View) (e : Endpoint) (code : G) :
  (upDecoded state).interfaces e ≠ Sum.inr code
Selected.actual_addresses (origin : Declaration) :
  Selected.sourceAddress origin = ⟨3, .callableImage⟩ ∧
  Selected.resultAddress origin = ⟨3, .synthesis⟩ ∧
  oldAddress (R328.Selected.request origin).originalCheck = ⟨2, .callableImage⟩ ∧
  oldAddress (R328.Selected.request origin).originalResult = ⟨2, .synthesis⟩
Selected.original_result_check_recovered (origin : Declaration) :
  originalAddress (Selected.sourceAddress origin) = (R328.Selected.request origin).originalCheck ∧
  originalAddress (Selected.resultAddress origin) = (R328.Selected.request origin).originalResult
Selected.all_original_arms_disjoint (origin : Declaration) (arms : List Endpoint) :
  ∀ arm ∈ arms, oldAddress arm ≠ Selected.sourceAddress origin ∧
    oldAddress arm ≠ Selected.resultAddress origin
Selected.actual_source_not_in_old_decoded (state : Decoded s View)
  (origin : Declaration) (e : Endpoint) :
  (upDecoded state).interfaces e ≠ R328.Selected.sourceInterface s origin
```

Here `R328` abbreviates the full `OriginalInterfacePreservationR328` namespace
only in this display. Axioms, exhaustive partition of the 13 theorems:

- `[]`: `unchanged_readout_excludes_generated`, `up_decoded_excludes_generated`.
- `[propext]`: `original_old`, `old_injective`, `old_readout`.
- `[propext, Quot.sound]`: `original_generated`, `generated_injective`,
  `address_disjoint`, `generated_readout`.
- `[propext, Classical.choice, Quot.sound]`: all four `Selected` theorems.

No sorryAx, project axiom or unchecked native-evaluation assumption. The
selected request transitively carries the standard axioms printed above.

## Execution, hashes, and cessation

Pin/config/manifest read: Lean 4.35.0, no external packages, unchanged
`-j1 -M1024`. Read-only `elan which lake` resolved
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`.
Actual Lake `5.0.0-src+eb6cafb`; Lean `4.35.0`, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Linux x86_64 Release.

Isolated project copied from the frozen R328 project; all 53 transitive source
files in this module's import closure were byte-compared against current
repository files and matched. Imported oleans were reused from that frozen
checked project; dependencies were not rebuilt in this packet. Direct checks:

```text
lake env lean -j1 -M1024 -o .lake/build/lib/lean/YulangClosure/OriginalSelectedEIInstanceR329.olean YulangClosure/OriginalSelectedEIInstanceR329.lean
  check-1.log exit 1: Nat alias normalization/constructor noConfusion diagnostics
  check-2.log exit 1: remaining reflexivity goal
  check-3.log exit 0: no warnings
lake env lean -j1 -M1024 --root=/tmp/yulang-r329-core /tmp/yulang-r329-core/YulangProofAudit.lean
  exit 0, all 13 theorem-kind/type/complete-axiom audits
bundled check_lean.py audit_source + validate_audit
  exit 0, all complete ordered audits accepted
```

No full helper CLI build, default-root integration, compiler/native execution,
or source semantic correspondence is claimed. Prior diagnostics are retained
in scratch. No live checker remains; the heavy slot was explicitly released
to primary before handoff. One process at a time, local -M1024; exact CPU and
peak RSS were not measured. Work stopped on primary direction, before the
packet wall bound; no assertion that the entire resource budget was consumed.

Frozen hashes:

```text
61200ca1d6349fcd2707ebf186eca3270b22d15c98a9b47004ba72b9f7bb3fa7  OriginalSelectedEIInstanceR329.lean
8813ca10cd4a4a05e6c0c354b249ac61f6316e9edac23c533f8d5832d0a69a30  /tmp/yulang-r329-core/audit.log
c5d75a4d96b0f43e16560318cba1e3ef643bbd2a6c1aaec9880546b22ba642b7  /tmp/yulang-r329-core/dependencies.json
688761f68969c1a8ed27fb5f8415939a4cd8edea6f27e31188c1c97878e02379  /tmp/yulang-r329-core/theorems.json
77f826d5ae965cd41b7b841b9915d7a2ac9811ef68a3756036c3831342ef4e4a  isolated OriginalSelectedEIInstanceR329.olean
```

Authority/source hashes are in `/tmp/yulang-r329-core/frozen-hashes.json`;
all 53 dependency hashes and paths in `dependencies.json`. Scratch consists
only of the isolated project/cache, three check logs, Debug.lean/debug.log,
YulangProofAudit.lean/audit.log, theorems.json, dependencies.json, axioms.json
and frozen-hashes.json under the leased scratch root.

**STOPPED. Source and scratch frozen; all writes stop after this handoff.
No Git, children, compiler/tests/expectations, central state, theory index,
questions, dependencies/configuration or other-worker paths were changed.
Pending independent review and primary adjudication; selected EI/R159 OPEN.**
