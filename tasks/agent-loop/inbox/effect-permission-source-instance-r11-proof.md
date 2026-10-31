# R11 proof handoff — revision 1, constructed and unchecked

## Assignment, authority and frozen inputs

Leaf `/root/effect_permission_source_instance_r11_lean`; 300-second finite proof packet. Exact writes: `notes/theory/lean/YulangClosure/FormalPermissionSourceInstance.lean` and this handoff. No descendants or other writes. Primary owns isolated cache/generated outputs and all Lean execution, audit release, independent review and adjudication.

Read root `AGENTS.md`, `AGENTS.pre-sprint.md`, `rules/goal-driven-sprints.md`, `rules/design-authority.md`, `yulang-lean-proofs/SKILL.md` and its `references/sources.md` and `references/execution.md`, R11 contract/source boundary/manifest, R10 outcome/failure review/proof/source handoffs, R9/R5 definitions, project README/pin/lakefile/manifest, original source-preservation manuscript §1 and governing-source references, the birth-level correction §§2–6, and authoritative top-level inference principles. The original parent remains the universal supported-source preservation/principal-coverage/soundness/progress/termination claim in `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §1, with `notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6. This exact-tree supplier retains the original parent domain and quantifiers; it does not close that parent. Candidate helper semantics remain conditional transcription.

All 127 entries of `tasks/agent-loop/sprints/effect-permission-source-instance-20261029-r11-inputs.json` authenticated against actual bytes before editing: zero mismatches. Contract SHA256 `13866ae5b51fac68500f7b6ac452e3cb0f55ef4789882784d0326fdb26423908`; manifest SHA256 `1534065c8bc96872cfa3dc34120f7e5fc690c8a6023ced3ac0262d67832b8088`; R11 source handoff SHA256 `abe2289150f5c31523a01649b34317a602991ea36b5a8dc730ff370092a0a206`.

R10 revision-3 baseline artifact SHA256 `4a25b24d251494ca6c05fcc696306cedf3d9cfa36d4a90a2a3437b68a04ff977` (14073 bytes). Read-only comparison uses the preserved audit-2 project artifact. R9 dependency `FormalPermissionSourceAllocation.lean` SHA256 `795e63e850f73d75f18f721224d3e0723c187a57c7437ffe3ef08a4dbd80648a`; R5 dependency `FormalPermissionAuthenticatedNativeDecode.lean` SHA256 `ea97baf7c98becef27df9e0c416d8d5fb00e9e1b5b63f37021b01598231936dc`. No dependency changed.

## Exact construction delta

Only the final block of `exact_tree_supplier` changes. The actual already-constructed `rootChildren : SourceTuples ... out` supplies its dependent output to a local lambda. That lambda reassembles a typed `children : TupleDecoded context false s` from exactly `out.elements`, `out.entries`, `out.state`, `out.births` and `out.events`. It receives the existing `rootChildren` proof; it does not assume a new source derivation or choose a second output. Structure eta reduction makes this record definitionally the actual root-child result.

`nonempty : children.elements ≠ []` is proved from the actual two children. A typed `root : ValueDecoded context false s` contains `.tuple children.elements`, unchanged entries/state/births, and `.tuple children.events nonempty`. A typed `rootRun : SourcePair context false R5.tree (R5.code 0 1) s root` then applies `SourcePair.tuple (out := children)` to that same `rootChildren`, unchanged root annotation/guard, `nonempty`, and the existing root helper obligation. Only after these typed objects exist does `exact ⟨root, rootRun⟩` package the existential. The root helper simplification explicitly unfolds the local `children` definition.

All four public theorem statements are byte-identical to the preserved R10 revision-3 statements (read-only Python comparison: four True results). All allocator definitions, four connected `FreshStep` states, arbitrary permission prefix, four `FreshReady` inputs, 13 local helper-frame inputs, inner/root tuple guards, source constructors, polarity and successful-return cut are unchanged. `exact_tree_r9_application` is byte-unchanged and passes the SAME `out`/`run` supplied by `exact_tree_supplier` into R9 `r5_source_allocation_instance`; no independent witness is selected.

Source mapping: `FormalPermissionSourceAllocation.lean` `SourceTuples.cons`/`.nil` assemble the ordered root and inner child output records; `SourcePair.tuple` (lines 200–207 in the pinned dependency) supplies exactly the selected root fields. `FormalPermissionExportWitness.lean` `TupleDecoded` and `ValueDecoded` (lines 125–137) carry dependent event indices. R5 `tree`, `code`, `retained`, and `output` retain the exact root Tuple(Function, Tuple(Int, Function)) and four ordered ports. Rust owners remain `candidate_effect.rs::candidate_formal_value_pair`, `candidate_formal_effect_port` and `lib.rs::fresh_effect_at_level`/reservation/term helpers, as mapped by the frozen R10 source handoff. This repair supplies no additional Rust helper-success or native correspondence evidence.

## Public theorem statements

All four names below are in `YulangClosure.FormalPermissionSourceInstance`. Private suppliers remain transitive dependencies; structures/definitions are construction data, not parent closure.

```lean
theorem push_aligned (a : Allocator) (level : Nat) (h : Aligned a) :
    Aligned (a.push level)
```

```lean
theorem four_allocations_and_prefix (a : Allocator) (level : Nat) (h : Aligned a) :
    Aligned (afterOne a level) ∧ Aligned (afterTwo a level) ∧
    Aligned (afterThree a level) ∧ Aligned (afterFour a level) ∧
    (afterOne a level).bounds.length = a.bounds.length + 1 ∧
    (afterTwo a level).bounds.length = a.bounds.length + 2 ∧
    (afterThree a level).bounds.length = a.bounds.length + 3 ∧
    (afterFour a level).bounds.length = a.bounds.length + 4 ∧
    (afterFour a level).permissions = a.permissions ++ FormalPermissionAuthenticatedNativeDecode.retained a.bounds.length
```

```lean
theorem exact_tree_supplier (s : State) (a : Allocator) (level : Nat)
    (length : a.bounds.length = s.nextEffect) (aligned : Aligned a)
    (ready : Reservations a level) (helpers : TreeFrames s) :
    ∃ out : ValueDecoded FormalPermissionAuthenticatedNativeDecode.context false s,
      SourcePair FormalPermissionAuthenticatedNativeDecode.context false FormalPermissionAuthenticatedNativeDecode.tree (FormalPermissionAuthenticatedNativeDecode.code 0 1) s out
```

```lean
theorem exact_tree_r9_application (s : State) (a : Allocator) (level : Nat)
    (length : a.bounds.length = s.nextEffect) (aligned : Aligned a)
    (ready : Reservations a level) (helpers : TreeFrames s) :
    ∃ out : ValueDecoded FormalPermissionAuthenticatedNativeDecode.context false s,
      SourcePair FormalPermissionAuthenticatedNativeDecode.context false FormalPermissionAuthenticatedNativeDecode.tree (FormalPermissionAuthenticatedNativeDecode.code 0 1) s out ∧
      out = FormalPermissionAuthenticatedNativeDecode.output s 0 1 ∧ out.entries = FormalPermissionAuthenticatedNativeDecode.retained s.nextEffect ∧
      out.births = [s.nextEffect, s.nextEffect + 1, s.nextEffect + 2, s.nextEffect + 3] ∧
      out.state = {s with nextEffect := s.nextEffect + 4} ∧
      Aligned (afterFour a level) ∧
      (afterFour a level).permissions = a.permissions ++ out.entries
```

## Evidence, failures and execution ownership

Final R11 revision-1 artifact: 15285 bytes; SHA256 `828eef57d8caaa538c8feb91ad023dc45eb41e421b4eb430532e383ee1c75e91`.

Read-only commands: `cat`, `rg`, `sed`, Python file/manifest SHA256 and exact-statement comparison. The only edit tool was `apply_patch` on the leased artifact; Python wrote this exact handoff. No scratch/generated/cache outputs were created. No Lean/Lake/elan/checker probes, tests, Cargo, compiler edits, instrumentation, Git, dependency installation or reviewer commands ran. Commands executed by this leaf completed successfully except one initially incorrect read-only path lookup for the historical audit-2 stdout; the actual preserved path was then read. Project files pin Lean `leanprover/lean4:v4.35.0`, `-j1 -M1024`, zero external packages. Executable version was not queried under the primary's execution ownership.

R10 audit-2 material failure remains preserved: exit 1, 13.21 seconds, maximum RSS 788828 KiB; missing existential placeholder `w` at 192:10 and open `exact_tree_supplier`. Its stdout SHA256 `4fb15b5f0cd7d35c10db2dba47c53ebf0a801eef199c44171153dbcd1c7a0b5c`. R10 audit 1 and both raw plans/receipts remain unchanged. R10 review records a minor historical limitation: revision-2 proof-handoff bytes were not retained before revision 3 overwrote that path. R11 does not erase or reinterpret those failures.

This leaf has no Lean command exit, fresh printed type or axiom inventory to report. Kernel acceptance, exact theorem-type output and complete transitive axiom audits are PENDING primary release. A source search found no introduced `sorry`, `admit`, project axiom or checker bypass; that source search does not replace a kernel/axiom audit. Intended audit roots are the four fully qualified theorem names above. No self-certification or independent-review claim is made.

## Parent application and remaining premises

Represented: exactly the R5 Int/Unit/Function/nonempty-Tuple tree, both guards, omitted positive argument ports and negative concrete result ports, all four births and two local permissions. Other source constructors/error paths/enclosing publication stay within the original parent domain and remain outside this finite supplier.

The precise first remaining proof task is primary execution of a prospectively frozen R11 focused audit, establishing whether the explicit record and `SourcePair.tuple` conclusion are definitionally compatible. If accepted, the same-witness R9 application still depends on `Reservations a level` and `TreeFrames s`: concrete Rust reservation/copy/term successful returns and their local projected frame correspondence remain with source/native owners. No availability, local frame obligation, target `SourcePair` premise or native state 21 is manufactured. Original parent, helper/native authenticity, effect hygiene, consumer, soundness, principality, termination and production gates remain OPEN.

Construction and freeze completed within the assigned 300-second envelope; exact leaf CPU/RSS were not measured. Zero execution allowance spent and zero descendants. All writes STOPPED after this revision-1 handoff. Any successor edit requires primary release; preserve this artifact and handoff bytes before authorizing a successor revision.
