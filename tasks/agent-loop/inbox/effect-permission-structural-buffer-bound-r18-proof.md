Sprint-ID / contract revision: EFFECT-PERMISSION-STRUCTURAL-BUFFER-BOUND/20261029-r18; rev1.
Contract SHA-256: e81f4bf967fd39d300712a9438277c9d9ba05b7c9a89e75358997c7d284bd3b6.
Assignment-ID / handoff revision: R18-proof / rev1.
Outcome class: conditional; constructor module accepted by pinned Lean; complete axiom/type audit and independent review remain Luna-owned and pending at leaf freeze.
Worker: /root/effect_permission_structural_buffer_bound_r18_lean; session EFFECT-PERMISSION-STRUCTURAL-BUFFER-BOUND/20261029-R18. Actual launch is the primary's NEW_TASK packet. Requested role lean_prover/high; observed model/effort metadata UNKNOWN. No contributing descendants.
Exact leased writes: notes/theory/lean/YulangClosure/FormalPermissionStructuralBufferBound.lean and this handoff. All generated/scratch writes are beneath /tmp/yulang-effect-permission-structural-buffer-bound-20261029-r18/. No Rust/compiler, earlier artifact, root import, configuration, dependency, shared status, question, test, Cargo, Git or third-party writes/actions.

## Governing claim and scope

Original claim: notes/theory/2026-10-13-intrusion-source-preservation-proof.md §§1,3,5, corrected by notes/design/2026-10-24-birth-level-scc-intrusion.md §§2–6. Its quantification remains every supported original source program, lawful finite construction history and retained extrusion occurrence, preserving actual source scopes and one shared strategy/witness; soundness, coverage, normal progress and termination remain OPEN. The authoritative 2026-10-11 top-level principles are retained. docs/yulang-whole-proof-closure-ja.md §§1–3 separates inference, elaboration and native correspondence; it is not new semantic approval.

Exact parent interfaces read: YulangClosure.SourceProblem.InferenceSoundness and NativeCorrespondence (Contracts.lean:128–149), and YulangClosure.SourceProblem.native_success_elaborates (CoreComposition.lean:92). The former are proposition definitions. The latter requires all of hnative, hinfer and helab, with the same source scope and witness. R18 proves none of these concrete premises. No manuscript draft is promoted to semantic authority.

The fixed R18 question is a local positive tuple obstruction before the wrapper drain. It neither refutes nor proves the original source theorem. First remaining source/native premise, owned by Luna/source lane: instantiate all R18 Conditions and empty entry on one authenticated candidate_formal_value_pair call, with the SAME arena/cache/journal, five actual reserve growth observations and successful allocator/claim/intern outcomes; alternatively establish an actual invariant excluding their conjunction. No such native instance or exclusion invariant is constructed here.

## Frozen inputs and artifact

All 197 manifest entries matched their frozen SHA-256 values before construction. R18 manifest: 4a7f3a8e1e75ba0b761b7c927a7b6eaaf87b559df041a6d52915cd360ce63439. R18 frozen source handoff: 2deb722afa72c76aeb09e5768de9803123ca1178e991c52e488f14e5ac8cd62c. Baseline commit from manifest: d33805eb589ac89925bacab57b362df093456fe0.

Direct dependency R17 FormalPermissionEventBuffer.lean: 1886b763ebd493721cd6cb7d03f32ff3c43555587a53ccf4e0ee3c351c450b57. R16 FormalPermissionArenaEvents.lean: 02ef97716d882073ccb2e53c53bbf8046c80e82a517253898db5d1c02cd1b8b3.

Frozen new artifact SHA-256: f9bfd9ea556128b27e850b5ca66934d46fd86d73a77bdfdbb3846142ad37abd7.
The construction copy has the same bytes. The 17-module dependency inventory is /tmp/yulang-effect-permission-structural-buffer-bound-20261029-r18/construction-cone.json, SHA-256 9a53a24e34a0806da37621b2364811eb409b94a9a87ef7b666617e15249c4e8a.

## Source correspondence and explicit premises

candidate_effect.rs:1617–1659 selects the nonempty tuple path; Bool/Str/Int/Unit collected children can avoid postfix allocation. The source handoff leaves caller-level candidate reachability open. term.rs:1272–1303 validates each positive child, reserves/copies the tuple payload and materializes Arc backing. intern_structure, term.rs:1352–1385, checks cache/payload and reserves the structural vector before intern. intern, term.rs:1166–1201, and push, term.rs:1083–1158, order the five reserves and PageBacking. term.rs:961–983 records each changed capacity before checking reserve error. term.rs:577–583 asserts len < 6 before indexed write/increment. lib.rs:10594–10622 drains only after normal constructor return.

TupleInput supplies observed primitive results rather than free success/growth Booleans. Each ReserveReceipt retains beforeCapacity, afterCapacity, Except result and its snapshot; grewSuccessfully requires BOTH Ok and unequal capacity observations. Conditions explicitly retains nonempty children; each child's lookup and positive Value endpoint; tuple-copy reserve Ok; materialized backing identity; checked payload arithmetic; structural reserve Ok; shared cache miss; active journal; needed page; all five reserve successes and actual capacity inequalities; page allocation Ok; page claim Ok; and successful intern result. Empty entry is a separate Layout entry [] premise. None of these observations is authenticated as Rust execution by Lean.

internInput reuses only R16's mode-independent protocol, not its starts/valid/appended guards. Its administrative liveVariable mode field is ignored by protocol; tuple validity remains Conditions and is never inferred from a live-variable or function classification. Allocation/claim failures are merged only outside the proved successful branch; no failure-branch theorem is claimed. Successful reserve alone is never used as growth evidence.

internEvents is computed by R16 run(protocol(internInput i)); it is not an arbitrary seven-element input list. Its exact six events are Interner, InternedJournal, PageDescriptors, PagePositions, ClaimedPagesJournal and PageBacking. attemptedSnapshots adds the unconditional structural-owner snapshot only on the selected successful-intern source branch. R17 Appends and Layout prove the six actual Option slots are occupied, with len = 6 and no padding. attemptPush models assertion-before-write: the seventh structural push yields assertionFailure 6 6. There is no seventh stored element, recoverable Err, takeEvents, finish or wrapper return in that selected local trace.

Represented: positive nonempty tuple local construction; valid children; shared cache miss; active journal; page-needed case; all five changed-successful reserves; allocation/claim/intern success; successful tuple/structural preparation; empty event buffer; exact ordered physical writes and final attempted index.
Omitted, still open: full Rust heap/TermNode/brand/lineage semantics, actual candidate caller and collected-child derivations, simultaneous real capacity reachability, concrete snapshot authenticity, allocator/address/base validity, native source simulation, injected cfg(test) post-growth failures, all failed primitive branches, cache hits, absent journals, existing pages, invalid/empty tuples, negative tuple and other structural constructors, callback/unwind/destructor behavior and interleavings. These cases remain in the original parent domain; this conditional packet makes no whole-domain claim.

## Public declarations and exact types

Namespace for all four: YulangClosure.FormalPermissionStructuralBufferBound.

```lean
intern_events_exact (i : TupleInput) (h : Conditions i) :
  internEvents i =
    [⟨.interner, i.interner.snapshot⟩,
     ⟨.internedJournal, i.internedJournal.snapshot⟩,
     ⟨.pageDescriptors, i.pageDescriptors.snapshot⟩,
     ⟨.pagePositions, i.pagePositions.snapshot⟩,
     ⟨.claimedPagesJournal, i.claimedPagesJournal.snapshot⟩,
     ⟨.pageBacking, i.pageSnapshot⟩]

intern_length (i : TupleInput) (h : Conditions i) :
  (internSnapshots i).length = 6

conditional_seventh_assertion (i : TupleInput) (h : Conditions i)
    (entry : FormalPermissionEventBuffer.Buffer EventOutcome)
    (emptyEntry : FormalPermissionEventBuffer.Layout entry []) :
  ∃ full : FormalPermissionEventBuffer.Buffer EventOutcome,
    FormalPermissionEventBuffer.Appends entry (internSnapshots i) full ∧
    FormalPermissionEventBuffer.Layout full (internSnapshots i) ∧
    full.len = 6 ∧
    full.snapshots.toList = (internSnapshots i).map some ∧
    attemptPush full i.structuralSnapshot = .assertionFailure 6 6

no_normal_seven_pushes (i : TupleInput) (h : Conditions i)
    (entry : FormalPermissionEventBuffer.Buffer EventOutcome)
    (emptyEntry : FormalPermissionEventBuffer.Layout entry []) :
  ¬ ∃ last, FormalPermissionEventBuffer.Appends entry (attemptedSnapshots i) last
```

These are source-declared types, not claimed printed audit output. Private helper reserve_success also compiles. Luna owns printing each theorem type and #print axioms, the skill checker when possible, all 73 inherited roots and independent review. No axiom result is claimed by this leaf and no helper audit was run. The source search of the 17-module cone found no holes/project axioms/bypasses: its only word matches were ordinary prose in SiteTraversal.lean:7 and LiveCapture.lean:13. That search is not a transitive kernel axiom audit.

## Actual construction commands and preserved failures

Installed native toolchain, whose binary hashes are pinned in the manifest:
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --version
returned Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0), exit 0.
The native lean --version and lake env lean --version both returned Lean 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release, exit 0.

Construction project: /tmp/yulang-effect-permission-structural-buffer-bound-20261029-r18/construction/. It contains copied Lean sources/configuration, no changed manifest or root import. Only this isolated Lake cache was written by the leaf.

Command, with LEAN_NUM_THREADS=1:
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake build +YulangClosure.FormalPermissionStructuralBufferBound`

- construction-build-1.stdout/.stderr: exit 1. Initial relative output path was evaluated from the isolated project, so source creation failed and Lake reported module file absent. No theorem claim was made.
- construction-build-2.stdout/.stderr: exit 1. Fresh imports built; new definitions lacked Decidable instances for Except equality and existential allocation success. Lean reported generated placeholder warnings downstream, plus an observation-projection goal. No explicit source hole was introduced. Repaired by matching actual Except returns and using their supplied success witnesses.
- construction-build-3.stdout/.stderr: exit 1. Remaining exact goal was a five-conjunct equality of ReserveReceipt.outcome.observation with its snapshot. Repaired with five explicit reflexivity proofs.
- construction-build-4.stdout/.stderr: exit 0, 18 jobs, new module 415 ms. Existing inherited linter warnings were preserved. No new-module warning remains.

Final construction-only direct check (imports built first), using the same native Lake:
`/usr/bin/time -v -o ../construction-final.time lake env lean -j1 -M1024 YulangClosure/FormalPermissionStructuralBufferBound.lean`
exit 0; construction-final.stdout and .stderr empty. Actual resource report: wall 4.37 s, user 0.44 s, system 0.64 s, maximum RSS 749712 KiB, zero swaps, zero file-system outputs for this command. Aggregate construction resource usage was not instrumented. The first explicit clock receipt was 2026-10-29 14:51:36 UTC; construction and handoff completed inside the assigned 600-second bound. All raw logs and generated artifacts remain in the one granted /tmp tree; no process is left running.

## Parent application and STOPPED receipt

The useful parent application is conditional obstruction: any authenticated selected tuple entry satisfying Conditions and empty Layout has no normal seven-push Appends execution; the exact structural attempt hits len = physical size = 6 before the wrapper drain. This does not yield p.NativeCorrespondence, p.InferenceSoundness, p.Elaboration, inference termination, source preservation or production authority. It also does not prove that any native caller can satisfy all premises.

Boundary to Luna: frozen complete type/axiom audit (four public roots plus inherited roots), source correspondence adjudication, independent review, and concrete candidate-call primitive evidence or exclusion invariant. No installation/dependency request is needed. No compiler repair is authorized or proposed as completed work.

Worker state: STOPPED. Both leased files frozen at rev1 after this handoff write. All construction subprocesses completed; no descendants; no unresolved generated-output writers; no further writes or processes by this leaf. Pending independent audit/review/integration, not self-certified closure.
