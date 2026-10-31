Sprint-ID / revision: EFFECT-PERMISSION-CANDIDATE-CALL-JOURNAL/20261030-r19, r1.
Assignment: R19-proof, rev1; author /root/effect_permission_candidate_call_journal_r19_lean.
Class: CHECKED CONDITIONAL MODEL; source-prefix authentication OPEN; independent review NOT_RUN; native/parent/production OPEN.

## Original claim and governing sources

Original parent: notes/theory/2026-10-13-intrusion-source-preservation-proof.md §§1,3,5; current correction notes/design/2026-10-24-birth-level-scc-intrusion.md §§2–6; authoritative top-level principles 2026-10-11 §§1–5. Every supported original source program, lawful finite history and retained occurrence remains in scope, with original source scopes and one shared strategy/witness. No source restriction is adopted by this local model. docs/yulang-whole-proof-closure-ja.md §§1–3 distinguishes conditional composition from the whole claim.

Exact parent definitions inspected: YulangClosure.SourceProblem.InferenceSoundness and NativeCorrespondence (Contracts.lean:128–149); parent composition YulangClosure.SourceProblem.native_success_elaborates (CoreComposition.lean:92), still requiring hnative, hinfer, helab for the SAME source scope/witness. Proposition definitions supply no concrete instances. Research drafts supply no semantic authority.

## Source transcription and precise unfinished edge

The source handoff and primary addendum identify direct ordinary graph-plan root dispatch, BeginLambda, FormalAnnotation without FormalEntry/record/unit actions, scalar collected children and positive_tuple through with_term_events: candidate_source.rs:1280–1340,2354–2488; candidate_scheme.rs:2898–2950; candidate_effect.rs:1617–1659,1877–1926; lib.rs:10594–10622.

R18 activeJournal concerns BranchTermArena.route_journal, NOT InferenceSession.route_journal. Model Journals retains both separately. BranchTermArena::new initializes arena None (term.rs:713); session initialization is lib.rs:10196. Store::begin_route calls terms.begin_route (lib.rs:3503); the session publishes its journal later (lib.rs:9477). Successful finish takes session journal then commits Store/arena; rollback takes both; preparation failures after Store begin roll arena back before session publication (lib.rs:9267–9545,9646–9678; Store delegates 3503–3558; term.rs:746–822). Spare journal payloads are omitted and never counted active. Microstep equations model only presence effects, not Rust assertion reachability, payload restoration, accounting, errors, unwinding, allocator validity or full machine semantics. committed_route_clears is an equation of completed presence updates for arbitrary input; it does not assert a wrapper can enter from arbitrary input.

Construction: runCalls starts at initial = (None,None). CompletedCall has explicit neutral named boundaries and completed successful wrapper microsteps; failure/rollback equations are separately proved, but failed source actions are not inserted into the successful target prefix. selectedSuffix computes root/start/drive/step, BeginLambda, formal preparation, tuple scratch and one collected-scalar return per child. No hypothesis states journal=None, a caller frame, or not activeJournal. The theorem also holds on an empty child list because presence updates do not depend on length; the actual selected positive tuple still requires nonempty, effect-free scalar children at its source owner.

FIRST REMAINING SOURCE PREMISE (owner Luna/source lane): authenticate the complete actual graph-plan prefix, including earlier component members, operator-provider branches and their transitive calls, as this CompletedCall trace while preserving BOTH journal projections and the SAME arena at the selected direct target. The local handoff does not enumerate those prior calls. The neutral classification is a transcription alphabet, not a proved law for every native action. No general all-call source correspondence relation is defined or proved. Therefore the checked result alone does NOT establish that the actual selected native call has an absent arena journal. This is the first missing edge; it is left OPEN rather than encoded as a None/frame hypothesis.

Parent application: selected_call_excludes_R18 applies R18 Conditions itself to atCallInput, whose journalPresent is COMPUTED from atPositiveTuple.arena; every other field is retained from the SAME i. This is a model projection, NOT evidence that an observed native TupleInput equals that projection. Thus it conditionally excludes R18's activeJournal conjunction on represented prefixes. It neither refutes R18 nor supplies native caller reachability. No five-event trace/bound is claimed: same-call source authentication and other R18 child/cache/capacity/reserve/allocator/claim/intern premises remain unestablished. Original source/native/parent/production closure stays OPEN.

Represented: two journal owners, initial absence, Store-before-session begin, successful completed wrapper commit, error rollback, prepublication failure, direct selected root/action suffix, Bool/Str/Int/Unit scalar returns, R18 predicate application. Omitted: authentication of full prior native prefix, arbitrary actions and nested/retained transaction bodies, native HIR/module instance, full heap/brands/term identities, effectful/nonscalar/record/other callers, cache and capacity outcomes, allocation/claim failures, callbacks/unwind/interleavings. These omissions do not remove cases from the original parent.

## Frozen bytes and execution

Contract SHA-256: 626bde02d87b7205530e5fb4c90598f4f7d2aad7c4e442fcce1d7d9b332be565.
R19 manifest: 3ba699f81d0a6f9f88cc63e3df744194cd758ace5ae636098b80870a020013c3; all 200 entries matched (manifest-check.json). Baseline d33805eb589ac89925bacab57b362df093456fe0.
R18 artifact: f9bfd9ea556128b27e850b5ca66934d46fd86d73a77bdfdbb3846142ad37abd7.
Source handoff e3cc387457f6362a650376cbbb093d5600e1ad3eb7f838f76fa488144d3ccd4c; primary addendum 52e188ffa8874091ba57fb1938bc168f68154f079e0cf6cd44e3ed53f734e4a3.
candidate_source.rs 96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a; candidate_scheme.rs 31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707. Other exact source/dependency hashes are in the checked manifest.
New artifact SHA-256: 7796394c7cc312f2a403d82fe938c31b7d3c2dc4092ad1c53ef6729496f4f83a. Construction-copy bytes match.
18-module construction-cone.json SHA-256: ac8285c2508b20209d9db7cc8e30194d0cb1044ceea9578ac10da59d046c67ca.
Audit-1.log SHA-256: af7a811f0a977bdf9859c48ec251927f37e62c2a48b53e87524e86f4a7b3caf2.

Installed native Lake resolved by read-only `elan which lake` (exit 0; existing-version warning retained in tool output); no installation or global change. Native binary: /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake. `lake --version`: Lake 5.0.0-src+eb6cafb (Lean 4.35.0), exit 0. `lake env lean --version`: Lean 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release, exit 0. Toolchain/config/manifest bytes were copied unchanged; no packages.

All generated/cache/scratch writes are under /tmp/yulang-effect-permission-candidate-call-journal-20261030-r19/. Exact project: construction/. Cache: construction/.lake/. Inputs copied from notes/theory/lean; no root import edits. Material failures preserved:

- construction-build-1.log, `LEAN_NUM_THREADS=1 <native-lake> build +YulangClosure.FormalPermissionCandidateCallJournal`: exit 1. Actual diagnostics: `unexpected token 'prefix'; expected '_' or identifier` and downstream parser errors. Repaired reserved identifier to priorCalls. No hole was introduced.
- Attempted second build used wrong cwd (repository root); redirection `../construction-build-2.log` was rejected `Read-only file system`, exit 1 before Lake launch. No outside file was written. This failure is recorded here because no log could be created.
- construction-build-3.log, cwd construction/, `LEAN_NUM_THREADS=1 <native-lake> --no-cache build +YulangClosure.FormalPermissionCandidateCallJournal`: exit 0, 19 jobs, new module 625 ms. No new-module warning; inherited warnings retained.
- Skill checker: command fully recorded in audit-command.json and audit-1.time; `python3 .agents/skills/yulang-lean-proofs/scripts/check_lean.py --project <scratch>/construction --lake <native-lake> --module YulangClosure.FormalPermissionCandidateCallJournal --timeout 90`, with each of the 12 theorem roots printed below passed separately through --theorem. Exit 0. One audit only, 2.35 s wall, 0.86 s user, 0.37 s system, maximum RSS 975388 KiB, zero swaps. TMPDIR was <scratch>/audit-tmp; helper temporary audit source was removed normally. All changed eight roots plus inherited four R18 roots were printed/audited. Broader inherited-root census remains primary-owned. No default/full build, tests, Cargo, Rust execution, instrumentation or network run.

Source-hole-search.txt inspects the 18-module cone for sorry/admit/axiom/skipKernelTC/native_decide: only ordinary prose matches in FormalPermissionSiteTraversal.lean:7 and FormalPermissionLiveCapture.lean:13. No code hole/project axiom/bypass match. This search supplements, and does not replace, the transitive printed axiom audits.

## Actual printed theorem types and complete axiom reports

The following is copied from the successful checker output, including inherited R18 roots. Expected whitelist: only propext, Classical.choice, Quot.sound. Actual new roots: propext only, except failed_preparation_clears has no axioms. R18 first two use propext; final two use propext and Quot.sound. No sorryAx, project axiom or native-evaluation assumption occurs.

```text
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionCandidateCallJournal.committed_route_clears
YulangClosure.FormalPermissionCandidateCallJournal.committed_route_clears : ∀
  (s : YulangClosure.FormalPermissionCandidateCallJournal.Journals),
  YulangClosure.FormalPermissionCandidateCallJournal.run s
      YulangClosure.FormalPermissionCandidateCallJournal.committedRoute =
    YulangClosure.FormalPermissionCandidateCallJournal.initial
'YulangClosure.FormalPermissionCandidateCallJournal.committed_route_clears' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.FormalPermissionCandidateCallJournal.committed_route_clears
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionCandidateCallJournal.rolled_back_route_clears
YulangClosure.FormalPermissionCandidateCallJournal.rolled_back_route_clears : ∀
  (s : YulangClosure.FormalPermissionCandidateCallJournal.Journals),
  YulangClosure.FormalPermissionCandidateCallJournal.run s
      YulangClosure.FormalPermissionCandidateCallJournal.rolledBackRoute =
    YulangClosure.FormalPermissionCandidateCallJournal.initial
'YulangClosure.FormalPermissionCandidateCallJournal.rolled_back_route_clears' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.FormalPermissionCandidateCallJournal.rolled_back_route_clears
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionCandidateCallJournal.failed_preparation_clears
YulangClosure.FormalPermissionCandidateCallJournal.failed_preparation_clears : YulangClosure.FormalPermissionCandidateCallJournal.run
    YulangClosure.FormalPermissionCandidateCallJournal.initial
    YulangClosure.FormalPermissionCandidateCallJournal.failedPreparation =
  YulangClosure.FormalPermissionCandidateCallJournal.initial
'YulangClosure.FormalPermissionCandidateCallJournal.failed_preparation_clears' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.FormalPermissionCandidateCallJournal.failed_preparation_clears
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionCandidateCallJournal.completed_prefix_clears
YulangClosure.FormalPermissionCandidateCallJournal.completed_prefix_clears : ∀
  (calls : List YulangClosure.FormalPermissionCandidateCallJournal.CompletedCall),
  YulangClosure.FormalPermissionCandidateCallJournal.runCalls YulangClosure.FormalPermissionCandidateCallJournal.initial
      calls =
    YulangClosure.FormalPermissionCandidateCallJournal.initial
'YulangClosure.FormalPermissionCandidateCallJournal.completed_prefix_clears' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.FormalPermissionCandidateCallJournal.completed_prefix_clears
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionCandidateCallJournal.selected_call_journals
YulangClosure.FormalPermissionCandidateCallJournal.selected_call_journals : ∀
  (priorCalls : List YulangClosure.FormalPermissionCandidateCallJournal.CompletedCall)
  (children : List YulangClosure.FormalPermissionCandidateCallJournal.Scalar),
  YulangClosure.FormalPermissionCandidateCallJournal.atPositiveTuple priorCalls children =
    YulangClosure.FormalPermissionCandidateCallJournal.initial
'YulangClosure.FormalPermissionCandidateCallJournal.selected_call_journals' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.FormalPermissionCandidateCallJournal.selected_call_journals
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionCandidateCallJournal.selected_call_arena_absent
YulangClosure.FormalPermissionCandidateCallJournal.selected_call_arena_absent : ∀
  (priorCalls : List YulangClosure.FormalPermissionCandidateCallJournal.CompletedCall)
  (children : List YulangClosure.FormalPermissionCandidateCallJournal.Scalar),
  (YulangClosure.FormalPermissionCandidateCallJournal.atPositiveTuple priorCalls children).arena = Option.none
'YulangClosure.FormalPermissionCandidateCallJournal.selected_call_arena_absent' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.FormalPermissionCandidateCallJournal.selected_call_arena_absent
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionCandidateCallJournal.selected_call_not_active
YulangClosure.FormalPermissionCandidateCallJournal.selected_call_not_active : ∀
  (i : YulangClosure.FormalPermissionStructuralBufferBound.TupleInput)
  (priorCalls : List YulangClosure.FormalPermissionCandidateCallJournal.CompletedCall)
  (children : List YulangClosure.FormalPermissionCandidateCallJournal.Scalar),
  (YulangClosure.FormalPermissionCandidateCallJournal.atCallInput i priorCalls children).journalPresent = Bool.false
'YulangClosure.FormalPermissionCandidateCallJournal.selected_call_not_active' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.FormalPermissionCandidateCallJournal.selected_call_not_active
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionCandidateCallJournal.selected_call_excludes_R18
YulangClosure.FormalPermissionCandidateCallJournal.selected_call_excludes_R18 : ∀
  (i : YulangClosure.FormalPermissionStructuralBufferBound.TupleInput)
  (priorCalls : List YulangClosure.FormalPermissionCandidateCallJournal.CompletedCall)
  (children : List YulangClosure.FormalPermissionCandidateCallJournal.Scalar),
  ¬YulangClosure.FormalPermissionStructuralBufferBound.Conditions
      (YulangClosure.FormalPermissionCandidateCallJournal.atCallInput i priorCalls children)
'YulangClosure.FormalPermissionCandidateCallJournal.selected_call_excludes_R18' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.FormalPermissionCandidateCallJournal.selected_call_excludes_R18
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionStructuralBufferBound.intern_events_exact
YulangClosure.FormalPermissionStructuralBufferBound.intern_events_exact : ∀
  (i : YulangClosure.FormalPermissionStructuralBufferBound.TupleInput),
  YulangClosure.FormalPermissionStructuralBufferBound.Conditions i →
    YulangClosure.FormalPermissionStructuralBufferBound.internEvents i =
      [{ lane := YulangClosure.FormalPermissionArenaEvents.Lane.interner, observation := i.interner.snapshot },
        { lane := YulangClosure.FormalPermissionArenaEvents.Lane.internedJournal,
          observation := i.internedJournal.snapshot },
        { lane := YulangClosure.FormalPermissionArenaEvents.Lane.pageDescriptors,
          observation := i.pageDescriptors.snapshot },
        { lane := YulangClosure.FormalPermissionArenaEvents.Lane.pagePositions,
          observation := i.pagePositions.snapshot },
        { lane := YulangClosure.FormalPermissionArenaEvents.Lane.claimedPagesJournal,
          observation := i.claimedPagesJournal.snapshot },
        { lane := YulangClosure.FormalPermissionArenaEvents.Lane.pageBacking, observation := i.pageSnapshot }]
'YulangClosure.FormalPermissionStructuralBufferBound.intern_events_exact' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.FormalPermissionStructuralBufferBound.intern_events_exact
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionStructuralBufferBound.intern_length
YulangClosure.FormalPermissionStructuralBufferBound.intern_length : ∀
  (i : YulangClosure.FormalPermissionStructuralBufferBound.TupleInput),
  YulangClosure.FormalPermissionStructuralBufferBound.Conditions i →
    (YulangClosure.FormalPermissionStructuralBufferBound.internSnapshots i).length = 6
'YulangClosure.FormalPermissionStructuralBufferBound.intern_length' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.FormalPermissionStructuralBufferBound.intern_length
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionStructuralBufferBound.conditional_seventh_assertion
YulangClosure.FormalPermissionStructuralBufferBound.conditional_seventh_assertion : ∀
  (i : YulangClosure.FormalPermissionStructuralBufferBound.TupleInput),
  YulangClosure.FormalPermissionStructuralBufferBound.Conditions i →
    ∀
      (entry :
        YulangClosure.FormalPermissionEventBuffer.Buffer YulangClosure.FormalPermissionTermCallControl.EventOutcome),
      YulangClosure.FormalPermissionEventBuffer.Layout entry [] →
        ∃ full,
          YulangClosure.FormalPermissionEventBuffer.Appends entry
              (YulangClosure.FormalPermissionStructuralBufferBound.internSnapshots i) full ∧
            YulangClosure.FormalPermissionEventBuffer.Layout full
                (YulangClosure.FormalPermissionStructuralBufferBound.internSnapshots i) ∧
              full.len = 6 ∧
                full.snapshots.toList =
                    List.map Option.some (YulangClosure.FormalPermissionStructuralBufferBound.internSnapshots i) ∧
                  YulangClosure.FormalPermissionStructuralBufferBound.attemptPush full i.structuralSnapshot =
                    YulangClosure.FormalPermissionStructuralBufferBound.PushResult.assertionFailure 6 6
'YulangClosure.FormalPermissionStructuralBufferBound.conditional_seventh_assertion' depends on axioms: [propext,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.FormalPermissionStructuralBufferBound.conditional_seventh_assertion
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionStructuralBufferBound.no_normal_seven_pushes
YulangClosure.FormalPermissionStructuralBufferBound.no_normal_seven_pushes : ∀
  (i : YulangClosure.FormalPermissionStructuralBufferBound.TupleInput),
  YulangClosure.FormalPermissionStructuralBufferBound.Conditions i →
    ∀
      (entry :
        YulangClosure.FormalPermissionEventBuffer.Buffer YulangClosure.FormalPermissionTermCallControl.EventOutcome),
      YulangClosure.FormalPermissionEventBuffer.Layout entry [] →
        ¬∃ last,
            YulangClosure.FormalPermissionEventBuffer.Appends entry
              (YulangClosure.FormalPermissionStructuralBufferBound.attemptedSnapshots i) last
'YulangClosure.FormalPermissionStructuralBufferBound.no_normal_seven_pushes' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.FormalPermissionStructuralBufferBound.no_normal_seven_pushes
```

## Freeze and handoff

Only repository writes: notes/theory/lean/YulangClosure/FormalPermissionCandidateCallJournal.lean and tasks/agent-loop/inbox/effect-permission-candidate-call-journal-r19-proof.md. Scratch inventory: construction/ (copied project and isolated .lake outputs), construction-build-1.log, construction-build-3.log, manifest-check.json, construction-cone.json, source-hole-search.txt, audit-command.json, audit-result.json, audit-1.log, audit-1.time, audit-tmp/. No other writer/cache was used. No children, scheduling/status/index/config/dependency/compiler/test/question/Git mutations; no contact outside the primary.

Finite 600-second assignment: frozen inside bound; first explicit clock 2026-10-29 15:09:29 UTC. Aggregate construction CPU/RSS was not instrumented; only the audit resource report above is measured. Every launched construction/audit subprocess has completed. No processes remain running for this leaf.

Writes-stopped receipt: STOPPED; both leased repository files are frozen at rev1 after this write. No subsequent writes by this leaf. Primary owns authentication, fresh independent review, source-prefix seam adjudication, broader inherited-root audit and integration. This is not self-certification.
