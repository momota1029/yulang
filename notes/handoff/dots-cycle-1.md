# dots cycle 1 — I-1 / T1c (partial)

- Instruction ID: I-1, inbox update 2026-11-08 17:30 JST, ACTIVE.
- Cycle number: 1 of maximum 12. No previous cycle report existed.
- Base: `c6bdf6b3c8e4b3362096b0e499a1e28b9aeebd41` (`integration/m1-final`).
- Code verified at local commit `ce14754c5`; publication uses separate contents-API commits.
- Branch: `work/dots-main` only. No writes to integration/m1-final, yulang3, main, spec/, notes/plan/, or lakefile.
- Clone filesystem creation recorded 2026-11-08 08:13:14 UTC. First 8-file publication and exact tree comparison completed 08:24:50 UTC: **11 minutes 36 seconds** to that point. Final report publication follows this record.
- Final verification: 08:21:33.711–08:22:20.742 UTC, **47.031 seconds**, incremental build.

## Acceptance status

**T1c is NOT complete.** No final resolve_exact, no saturation termination theorem,
and no X13–X16 outer-entry PROVED statement was added. This cycle completes a
candidate-local ordinary-slot boundary and finite source-occurrence allocation,
not all source applicability or an associated-declaration producer.

Priority 1 partial: for each scalar candidate separately, append the candidate's
lower ≤ head ≤ upper ordinary atoms to the same previous state, run the actual
ordinary solver, and THEN collect feasible candidates. `solutions_exact` covers
every returned solution family and every assignment up to the existing solver's
AssignmentEquivalent, not a chosen point. Candidate assumptions are not committed
to the global state just because the list has one candidate. This is not yet K2,
knownness or the final language-visible selected/pending classification.

The concrete int/str before/after example proves that a separately supplied
shared equality to int removes str. It runs this new collection entry, but the
equality is provided as an ordinary constraint. It is **not** the requested full
`impl Parent (box 'a) where Left 'a, Right 'a` source example: deriving that
constraint from the Right declaration and lowering the shared source variable
is still unproved.

Priority 2 partial: the allocator really computes `2 * row + side` from a finite
list of actual Requests, retains distinct endpoint occurrences, and recovers the
original endpoint. `source_bounds_preserved` connects these allocated slots to
the candidate inequalities under any supplied interpretation. The interpretation's
full nominal semantic adequacy and closure under dynamically generated children
are not proved. Distinct syntactic occurrences are not automatically unified into
a common source variable; that graph/source identity bridge remains.

Priorities 3/4: no saturation driver/termination/final Classify iff was completed.

## Files

New Lean modules:
- `lean/Yulang/CommonRoleEndpointSlots.lean`
- `lean/Yulang/CommonRoleCandidateStateFrontier.lean`
- `lean/Yulang/CommonRoleIntervalCandidateFrontier.lean`

Append-only registration/documentation: `lean/Yulang.lean`, `lean/Audit.lean`,
`lean/README.md`. Two new design files and this report make **9 published files**
relative to the base. All 29 public theorems are registered in Audit.

## Theorems (Japanese statements; full exact types below)

### CommonRoleEndpointSlots (10)

- `decode_allocate`: 任意の有限表 table と有効な occurrence source について、計算したslotをdecodeすると元のsourceに戻る。
- `allocate_decode`: 任意の有限表tableとその範囲内のslotについて、decode後にallocateすると元slotに戻る。
- `allocate_injective`: 任意のtableと二つのsourceについて、allocated slotが等しいならsourceも等しい。
- `endpoint_preserved`: 任意のtable/sourceについて、allocated slotから回収したTyは元endpointそのもの。
- `interpretation_preserved`: 任意の型（Sort）α、解釈Ty→α、table/sourceについて、allocated assignmentの値は元endpointの解釈に等しい。解釈の正しさ自体は仮定も結論もしていない。
- `nominal_preserved`: 任意のtable/source/nameで、元endpointがnamed atom nameなら回収値も同じnamed atom。
- `wrapped_nominal_preserved`: 任意のtable/source/name/payloadで、元endpointがnominal wrapperなら回収値も同じwrapper/payload。
- `distinct_sources_distinct_slots`: 任意のtableの異なる二sourceは異なるslotになる。
- `request_lower_preserved`, `request_upper_preserved`: 任意の実Request列と有効なindexについて、収集・割当後の下界/上界はそのrequestの元の下界/上界に等しい。

### CommonRoleCandidateStateFrontier (11)

- `equality_grammar`: 任意のslotとscalar headについて、二方向の等式atomsは既存solverのchild/width/row-support文法を満たす。
- `extend_exact`: 任意のgrammar付きState、slot、head、同じassignmentについて、延長stateの全制約充足 iff 元stateの充足かつslot値とheadのCommon.Equivalent。
- `accepts_exact`: 任意のState/slot/candidateで、実solverの受理bool=true iff 一つのassignmentが元stateとhead等価性を同時に満たす。
- `collect_exact`: 任意のState/slot/可視候補列/candidateについて、出力への所属 iff 可視列への所属かつFits。
- `collect_antitone`: 任意のbefore/after State、slot、候補列、candidateについて、全assignmentでafterの充足がbeforeの充足を含意する前提なら、afterに残るcandidateはbeforeにも残る。
- `fits_after_equation`: 任意のState/slot/scalar head/candidateについて、共有等式を追加したFits iff 元Fitsかつ追加head=candidate.head。
- `collect_after_equation`: 任意のState/slot/head/可視列/candidateについて、共有等式追加後の候補所属 iff 元の所属かつhead一致。
- `empty_fits`: 任意の有効なslotとcandidateは空stateのFitsを満たす。
- `singleton_remains_feasible`: 任意のslot/candidateについて、空stateのsingleton候補列の収集結果はそのsingleton。これは型変数の解を返す定理ではない。
- `before_associated_equation`: 1 slotの空state、int/strの2候補では両方がcollectに所属する。
- `after_associated_equation`: 同じ1 slotへint等式を共有制約として追加すると、intは所属しstrは所属しない。

### CommonRoleIntervalCandidateFrontier (8)

- `constraints_grammar`: 任意の二端点Request/headでlower≤head≤upperのatomsはsolver文法を満たす。
- `prepare_exact`: 任意のState/二端点Request/candidate/assignmentについて、候補別stateの充足 iff 元stateの充足かつ元下界≤candidate head≤元上界。
- `accepts_exact`: 任意のState/二端点Request/candidateについて、実solverが非空 iff 一つのassignmentで元stateと両不等式が同時充足。
- `collect_exact`: 任意のState/二端点Request/候補列/candidateについて、収集後所属 iff 可視所属かつFits。
- `collect_antitone`: 任意のbefore/after State、二端点Request/候補列/candidateについて、全afterモデルがbeforeモデルである前提ならafter所属からbefore所属が従う。
- `same_slot_exact`: 任意のState/slot/candidateについて、下界と上界が同じsource slotのFitsはscalar equality版Fitsと同値。
- `solutions_exact`: 任意のState/二端点Request/candidate/assignmentについて、元stateと両不等式の充足 iff 実solverが返したあるscheme・rows・parametersがそのassignmentとAssignmentEquivalent。
- `source_bounds_preserved`: 任意の有限Request列、有効index、Ty→Compの解釈、割当サイズに合ったState、candidateについて、実allocatorで生成した制約の充足 iff 元stateの充足かつ元Requestの解釈下界≤head≤解釈上界。

## Commands and verification

- `git clone --branch integration/m1-final --single-branch https://github.com/momota1029/yulang.git yulang-dots-cycle`: success.
- Read standing orders, inbox, AGENTS/rules, T1c plan, T1b design/report, conformance list, relevant spec 6.2–6.5.
- `bash tools/verify-lean.sh . origin/integration/m1-final`: baseline PASS, exit 0, 1131 jobs, Audit 6072, gate 82004.
- `lake build Yulang.CommonRoleIntervalCandidateFrontier --wfail`: final focused PASS, exit 0, 276 jobs.
- `lake build Yulang.CommonRoleEndpointSlots --wfail`: separate worktree focused PASS, 266 jobs.
- Small local commits at theorem boundaries, followed by registration commit.
- Final command includes `cd lean && lake build --wfail`, Audit, and axiom gate. Full output:

```text
verify-lean: . @ ce14754c5 (base origin/integration/m1-final)
ok: lake build --wfail (Build completed successfully (1134 jobs).)
ok: Audit.lean exit 0
ok: axioms only propext/Classical.choice/Quot.sound over 6101 printed declarations
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended
ok: AXIOM-GATE-PASS: 82152 declarations
verify-lean: PASS
```

Final exit code: **0**. `#check @...` type dump also succeeds (exit 0).

## Interruptions / limits

No environment loss or timeout. Initial new-module focused compilation failed on
list membership simplification; corrected in the new modules and rerun successfully.
A type-report-only invocation used unsupported `pp.width`; removed the option and
reran successfully. Neither issue is hidden as a successful attempt. Baseline and
final builds ran serially in this worktree; the allocator used its own worktree.

No semantic decision was required for the stated boundary, so no question note was
added. The already answered sibling-finalization policy remains unchanged. The new
collector is not a finalizer and does not infer a source type from singleton visibility.
Usage accounting is **unknown**.

## Next exact lemmas / next cycle (1–3)

1. `associated_source_update_exact`: from an actual selected Right declaration and
   shared source variable, derive precisely the ordinary equality used in the
   Parent/Left/Right example, retaining old state and not choosing a type from a
   singleton impl set.
2. `reachable_endpoint_table_complete`: collect every dynamically generated child
   endpoint into a finite source-identity table; prove graph identity/nominal
   interpretation and compatibility with the producer, not only arbitrary transport.
3. `stable_source_frontier_exact`: join candidate-local constraint solving to K2,
   knownness and the source frontier, defer intermediate pending/ambiguity until
   saturation, then prove final Classify iff and an actual X13–X16 outer example.

The next cycle must refetch integration/m1-final and reread standing orders and
inbox. Do not treat these suggestions as overriding a changed inbox. Stop after
cycle 12 under I-1. No work continues between cycles.

## Exact Lean theorem types

```text
Yulang.CommonRoleEndpointSlots.decode_allocate : ∀ (table : Yulang.CommonRoleEndpointSlots.Table)
  (source : Yulang.CommonRoleEndpointSlots.Source table),
  Eq.{1} (Yulang.CommonRoleEndpointSlots.decode table (Yulang.CommonRoleEndpointSlots.allocate table source)) source
Yulang.CommonRoleEndpointSlots.allocate_decode : ∀ (table : Yulang.CommonRoleEndpointSlots.Table)
  (slot : Fin (HMul.hMul.{0, 0, 0} 2 (List.length.{0} table))),
  Eq.{1} (Yulang.CommonRoleEndpointSlots.allocate table (Yulang.CommonRoleEndpointSlots.decode table slot)) slot
Yulang.CommonRoleEndpointSlots.allocate_injective : ∀ (table : Yulang.CommonRoleEndpointSlots.Table)
  (left right : Yulang.CommonRoleEndpointSlots.Source table),
  Eq.{1} (Yulang.CommonRoleEndpointSlots.allocate table left) (Yulang.CommonRoleEndpointSlots.allocate table right) →
    Eq.{1} left right
Yulang.CommonRoleEndpointSlots.endpoint_preserved : ∀ (table : Yulang.CommonRoleEndpointSlots.Table)
  (source : Yulang.CommonRoleEndpointSlots.Source table),
  Eq.{1} (Yulang.CommonRoleEndpointSlots.slotEndpoint table (Yulang.CommonRoleEndpointSlots.allocate table source))
    (Yulang.CommonRoleEndpointSlots.endpoint table source)
@Yulang.CommonRoleEndpointSlots.interpretation_preserved.{u_1} : ∀ {α : Sort u_1}
  (table : Yulang.CommonRoleEndpointSlots.Table) (interpret : Yulang.CommonRoleSettledSyntax.Ty → α)
  (source : Yulang.CommonRoleEndpointSlots.Source table),
  Eq.{u_1}
    (Yulang.CommonRoleEndpointSlots.assignment.{u_1} table interpret
      (Yulang.CommonRoleEndpointSlots.allocate table source))
    (interpret (Yulang.CommonRoleEndpointSlots.endpoint table source))
Yulang.CommonRoleEndpointSlots.nominal_preserved : ∀ (table : Yulang.CommonRoleEndpointSlots.Table)
  (source : Yulang.CommonRoleEndpointSlots.Source table) (name : Nat),
  Eq.{1} (Yulang.CommonRoleEndpointSlots.endpoint table source)
      (Yulang.CommonRoleSettledSyntax.Ty.atom (Yulang.CommonRoleSettledSyntax.Atom.named name)) →
    Eq.{1} (Yulang.CommonRoleEndpointSlots.slotEndpoint table (Yulang.CommonRoleEndpointSlots.allocate table source))
      (Yulang.CommonRoleSettledSyntax.Ty.atom (Yulang.CommonRoleSettledSyntax.Atom.named name))
Yulang.CommonRoleEndpointSlots.wrapped_nominal_preserved : ∀ (table : Yulang.CommonRoleEndpointSlots.Table)
  (source : Yulang.CommonRoleEndpointSlots.Source table) (name : Nat) (payload : Yulang.CommonRoleSettledSyntax.Ty),
  Eq.{1} (Yulang.CommonRoleEndpointSlots.endpoint table source)
      (Yulang.CommonRoleSettledSyntax.Ty.wrap (Yulang.CommonRoleSettledSyntax.Constructor.nominal name) payload) →
    Eq.{1} (Yulang.CommonRoleEndpointSlots.slotEndpoint table (Yulang.CommonRoleEndpointSlots.allocate table source))
      (Yulang.CommonRoleSettledSyntax.Ty.wrap (Yulang.CommonRoleSettledSyntax.Constructor.nominal name) payload)
Yulang.CommonRoleEndpointSlots.distinct_sources_distinct_slots : ∀ (table : Yulang.CommonRoleEndpointSlots.Table)
  (left right : Yulang.CommonRoleEndpointSlots.Source table),
  Ne.{1} left right →
    Ne.{1} (Yulang.CommonRoleEndpointSlots.allocate table left) (Yulang.CommonRoleEndpointSlots.allocate table right)
Yulang.CommonRoleEndpointSlots.request_lower_preserved : ∀ (requests : List.{0} Yulang.CommonRoleOpenDescent.Request)
  (index : Fin (List.length.{0} requests)),
  Eq.{1}
    (Yulang.CommonRoleEndpointSlots.slotEndpoint (Yulang.CommonRoleEndpointSlots.collect requests)
      (Yulang.CommonRoleEndpointSlots.allocate (Yulang.CommonRoleEndpointSlots.collect requests)
        (Yulang.CommonRoleEndpointSlots.requestSource requests index false)))
    (getElem.{0, 0, 0} requests ↑index ⋯).lower
Yulang.CommonRoleEndpointSlots.request_upper_preserved : ∀ (requests : List.{0} Yulang.CommonRoleOpenDescent.Request)
  (index : Fin (List.length.{0} requests)),
  Eq.{1}
    (Yulang.CommonRoleEndpointSlots.slotEndpoint (Yulang.CommonRoleEndpointSlots.collect requests)
      (Yulang.CommonRoleEndpointSlots.allocate (Yulang.CommonRoleEndpointSlots.collect requests)
        (Yulang.CommonRoleEndpointSlots.requestSource requests index true)))
    (getElem.{0, 0, 0} requests ↑index ⋯).upper
@Yulang.CommonRoleCandidateStateFrontier.equality_grammar : ∀ {n : Nat} (slot : Fin n) (head : Yulang.Inference.Base),
  Yulang.PresenceGeneratedChildGrammar.GoodAtoms (Yulang.CommonRoleCandidateStateFrontier.equality slot head) ∧
    Yulang.PresenceGeneratedWidth.WidthAtoms (Yulang.CommonRoleCandidateStateFrontier.equality slot head) ∧
      Yulang.PresenceSourceConstraintSupport.GoodAtoms (Yulang.CommonRoleCandidateStateFrontier.equality slot head)
@Yulang.CommonRoleCandidateStateFrontier.extend_exact : ∀ {n : Nat} (s : Yulang.CommonRoleSettledConstraints.State n)
  (slot : Fin n) (head : Yulang.Inference.Base)
  (assignment : Fin n → Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model),
  Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model assignment
      (Yulang.CommonRoleCandidateStateFrontier.extend s slot head).atoms ↔
    Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model assignment s.atoms ∧
      Yulang.Common.Equivalent (Prod.fst.{0, 0} (assignment slot)) (Yulang.CommonSyntax.Layer.base.{0, 0} head)
@Yulang.CommonRoleCandidateStateFrontier.accepts_exact : ∀ {n : Nat} (s : Yulang.CommonRoleSettledConstraints.State n)
  (slot : Fin n) (c : Yulang.CommonRoleCandidateStateFrontier.Candidate),
  Eq.{1} (Yulang.CommonRoleCandidateStateFrontier.accepts s slot c) true ↔
    Yulang.CommonRoleCandidateStateFrontier.Fits s slot c
@Yulang.CommonRoleCandidateStateFrontier.collect_exact : ∀ {n : Nat} (s : Yulang.CommonRoleSettledConstraints.State n)
  (slot : Fin n) (visible : List.{0} Yulang.CommonRoleCandidateStateFrontier.Candidate)
  (c : Yulang.CommonRoleCandidateStateFrontier.Candidate),
  Membership.mem.{0, 0} (Yulang.CommonRoleCandidateStateFrontier.collect s slot visible) c ↔
    Membership.mem.{0, 0} visible c ∧ Yulang.CommonRoleCandidateStateFrontier.Fits s slot c
@Yulang.CommonRoleCandidateStateFrontier.collect_antitone : ∀ {n : Nat}
  (before after : Yulang.CommonRoleSettledConstraints.State n) (slot : Fin n)
  (visible : List.{0} Yulang.CommonRoleCandidateStateFrontier.Candidate),
  (∀ (assignment : Fin n → Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model),
      Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model assignment after.atoms →
        Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model assignment before.atoms) →
    ∀ (c : Yulang.CommonRoleCandidateStateFrontier.Candidate),
      Membership.mem.{0, 0} (Yulang.CommonRoleCandidateStateFrontier.collect after slot visible) c →
        Membership.mem.{0, 0} (Yulang.CommonRoleCandidateStateFrontier.collect before slot visible) c
@Yulang.CommonRoleCandidateStateFrontier.fits_after_equation : ∀ {n : Nat}
  (s : Yulang.CommonRoleSettledConstraints.State n) (slot : Fin n) (head : Yulang.Inference.Base)
  (c : Yulang.CommonRoleCandidateStateFrontier.Candidate),
  Yulang.CommonRoleCandidateStateFrontier.Fits (Yulang.CommonRoleCandidateStateFrontier.extend s slot head) slot c ↔
    Yulang.CommonRoleCandidateStateFrontier.Fits s slot c ∧ Eq.{1} head c.head
@Yulang.CommonRoleCandidateStateFrontier.collect_after_equation : ∀ {n : Nat}
  (s : Yulang.CommonRoleSettledConstraints.State n) (slot : Fin n) (head : Yulang.Inference.Base)
  (visible : List.{0} Yulang.CommonRoleCandidateStateFrontier.Candidate)
  (c : Yulang.CommonRoleCandidateStateFrontier.Candidate),
  Membership.mem.{0, 0}
      (Yulang.CommonRoleCandidateStateFrontier.collect (Yulang.CommonRoleCandidateStateFrontier.extend s slot head) slot
        visible)
      c ↔
    Membership.mem.{0, 0} (Yulang.CommonRoleCandidateStateFrontier.collect s slot visible) c ∧ Eq.{1} head c.head
@Yulang.CommonRoleCandidateStateFrontier.empty_fits : ∀ {n : Nat} (slot : Fin n)
  (c : Yulang.CommonRoleCandidateStateFrontier.Candidate),
  Yulang.CommonRoleCandidateStateFrontier.Fits Yulang.CommonRoleSettledConstraints.State.empty slot c
@Yulang.CommonRoleCandidateStateFrontier.singleton_remains_feasible : ∀ {n : Nat} (slot : Fin n)
  (c : Yulang.CommonRoleCandidateStateFrontier.Candidate),
  Eq.{1}
    (Yulang.CommonRoleCandidateStateFrontier.collect Yulang.CommonRoleSettledConstraints.State.empty slot
      (List.cons.{0} c List.nil.{0}))
    (List.cons.{0} c List.nil.{0})
Yulang.CommonRoleCandidateStateFrontier.before_associated_equation : Membership.mem.{0, 0}
    (Yulang.CommonRoleCandidateStateFrontier.collect Yulang.CommonRoleSettledConstraints.State.empty 0
      (List.cons.{0} Yulang.CommonRoleCandidateStateFrontier.leftInt
        (List.cons.{0} Yulang.CommonRoleCandidateStateFrontier.leftStr List.nil.{0})))
    Yulang.CommonRoleCandidateStateFrontier.leftInt ∧
  Membership.mem.{0, 0}
    (Yulang.CommonRoleCandidateStateFrontier.collect Yulang.CommonRoleSettledConstraints.State.empty 0
      (List.cons.{0} Yulang.CommonRoleCandidateStateFrontier.leftInt
        (List.cons.{0} Yulang.CommonRoleCandidateStateFrontier.leftStr List.nil.{0})))
    Yulang.CommonRoleCandidateStateFrontier.leftStr
Yulang.CommonRoleCandidateStateFrontier.after_associated_equation : Membership.mem.{0, 0}
    (Yulang.CommonRoleCandidateStateFrontier.collect
      (Yulang.CommonRoleCandidateStateFrontier.extend Yulang.CommonRoleSettledConstraints.State.empty 0
        Yulang.Inference.Base.int)
      0
      (List.cons.{0} Yulang.CommonRoleCandidateStateFrontier.leftInt
        (List.cons.{0} Yulang.CommonRoleCandidateStateFrontier.leftStr List.nil.{0})))
    Yulang.CommonRoleCandidateStateFrontier.leftInt ∧
  ¬Membership.mem.{0, 0}
      (Yulang.CommonRoleCandidateStateFrontier.collect
        (Yulang.CommonRoleCandidateStateFrontier.extend Yulang.CommonRoleSettledConstraints.State.empty 0
          Yulang.Inference.Base.int)
        0
        (List.cons.{0} Yulang.CommonRoleCandidateStateFrontier.leftInt
          (List.cons.{0} Yulang.CommonRoleCandidateStateFrontier.leftStr List.nil.{0})))
      Yulang.CommonRoleCandidateStateFrontier.leftStr
@Yulang.CommonRoleIntervalCandidateFrontier.constraints_grammar : ∀ {n : Nat}
  (q : Yulang.CommonRoleIntervalCandidateFrontier.Request n) (head : Yulang.Inference.Base),
  Yulang.PresenceGeneratedChildGrammar.GoodAtoms (Yulang.CommonRoleIntervalCandidateFrontier.constraints q head) ∧
    Yulang.PresenceGeneratedWidth.WidthAtoms (Yulang.CommonRoleIntervalCandidateFrontier.constraints q head) ∧
      Yulang.PresenceSourceConstraintSupport.GoodAtoms (Yulang.CommonRoleIntervalCandidateFrontier.constraints q head)
@Yulang.CommonRoleIntervalCandidateFrontier.prepare_exact : ∀ {n : Nat}
  (s : Yulang.CommonRoleSettledConstraints.State n) (q : Yulang.CommonRoleIntervalCandidateFrontier.Request n)
  (c : Yulang.CommonRoleCandidateStateFrontier.Candidate)
  (assignment : Fin n → Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model),
  Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model assignment
      (Yulang.CommonRoleIntervalCandidateFrontier.prepare s q c).atoms ↔
    Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model assignment s.atoms ∧
      Yulang.Common.Subtype (Prod.fst.{0, 0} (assignment q.lower)) (Yulang.CommonSyntax.Layer.base.{0, 0} c.head) ∧
        Yulang.Common.Subtype (Yulang.CommonSyntax.Layer.base.{0, 0} c.head) (Prod.fst.{0, 0} (assignment q.upper))
@Yulang.CommonRoleIntervalCandidateFrontier.accepts_exact : ∀ {n : Nat}
  (s : Yulang.CommonRoleSettledConstraints.State n) (q : Yulang.CommonRoleIntervalCandidateFrontier.Request n)
  (c : Yulang.CommonRoleCandidateStateFrontier.Candidate),
  Eq.{1} (Yulang.CommonRoleIntervalCandidateFrontier.accepts s q c) true ↔
    Yulang.CommonRoleIntervalCandidateFrontier.Fits s q c
@Yulang.CommonRoleIntervalCandidateFrontier.collect_exact : ∀ {n : Nat}
  (s : Yulang.CommonRoleSettledConstraints.State n) (q : Yulang.CommonRoleIntervalCandidateFrontier.Request n)
  (visible : List.{0} Yulang.CommonRoleCandidateStateFrontier.Candidate)
  (c : Yulang.CommonRoleCandidateStateFrontier.Candidate),
  Membership.mem.{0, 0} (Yulang.CommonRoleIntervalCandidateFrontier.collect s q visible) c ↔
    Membership.mem.{0, 0} visible c ∧ Yulang.CommonRoleIntervalCandidateFrontier.Fits s q c
@Yulang.CommonRoleIntervalCandidateFrontier.collect_antitone : ∀ {n : Nat}
  (before after : Yulang.CommonRoleSettledConstraints.State n)
  (q : Yulang.CommonRoleIntervalCandidateFrontier.Request n)
  (visible : List.{0} Yulang.CommonRoleCandidateStateFrontier.Candidate),
  (∀ (assignment : Fin n → Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model),
      Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model assignment after.atoms →
        Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model assignment before.atoms) →
    ∀ (c : Yulang.CommonRoleCandidateStateFrontier.Candidate),
      Membership.mem.{0, 0} (Yulang.CommonRoleIntervalCandidateFrontier.collect after q visible) c →
        Membership.mem.{0, 0} (Yulang.CommonRoleIntervalCandidateFrontier.collect before q visible) c
@Yulang.CommonRoleIntervalCandidateFrontier.same_slot_exact : ∀ {n : Nat}
  (s : Yulang.CommonRoleSettledConstraints.State n) (slot : Fin n)
  (c : Yulang.CommonRoleCandidateStateFrontier.Candidate),
  Yulang.CommonRoleIntervalCandidateFrontier.Fits s { lower := slot, upper := slot } c ↔
    Yulang.CommonRoleCandidateStateFrontier.Fits s slot c
@Yulang.CommonRoleIntervalCandidateFrontier.solutions_exact : ∀ {n : Nat}
  (s : Yulang.CommonRoleSettledConstraints.State n) (q : Yulang.CommonRoleIntervalCandidateFrontier.Request n)
  (c : Yulang.CommonRoleCandidateStateFrontier.Candidate)
  (assignment : Fin n → Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model),
  Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model assignment s.atoms ∧
      Yulang.Common.Subtype (Prod.fst.{0, 0} (assignment q.lower)) (Yulang.CommonSyntax.Layer.base.{0, 0} c.head) ∧
        Yulang.Common.Subtype (Yulang.CommonSyntax.Layer.base.{0, 0} c.head) (Prod.fst.{0, 0} (assignment q.upper)) ↔
    Exists.{1} fun scheme =>
      Membership.mem.{0, 0} (Yulang.CommonRoleIntervalCandidateFrontier.solutions s q c) scheme ∧
        Exists.{1} fun rows =>
          Exists.{1} fun parameters =>
            Yulang.CommonDeclaredNominalSourceFamily.AssignmentEquivalent (scheme.instantiate rows parameters)
              assignment
Yulang.CommonRoleIntervalCandidateFrontier.source_bounds_preserved : ∀
  (requests : List.{0} Yulang.CommonRoleOpenDescent.Request) (index : Fin (List.length.{0} requests))
  (interpret : Yulang.CommonRoleSettledSyntax.Ty → Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model)
  (s :
    Yulang.CommonRoleSettledConstraints.State
      (HMul.hMul.{0, 0, 0} 2 (List.length.{0} (Yulang.CommonRoleEndpointSlots.collect requests))))
  (c : Yulang.CommonRoleCandidateStateFrontier.Candidate),
  Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model
      (Yulang.CommonRoleEndpointSlots.assignment.{1} (Yulang.CommonRoleEndpointSlots.collect requests) interpret)
      (Yulang.CommonRoleIntervalCandidateFrontier.prepare s
          (Yulang.CommonRoleIntervalCandidateFrontier.fromSource requests index) c).atoms ↔
    Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model
        (Yulang.CommonRoleEndpointSlots.assignment.{1} (Yulang.CommonRoleEndpointSlots.collect requests) interpret)
        s.atoms ∧
      Yulang.Common.Subtype (Prod.fst.{0, 0} (interpret (getElem.{0, 0, 0} requests ↑index ⋯).lower))
          (Yulang.CommonSyntax.Layer.base.{0, 0} c.head) ∧
        Yulang.Common.Subtype (Yulang.CommonSyntax.Layer.base.{0, 0} c.head)
          (Prod.fst.{0, 0} (interpret (getElem.{0, 0, 0} requests ↑index ⋯).upper))
```
