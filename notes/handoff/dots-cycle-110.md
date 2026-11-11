# dots cycle 110 — 構造ordinaryとassociated式の有限共同飽和

## 結論・時間

開始は2026-11-11T05:23:09Z。約49分でコードの最終公開を完了し、その後は最終照合・報告。正確な終了時刻と経過時間はcompleted heartbeatに記録する。親の絶対期限06:22:19Zを優先する。
新規6モジュール、1,174行、公開定理63本。**有限な静的associated occurrenceを含む実driverの健全性・完全性と停止、任意の完全な実行順序の結果一致、元の名前つき入力からのordinary solver入口まで閉じた。一般B4/T1cは未完。主型性は未証明。**

小さな目標で終了せず、共同閉包→実solverとreplay→任意順序→名前つきsource入口へ継続した。新しい意味論判断0件、質問ノート0件。既存のinvocation lifetimeの判断待ちは再質問せず、依存しない断片で進めた。

## 復旧・指示・公開

最初にfresh integrationのstanding ordersとinbox（末尾I-15まで）を読み、ACTIVEでSTOPなしを確認。出発点integration/publicationはともに361c8b0f685cdbed2baaed937525315df2bba4a1。cycle109のcompleted heartbeatと報告が存在し、作業木と公開treeも一致。復旧すべき未公開コードなし。同時writerなし。spec・plan・lake設定・既存証明モジュールは変更しなかった。

設計ノートをコードより先に作成。関連Y2監査を読み、一般source意味論の未決定部分を引き受けずに下記断片を実装した。

公開は全てGitHubアプリのblob/tree/commit APIまたはheartbeat用contents API。expected-headを確認しnonforce更新。書込先はwork/dots-mainのみ。git pushなし。各コードblobをlocal SHAと照合し、各checkpointを明示refspecでfetchして比較した。

- 05:33:16Z: 46a54d41342608c16a9aa8afde10d448b910b14e — 混合Horn/associated閉包。
- 05:39:40Z: b17af93664ea32bc84d42770bf164cf839165534 — 実solverとcausal replay。
- 05:47:30Z: f2ec6a44f0216b53612380042ef9090ad19b9969 — 任意の完全な実行順序。開始25分以内の中間公開も達成。
- 06:00:24Z: a988791aee283de8caa3b2171de02ea0f62f79d0 — compact source allocationとraw入口。
- 06:04:47Z: 05015b8eec082810aef0c5527ede16863be31388 — 最終全診断木、挿入数、multisetの順序独立。
- **06:12:00Z: a9fc9b15a06d662670bda853fdeb630f56bd65ca — 最終コード。** treeは3458925c4da236f2ceea3eba4f4fe082ebb17ed5。

06:15のfresh fetch時、integrationは依然361c8b0f685cdbed2baaed937525315df2bba4a1。最終コードとlocal treeのgit diffはexit 0、通常mergeで履歴を接続。最後の公開はこの報告とcompleted heartbeatのみ。出発点から異なる公開pathは計14（Lean6、接続3、設計ノート3、heartbeat、報告）。
開始/10/20/30/40分heartbeatを別に公開した。**50分heartbeatは06:15:50Z（52.7分）となり、2.7分遅延した。** コードは06:12に公開済みで、検証済み成果の未保存はなかった。次回は報告準備中も時刻確認を優先する。

## 数学的な範囲とM1のどの側に効くか

以下は全て任意の有限入力についての定理。特定の回帰例だけを証明したものではない。完全な量化子と仮定を含む63本の定理型は末尾に原文で再掲する。

### 1. CommonRoleStructuralHornClosure（12本）— 補助、有限規則の健全性・完全性

任意n、任意の有限ordinary atom seed列、任意の有限Horn clause列について、seed・実構造split・transitivity・全premise成立時のclauseという独立Derivesを定義した。clauseのpremiseとconclusionも含む有限carrierを内側で計算し、実saturateのmembership iff Derives。停止時の閉包、重複なし、挿入数≤計算carrier長、冪等性、cutを証明。全モデルの契約は「seedを満たし、独立Derivesで発火する各clause conclusionを満たす」こととのiff。任意の意味的entailment全体への完全性ではない。

generated_execution_completeは実firstFreshが選んだ順序を逆向きtraceから戻し、各更新がその時点までに既知のpremiseだけで可能だったことを保証する。外部の完成trace・closed証明・有限宇宙の列挙をcallerに要求しない。run_closedには実seen⊆computed universeという内部補題の前提がある。

### 2. CommonRoleStructuralAssociatedClosure（6本）— 健全性・有限宣言規則内の完全性

任意の既存AssocEnv/RoleDecls、Core WellFormedとAssocWellFormed、任意n/seed/有限occurrence列について、実際のassociated value宣言から4種類のbase receiverごとのHorn clauseを計算する。receiverの上下両boundがそろって初めてoutputの上下boundを追加する。独立Derivesのassociated規則はDeclarativeComputedを使い、resolverの結果で定義しない。

clauses_exact/derives_exact/saturate_exactは宣言、独立導出、実計算の三者のiff。models_exactは全モデルの保存と正確な絞り込み。derives_congr/saturate_congrはseed/occurrenceのmembershipが等しい列の順序・重複に依存しないことを示す。

制限は既存scalar decoderが受け付けるint/str RHSの有限fragment。任意の構造RHSや、新しいchild occurrenceの生成まで閉じたとは言わない。実装fragmentの制限であり、新しい言語上の拒否規則ではない。

### 3. CommonRoleStructuralAssociatedSolver（5本）— ordinary実行の健全性・完全性

同じWF条件と任意の既存checked Stateについて、共同閉包中で上下両boundを持つscalar factを列挙し、実ordinary Stateへemitする。completeState_modelsは結果Stateの全モデルが独立共同導出の全モデルと等しいことを証明。solver_exactは実ordinary solver成功 iff その全制約集合が充足可能。初期Stateの整合性だけでは十分でなく、associated feedbackによる最終矛盾を実際に拒否する。completeState_stableは同じ入力群で再起動した際の安定性。role選択成功や主型性は結論にない。

### 4. CommonRoleStructuralAssociatedReplay（7本）— 補助、実行保存の健全性・完全性

任意env/roles/WF/AssocWF、有限occurrences、初期Stateと、既存registry/slots/Sources/元Goalについて、内部生成した因果的traceの各累積snapshotをreplayする。返却runについて最終Stateのモデルを前提とすると、全先行snapshotにもそのモデルがある。逆向きは一般に成り立たない。associated式は新しい制約を増やすためである。

run_exact/runGraphs_exactは完全な診断木（失敗branchとchildを含む）を保存し、木を再利用するplateauでもordinary graphは毎回生成する。snapshot数≤1+computed carrier長、木のrebuild≤1+2*元Goal内の変数occurrence数、visit≤そのrebuild上限*computed work domain長。final_graph_models_exactは全モデルに対する最終graphの同値で、代表モデルや候補の選択ではない。

### 5. CommonRoleStructuralHornSchedules（16本）— 補助、有限飽和の完全性・順序独立

任意n/seed/clauseに対し、seed/split/trans/clauseの独立Stepと、新factだけを挿入するExecutionを定義する。全有限実行はsound、重複なし、computed carrier長以内。任意の**closedな最終状態まで進んだ**実行について、membership iff独立Derives。途中で止めた任意prefixに完全性は主張しない。

同じseed/clauseからの2つの完全実行の最終membership、全モデル、materialized syntax、multiset、挿入数は一致する。固定registry/slots/Sources/元Goalなら、完全な最終診断木が文字通り等しい。異なるregistryや任意の未来の新occurrence追加への定理ではない。実generated scheduleがこのExecutionでありclosedになることも証明し、外部のfairness仮定を実driverへ渡さない。

### 6. CommonRoleStructuralNamedInputs（17本）— source境界の補助、ordinary入口の健全性・完全性

任意のraw Atom Nat列と、既存のscope-checked structural Programから、全てのnested型/row内の名前とoccurrence endpointを集め、重複を除き、capacity=名前数+1を計算する。元の名前が巨大な自然数でもcapacityはmax名に依存しない。実際に現れる名前は別名と衝突せず、余分なdummy slotを使わない。capture-free renameとreadbackの全モデル同値を、型/rowの全構文に対して証明した。

Good/grammarは既存Stateの3つのordinary grammar条件をそのまま判定する。prepare_exactはGoodなら外部checked Stateを要求せず内側で構成することを示す。runは次元・slot map・State・carrier・batch・modelをcallerから受けず、実共同閉包とordinary solverを呼ぶ。

任意env/roles/CoreWF/AssocWF/srcについて、run_source_exists_iffは
「実run.isSome=true iff Good src ∧ ∃finite valuation, SourceModels env roles src valuation」。SourceModelsは元の名前つきordinary atomsと、独立にactivatedされたsource associated等式の全てを満たすこと。run_source_modelsは、返却された任意outputと任意valuationについて、outputの全モデル iff SourceModels。

**残る前提**: Program自体は既存のchecked template syntax、activationのKnownは計算したfinite index上の独立Derivesである。parserからのscope生成、任意の新child/source identity、全source Typing判断からの翻訳、裸のrole要求全体の選択・辞書は導いていない。Good不成立はこの既存ordinary fragmentの入口外という意味で、Yulang言語の新しい拒否仕様ではない。

## 検証・受け入れ条件

Lean 4.35.0。全コマンドは時間上限を設定し、長い実行はtool sessionで継続・pollした。最終の実行は全てexit 0。

- `lake build Yulang.CommonRoleStructuralNamedInputs --wfail`: 382 jobs成功。6新モジュールをimportする焦点target。全体buildではない。
- `lake env lean --trust=0 <suite>`: horn 9guard/2example、associated 29/5、named 31/4、schedule 3/5、stress 9/0、合計81guardと16kernel example。
- 最終public存在定理追加後にもNamedInputs焦点build、named suite、全63公開定理の#print axioms、scoped axiom gateを再実行して成功。全suite一括の後に変えた実行コードはなく、存在定理だけを追加した。
- `lake env lean --trust=0 final-axioms.lean`: 63本全て確認。許容する依存はpropext/Classical.choice/Quot.soundだけ。
- `lake env lean --trust=0 scoped-axiom-gate.lean`: 六新モジュールに属する273宣言全てで同allowlist成功。既存全プロジェクトへの監査ではない。
- `git diff --check`: 成功。`bash tools/verify-lean.sh . origin/integration/m1-final --no-build`: 下記全文の通りPASS。
- import/Audit登録の静的照合: 全63本登録。新importは最初の#printより前。
- 最終コードa9fc9b15へのGitHub statusはstatuses=[]、workflow APIはworkflow_runs=[]。後者はPR-triggered/先頭pageのみのwrapper。**CI成功とは報告しない。**

境界suiteは、構造splitがreceiverのpaired boundsを作り次のassociated式を発火する例、feedback2段とtrans、初期整合→最終矛盾、空seed/未発火、occurrence順序反転/重複、違う合法schedule、registry拒否、tree plateauでのgraph生成、巨大source名、nested arrow/row、幅条件不足、unsupported既存grammar、source readbackを含む。

追加stressは深さ8の実associated/ordinary連鎖を完走。cycleを含むsource graphでも、int seedでは有限閉包、str seedでは初期整合から最終矛盾拒否、seedなしでは発火せずordinary成功（role成功ではない）を確認。shell timeでreal9.997s。深さ16や全体性能の検証はしていない。

**禁止された全体lake build、全Audit、build付きverifyは実行していない。全体統合確認は監督役に残す。** focused上では新しい公理・holes・native_decideなし。propext等既存Lean公理は区別して明示している。

verify出力全文:

```text
verify-lean: . @ b32d2e23b (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

## Yulang2との照合・中断と制限

着手前にfresh work/dots-auditのnotes/audit/y2-claims-role-boundaries-cycle-2.mdを読み、ROLE-MORE001/002/003/005の記録と照合した。今回の関連式由来の絞り込みと順序独立は既存規則の範囲で実装し、Y2を意味論の権威にはしていない。新しいY2実機runは行っていない。source一般翻訳とdictionary観測同値は未照合・未証明。

途中のLean elaborationエラー（予約語、shadowing、Bool/Fin/list補題の組立て）は修正して再build。単純shell backgroundが継続しなかったためtool sessionへ切り替え、最終logを確認した。初回timing用/usr/bin/timeは未搭載（exit127）だったためshell builtin timeへ変更した。stressの最初のテストはcandidate列を[int]に限定して失敗したが、既存solverは初期boundとemit後の重複を保存し[int,int]を返すと確認したため、「nonemptyかつ全要素int」に修正した。実装の意味は変えていない。

大きい既存ファイルのtool出力が切れた際は、GitHub baseとlocal差分から再構築しblob SHA一致後にのみrefを更新した。最終公開の出力も切れたが、SHAとremoteを取得して成功を確定した。結果不明の書込みを盲目的に再試行していない。最終空きdisk約43GiB、quota残量は取得不能で未知。

## 未完・次の候補

B4の主要橋は5本全て未完:
- source_boundary_adequate
- generated_work_closed
- saturate_terminates_and_closes
- saturated_frontier_exact
- resolve_dictionary_order_sound

今回の定理は静的有限occurrence断片で上記の一部条件を内側へ移したもので、同名の一般橋を完成したことにはならない。一般構造RHS、動的に生成したchild occurrenceと新source名、K2、pending/selected/ambiguous/rejected、全モデルでのdictionary整合性と観測同値、M1の主型性は残る。X13〜X16を外側入口でPROVEDへ変更していない。

次の候補（意味論を先に決めない）:
1. generated_work_closedのため、scope-checked Programから新child occurrenceを生成する際の有限name/occurrence領域を証明し、既存checked境界を内側へ移す。
2. scalar associated decoderを一般構造RHSへ拡張する前に、finite carrierが実RHSと新childまで閉じる条件を独立に定義・証明する。
3. source_boundary_adequateの独立source judgmentとSourceModelsの間の翻訳を、既存invocation identity判断を侵さない断片で定める。

## 63本の正確な定理型

前節の日本語説明はこの型を省略・弱化しない。namespaceは各見出し。証明本体は対応する新モジュール参照。

### CommonRoleStructuralHornClosure（12本）

```lean
theorem derives_coverage {seeds : List (Atom (Fin n))} {clauses : List (Clause n)} {a}
    (h : Derives seeds clauses a) : a ∈ carrierAtoms seeds clauses

theorem run_closed [DecidableEq α] (rs : List (FiniteHorn.Rule α)) (u : List α)
    (capacity : Nat) (seen : List α) (distinct : seen.Nodup)
    (covered : ∀ a ∈ seen, a ∈ u) (enough : u.length ≤ seen.length + capacity) :
    ∀ a ∈ u, FiniteHorn.Enabled rs (FiniteHorn.run rs u capacity seen) a →
      a ∈ FiniteHorn.run rs u capacity seen

theorem saturate_closed (seeds : List (Atom (Fin n))) (clauses : List (Clause n))
    (a : Atom (Fin n)) (covered : a ∈ carrierAtoms seeds clauses)
    (enabled : FiniteHorn.Enabled (rules seeds clauses) (saturate seeds clauses) a) :
    a ∈ saturate seeds clauses

theorem saturate_exact (seeds : List (Atom (Fin n))) (clauses : List (Clause n)) (a) :
    a ∈ saturate seeds clauses ↔ Derives seeds clauses a

theorem stopped (seeds : List (Atom (Fin n))) (clauses : List (Clause n)) :
    FiniteHorn.firstFresh (rules seeds clauses) (saturate seeds clauses) (carrierAtoms seeds clauses) = none

theorem saturate_nodup (seeds : List (Atom (Fin n))) (clauses : List (Clause n)) :
    (saturate seeds clauses).Nodup

theorem saturate_bounded (seeds : List (Atom (Fin n))) (clauses : List (Clause n)) :
    (saturate seeds clauses).length ≤ (carrierAtoms seeds clauses).length

theorem models_exact (seeds : List (Atom (Fin n))) (clauses : List (Clause n))
    (v : Fin n → Comp Common.model) :
    All Common.model v (saturate seeds clauses) ↔ All Common.model v seeds ∧
      ∀ r ∈ clauses, (∀ a ∈ r.premises, Derives seeds clauses a) → r.conclusion.Holds Common.model v

theorem derives_cut {seeds more : List (Atom (Fin n))} {clauses : List (Clause n)} {a}
    (initial : ∀ b ∈ more, Derives seeds clauses b) (h : Derives more clauses a) :
    Derives seeds clauses a

theorem saturate_idempotent (seeds : List (Atom (Fin n))) (clauses : List (Clause n)) (a) :
    a ∈ saturate (saturate seeds clauses) clauses ↔ a ∈ saturate seeds clauses

theorem generated_reverse (seeds : List (Atom (Fin n))) (clauses : List (Clause n)) :
    (generated seeds clauses).reverse = saturate seeds clauses

theorem generated_execution_complete (seeds : List (Atom (Fin n))) (clauses : List (Clause n)) :
    CommonRoleStructuralSaturationTrace.Execution (rules seeds clauses) [] (generated seeds clauses) ∧
      FiniteHorn.firstFresh (rules seeds clauses) (generated seeds clauses).reverse (carrierAtoms seeds clauses) = none
```

### CommonRoleStructuralAssociatedClosure（6本）

```lean
theorem clauses_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (occurrences : List (Occurrence n)) (r : Clause n) :
    r ∈ clauses env roles wf occurrences ↔ ∃ q ∈ occurrences, ∃ head output a,
      DeclarativeComputed env roles (request q head) output ∧ a ∈ equality q.output output ∧
      r = ⟨equality q.receiver head,a⟩

theorem derives_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (occurrences : List (Occurrence n)) (seeds : List (Atom (Fin n))) (a) :
    CommonRoleStructuralHornClosure.Derives seeds (clauses env roles wf occurrences) a ↔
      Derives env roles occurrences seeds a

theorem saturate_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (occurrences : List (Occurrence n)) (seeds : List (Atom (Fin n))) (a) :
    a ∈ saturate env roles wf occurrences seeds ↔ Derives env roles occurrences seeds a

theorem models_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (occurrences : List (Occurrence n)) (seeds : List (Atom (Fin n)))
    (v : Fin n → Comp Common.model) :
    All Common.model v (saturate env roles wf occurrences seeds) ↔ All Common.model v seeds ∧
      ∀ q ∈ occurrences, ∀ head output,
        (∀ premise ∈ equality q.receiver head, Derives env roles occurrences seeds premise) →
        DeclarativeComputed env roles (request q head) output →
        All Common.model v (equality q.output output)

theorem derives_congr (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (left right : List (Occurrence n)) (seeds more : List (Atom (Fin n)))
    (source : ∀ q, q ∈ left ↔ q ∈ right) (initial : ∀ a, a ∈ seeds ↔ a ∈ more) (a) :
    Derives env roles left seeds a ↔ Derives env roles right more a

theorem saturate_congr (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (left right : List (Occurrence n)) (seeds more : List (Atom (Fin n)))
    (source : ∀ q, q ∈ left ↔ q ∈ right) (initial : ∀ a, a ∈ seeds ↔ a ∈ more) (a) :
    a ∈ saturate env roles wf left seeds ↔ a ∈ saturate env roles wf right more
```

### CommonRoleStructuralAssociatedSolver（5本）

```lean
theorem equality_models (slot : Fin n) (head : Inference.Base) (v : Fin n → Comp Common.model) :
    All Common.model v (equality slot head) ↔ Common.Equivalent (v slot).1 (.base head)

theorem knownFacts_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (occurrences : List (Occurrence n)) (seeds : List (Atom (Fin n))) (f : Fact n) :
    f ∈ knownFacts env roles wf occurrences seeds ↔
      ∀ a ∈ equality f.1 f.2, Derives env roles occurrences seeds a

theorem completeState_models (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (occurrences : List (Occurrence n)) (initial : State n) (v : Fin n → Comp Common.model) :
    All Common.model v (completeState env roles wf occurrences initial).atoms ↔
      All Common.model v (saturate env roles wf occurrences initial.atoms)

theorem solver_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (occurrences : List (Occurrence n)) (initial : State n) :
    CommonRoleOpenPropagation.consistent (completeState env roles wf occurrences initial) = true ↔
      ∃ v : Fin n → Comp Common.model, ∀ a, Derives env roles occurrences initial.atoms a →
        a.Holds Common.model v

theorem completeState_stable (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (occurrences : List (Occurrence n)) (initial : State n) (a) :
    Derives env roles occurrences (completeState env roles wf occurrences initial).atoms a ↔
      Derives env roles occurrences initial.atoms a
```

### CommonRoleStructuralAssociatedReplay（7本）

```lean
theorem final_membership (awf : Roles.AssocWellFormed env roles)
    (occurrences : List (Occurrence n)) (seeds : List (Atom (Fin n))) (a) :
    a ∈ finalAtoms env roles wf occurrences seeds ↔ Derives env roles occurrences seeds a

theorem final_models (awf : Roles.AssocWellFormed env roles)
    (occurrences : List (Occurrence n)) (initial : State n) (v : Fin n → Comp Common.model) :
    All Common.model v (finalAtoms env roles wf occurrences initial.atoms) ↔
      All Common.model v (completeState env roles wf occurrences initial).atoms

theorem final_models_snapshot (awf : Roles.AssocWellFormed env roles)
    (occurrences : List (Occurrence n)) (initial : State n) (v : Fin n → Comp Common.model)
    (models : All Common.model v (completeState env roles wf occurrences initial).atoms)
    (state : List (Atom (Fin n)))
    (present : state ∈ initial.atoms :: accumulate initial.atoms (generated env roles wf occurrences initial.atoms)) :
    All Common.model v state

theorem run_exact (awf : Roles.AssocWellFormed env roles)
    (occurrences : List (Occurrence n)) (registry : List Declaration)
    (slots : Nat → Fin n) (sources : Sources) (goal : Goal) (initial : State n) (output : Replay n) :
    run env roles wf occurrences registry slots sources goal initial = some output ↔
      (∃ v : Fin n → Comp Common.model, ∀ a, Derives env roles occurrences initial.atoms a →
        a.Holds Common.model v) ∧ ∃ checked : Checked registry,
        output = CommonRoleStructuralFrontierReplay.replay registry checked slots sources goal initial.atoms
          (accumulate initial.atoms (generated env roles wf occurrences initial.atoms))

theorem run_computed_bound (awf : Roles.AssocWellFormed env roles)
    (occurrences : List (Occurrence n)) (registry : List Declaration)
    (slots : Nat → Fin n) (sources : Sources) (goal : Goal) (initial : State n) (output : Replay n)
    (returned : run env roles wf occurrences registry slots sources goal initial = some output) :
    ∃ bound, CommonRoleStructuralMaterializationDomain.workDomain registry
        (finalAtoms env roles wf occurrences initial.atoms) slots goal = some bound ∧
      output.snapshots.length ≤ 1 + (CommonRoleStructuralHornClosure.carrierAtoms initial.atoms
        (clauses env roles wf occurrences)).length ∧
      output.rebuilds ≤ 1 + 2 * CommonRoleMaterializationProgress.potential goal ∧
      output.visits ≤ (1 + 2 * CommonRoleMaterializationProgress.potential goal) * bound.length ∧
      ∀ tree ∈ output.snapshots, ∀ target ∈ CommonRoleFrontierReachability.goals tree, target ∈ bound

theorem runGraphs_exact (occurrences : List (Occurrence n)) (registry : List Declaration)
    (slots : Nat → Fin n) (sources : Sources) (goal : Goal) (initial : State n)
    (old : Nat → Plan (Fin n)) (output : Replay n)
    (returned : run env roles wf occurrences registry slots sources goal initial = some output) :
    ∃ graphs, runGraphs env roles wf occurrences registry slots sources goal initial old = some (output,graphs) ∧
      graphs.map some = (initial.atoms :: accumulate initial.atoms
        (generated env roles wf occurrences initial.atoms)).mapIdx
          (fun i atoms => CommonRoleStructuralOrdinaryMaterialization.run registry slots sources atoms (old i) goal)

theorem final_graph_models_exact (awf : Roles.AssocWellFormed env roles)
    (occurrences : List (Occurrence n)) (registry : List Declaration)
    (slots : Nat → Fin n) (sources : Sources) (goal : Goal) (initial : State n)
    (old : Plan (Fin n)) (v : Fin n → Comp Common.model) :
    (∃ output, CommonRoleStructuralOrdinaryMaterialization.run registry slots sources
        (finalAtoms env roles wf occurrences initial.atoms) old goal = some output ∧
      CommonRoleFrontierGraphs.Represents output.2 v) ↔
      Checked registry ∧ (∀ a, Derives env roles occurrences initial.atoms a → a.Holds Common.model v) ∧
        ∃ sourceValues, CommonRoleCaptureBatchModels.SharedFits v sourceValues old ∧
          CommonRoleGuardedIntervalPlans.Derives registry slots sources v sourceValues
            (CommonRoleStructuralOrdinaryMaterialization.materializeGoal
              (finalAtoms env roles wf occurrences initial.atoms) slots goal)
```

### CommonRoleStructuralHornSchedules（16本）

```lean
theorem step_sound {seeds : List (Atom (Fin n))} {clauses : List (Clause n)} {seen a}
    (known : ∀ b ∈ seen, Derives seeds clauses b) (step : Step seeds clauses seen a) :
    Derives seeds clauses a

theorem execution_sound {seeds : List (Atom (Fin n))} {clauses : List (Clause n)} {seen trace}
    (run : Execution seeds clauses seen trace) (known : ∀ a ∈ seen, Derives seeds clauses a) :
    ∀ a ∈ finish seen trace, Derives seeds clauses a

theorem execution_nodup {seeds : List (Atom (Fin n))} {clauses : List (Clause n)} {seen trace}
    (run : Execution seeds clauses seen trace) (distinct : seen.Nodup) : (finish seen trace).Nodup

theorem execution_bounded {seeds : List (Atom (Fin n))} {clauses : List (Clause n)} {seen trace}
    (run : Execution seeds clauses seen trace) (distinct : seen.Nodup)
    (known : ∀ a ∈ seen, Derives seeds clauses a) :
    trace.length + seen.length ≤ (carrierAtoms seeds clauses).length

theorem closed_complete {seeds : List (Atom (Fin n))} {clauses : List (Clause n)} {seen a}
    (closed : Closed seeds clauses seen) (derived : Derives seeds clauses a) : a ∈ seen

theorem execution_exact {seeds : List (Atom (Fin n))} {clauses : List (Clause n)} {trace}
    (run : Execution seeds clauses [] trace) (closed : Closed seeds clauses (finish [] trace)) (a) :
    a ∈ finish [] trace ↔ Derives seeds clauses a

theorem schedules_confluent {seeds : List (Atom (Fin n))} {clauses : List (Clause n)} {left right}
    (lrun : Execution seeds clauses [] left) (lclosed : Closed seeds clauses (finish [] left))
    (rrun : Execution seeds clauses [] right) (rclosed : Closed seeds clauses (finish [] right)) (a) :
    a ∈ finish [] left ↔ a ∈ finish [] right

theorem enabled_step (seeds : List (Atom (Fin n))) (clauses : List (Clause n)) (seen : List (Atom (Fin n)))
    (a : Atom (Fin n)) (enabled : FiniteHorn.Enabled (CommonRoleStructuralHornClosure.rules seeds clauses) seen a) :
    Step seeds clauses seen a

theorem generated_execution (seeds : List (Atom (Fin n))) (clauses : List (Clause n)) :
    Execution seeds clauses [] (generated seeds clauses)

theorem saturated_closed (seeds : List (Atom (Fin n))) (clauses : List (Clause n)) :
    Closed seeds clauses (saturate seeds clauses)

theorem generated_complete (seeds : List (Atom (Fin n))) (clauses : List (Clause n)) :
    Execution seeds clauses [] (generated seeds clauses) ∧
      Closed seeds clauses (finish [] (generated seeds clauses)) ∧
      (generated seeds clauses).length ≤ (carrierAtoms seeds clauses).length

theorem schedule_models {seeds : List (Atom (Fin n))} {clauses : List (Clause n)} {trace}
    (run : Execution seeds clauses [] trace) (closed : Closed seeds clauses (finish [] trace))
    (v : Fin n → Comp Common.model) :
    All Common.model v (finish [] trace) ↔ All Common.model v (saturate seeds clauses)

theorem schedule_materialize {seeds : List (Atom (Fin n))} {clauses : List (Clause n)} {trace}
    (run : Execution seeds clauses [] trace) (closed : Closed seeds clauses (finish [] trace))
    (slots : Nat → Fin n) (form : CommonRoleCaptureNormalization.Form) :
    CommonRoleStructuralOrdinaryMaterialization.materialize (finish [] trace) slots form =
      CommonRoleStructuralOrdinaryMaterialization.materialize (saturate seeds clauses) slots form

theorem schedules_perm {seeds : List (Atom (Fin n))} {clauses : List (Clause n)} {left right}
    (lrun : Execution seeds clauses [] left) (lclosed : Closed seeds clauses (finish [] left))
    (rrun : Execution seeds clauses [] right) (rclosed : Closed seeds clauses (finish [] right)) :
    (finish [] left).Perm (finish [] right)

theorem schedules_length {seeds : List (Atom (Fin n))} {clauses : List (Clause n)} {left right}
    (lrun : Execution seeds clauses [] left) (lclosed : Closed seeds clauses (finish [] left))
    (rrun : Execution seeds clauses [] right) (rclosed : Closed seeds clauses (finish [] right)) :
    left.length = right.length

theorem schedule_tree {seeds : List (Atom (Fin n))} {clauses : List (Clause n)} {trace}
    (run : Execution seeds clauses [] trace) (closed : Closed seeds clauses (finish [] trace))
    (registry : List CommonRoleStablePaterson.Declaration) (checked : CommonRoleIntervalWorkClosure.Checked registry)
    (slots : Nat → Fin n) (sources : CommonRoleGuardedIntervalPlans.Sources) (goal : CommonRoleIntervalPaterson.Goal) :
    CommonRoleGuardedIntervalFrontier.build registry checked slots sources
      (CommonRoleStructuralOrdinaryMaterialization.materializeGoal (finish [] trace) slots goal) =
    CommonRoleGuardedIntervalFrontier.build registry checked slots sources
      (CommonRoleStructuralOrdinaryMaterialization.materializeGoal (saturate seeds clauses) slots goal)
```

### CommonRoleStructuralNamedInputs（17本）

```lean
theorem slot_present (src : Source) (name : Nat) (present : name ∈ names src) :
    (slot src name).val < (names src).length

theorem read_slot (src : Source) (name : Nat) (present : name ∈ names src) :
    readName src (slot src name) = name

theorem slot_injective (src : Source) (a b : Nat) (ha : a ∈ names src) (hb : b ∈ names src) :
    slot src a = slot src b ↔ a = b

theorem atom_names_present (src : Source) (a : Atom Nat) (member : a ∈ src.atoms)
    (name : Nat) (present : name ∈ atomNames a) : name ∈ names src

theorem occurrence_names_present (src : Source) (q : CommonRoleStructuralAssociatedTemplates.Occurrence)
    (member : q ∈ src.program) : q.receiver ∈ names src ∧ q.output ∈ names src

theorem row_eval_congr (t : RowTerm Nat) (v w : Nat → Comp Common.model)
    (same : ∀ a ∈ rowNames t, v a = w a) : t.eval Common.model v = t.eval Common.model w

theorem ty_eval_congr (t : TyTerm Nat) (v w : Nat → Comp Common.model)
    (same : ∀ a ∈ tyNames t, v a = w a) : t.eval Common.model v = t.eval Common.model w

theorem atom_holds_congr (a : Atom Nat) (v w : Nat → Comp Common.model)
    (same : ∀ name ∈ atomNames a, v name = w name) :
    a.Holds Common.model v ↔ a.Holds Common.model w

theorem allocated_models (src : Source) (v : Nat → Comp Common.model) :
    All Common.model (v ∘ readName src) (atoms src) ↔ All Common.model v src.atoms

theorem source_models (src : Source) (v : Fin (capacity src) → Comp Common.model) :
    All Common.model v (atoms src) ↔ All Common.model (v ∘ slot src) src.atoms

theorem grammar_exact (src : Source) : grammar src = true ↔ Good src

theorem prepare_exact (src : Source) (s : State (capacity src)) :
    prepare src = some s ↔ Good src ∧ s.atoms = atoms src

theorem run_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (wf : Roles.WellFormed env.cores)
    (awf : Roles.AssocWellFormed env roles) (src : Source) :
    (run env roles wf src).isSome = true ↔ Good src ∧
      ∃ v : Fin (capacity src) → Comp Common.model, ∀ a,
        CommonRoleStructuralAssociatedClosure.Derives env roles (occurrences src) (atoms src) a →
          a.Holds Common.model v

theorem occurrence_step (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (src : Source)
    (q : CommonRoleStructuralAssociatedTemplates.Occurrence) (head result : Inference.Base) :
    CommonRoleAssociatedDeclarationExact.DeclarativeComputed env roles
      (CommonRoleFiniteAssociatedClosure.request (occurrence src q) head) result ↔
      CommonRoleStructuralAssociatedTemplates.Step env roles q head result

theorem complete_source_models (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (src : Source) (initial : State (capacity src)) (prepared : prepare src = some initial)
    (v : Fin (capacity src) → Comp Common.model) :
    All Common.model v (CommonRoleStructuralAssociatedSolver.completeState env roles wf
      (occurrences src) initial).atoms ↔ SourceModels env roles src v

theorem run_source_models (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (src : Source) (output : State (capacity src)) (returned : run env roles wf src = some output)
    (v : Fin (capacity src) → Comp Common.model) :
    All Common.model v output.atoms ↔ SourceModels env roles src v

theorem run_source_exists_iff (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles) (src : Source) :
    (run env roles wf src).isSome = true ↔ Good src ∧
      ∃ v : Fin (capacity src) → Comp Common.model, SourceModels env roles src v
```

## 再現用検証入力

以下をleanディレクトリから各々lake env lean --trust=0で実行。既存ファイルを変更しない。

### horn-boundary.lean

```lean
import Yulang.CommonRoleStructuralAssociatedClosure
open Yulang PresenceNormalForm Core.PresenceGeneration
open CommonRoleStructuralHornClosure
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
namespace HornBoundary
abbrev A := Atom (Fin 2)
def x : TyTerm (Fin 2) := .var 0
def y : TyTerm (Fin 2) := .var 1
def i : TyTerm (Fin 2) := .base .int
def s : TyTerm (Fin 2) := .base .str
def seeds : List A := [.tyLe (.pair x y) (.pair i s),.tyLe (.pair i s) (.pair x y)]
def clause : Clause 2 := ⟨[.tyLe x i,.tyLe i x],.tyLe y i⟩
#guard (saturate seeds []).contains (.tyLe x i)
#guard (saturate seeds []).contains (.tyLe i x)
#guard (saturate seeds []).contains (.tyLe y s)
#guard !(saturate seeds []).contains (.tyLe y i)
#guard (saturate seeds [clause]).contains (.tyLe y i)
#guard (saturate [] [clause]).isEmpty
#guard (saturate ([] : List A) []).isEmpty
#guard (generated seeds [clause]).reverse = saturate seeds [clause]
#guard (saturate seeds [clause]).length ≤ (carrierAtoms seeds [clause]).length
example : Derives seeds [clause] (.tyLe y i) := by
  apply Derives.clause clause (by simp)
  intro a ha
  simp only [clause,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl | rfl
  · exact .split (.tyLe (.pair x y) (.pair i s)) _ (.seed _ (by simp [seeds])) (by decide +kernel)
  · exact .split (.tyLe (.pair i s) (.pair x y)) _ (.seed _ (by simp [seeds])) (by decide +kernel)
example (a : A) : a ∈ saturate (saturate seeds [clause]) [clause] ↔ a ∈ saturate seeds [clause] :=
  saturate_idempotent ..
end HornBoundary

```

### associated-boundary.lean

```lean
import Yulang.CommonRoleStructuralAssociatedReplay
open Yulang PresenceNormalForm Core.PresenceGeneration
open CommonRoleStructuralAssociatedClosure
open CommonRoleStructuralAssociatedSolver
open CommonRoleCandidateStateFrontier (equality)
set_option maxRecDepth 16384
set_option maxHeartbeats 32000000
namespace AssociatedBoundary

def decl : Roles.Impl := ⟨80,[.var 0],[],800⟩
def annotated : Roles.AssocImpl := ⟨decl,[(0,.app 0 [])],by decide⟩
def env := Roles.AssocExamples.singletonEnv annotated
def signature : Roles.RoleDecl where
  arity := 1
  assoc := fun name => if name = 0 then some none else none
  defaultsScoped := by intro name rhs h; split at h <;> simp_all
def roles : Roles.RoleDecls := fun _ => signature
theorem wf : Roles.WellFormed env.cores := by
  simp [env,Roles.AssocExamples.singletonEnv,Roles.AssocEnv.cores,Roles.WellFormed,
    annotated,decl,Roles.Impl.WellFormed]
theorem awf : Roles.AssocWellFormed env roles := by
  intro i hi
  have same : i = annotated := by simpa [env,Roles.AssocExamples.singletonEnv] using hi
  subst i
  simp [Roles.AssocHeadVars,Roles.AssocComplete,Roles.AssocDeclared,annotated,decl,roles,
    signature,Roles.Term.occurrences,Roles.argsOccurrences]
def ty : Inference.Base → Roles.Term
  | .int => .app 0 [] | .str => .app 1 [] | .bool => .app 2 [] | .unit => .app 3 []
def occ (receiver output : Fin 4) : CommonRoleFiniteAssociatedClosure.Occurrence 4 :=
  ⟨receiver,output,0,fun head => ⟨80,[ty head]⟩⟩
def occurrences := [occ 0 1,occ 2 3]
def x : TyTerm (Fin 4) := .var 0
def y : TyTerm (Fin 4) := .var 1
def z : TyTerm (Fin 4) := .var 2
def s : TyTerm (Fin 4) := .base .str
def seeds : List (Atom (Fin 4)) :=
  [.tyLe (.pair x y) (.pair s z),.tyLe (.pair s z) (.pair x y)]
def initial : CommonRoleSettledConstraints.State 4 where
  atoms := seeds
  child := by
    simp [PresenceGeneratedChildGrammar.GoodAtoms,PresenceGeneratedChildGrammar.GoodAtom,
      seeds,x,y,z,s,PresenceGeneratedChildGrammar.lower,PresenceGeneratedChildGrammar.upper]
  width := by
    intro a b h tail ht
    simp only [seeds,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with h | h <;> cases h <;> cases ht
  rows := by
    simp [PresenceSourceConstraintSupport.GoodAtoms,PresenceSourceConstraintSupport.GoodAtom,
      seeds,x,y,z,s,PresenceSourceConstraintSupport.simpleTyRows]
def result := saturate env roles wf occurrences seeds
#guard (clauses env roles wf occurrences).length = 16
#guard CommonRoleOrdinaryKnownness.candidates seeds 0 = []
#guard !(CommonRoleFiniteStructuralClosure.normalize seeds).contains (.tyLe (.var 3) (.base .int))
#guard result.contains (.tyLe (.var 0) (.base .str))
#guard result.contains (.tyLe (.base .str) (.var 0))
#guard result.contains (.tyLe (.var 1) (.base .int))
#guard result.contains (.tyLe (.base .int) (.var 1))
#guard result.contains (.tyLe (.var 2) (.base .int))
#guard result.contains (.tyLe (.base .int) (.var 2))
#guard result.contains (.tyLe (.var 3) (.base .int))
#guard result.contains (.tyLe (.base .int) (.var 3))
#guard (knownFacts env roles wf occurrences seeds).length = 4
#guard CommonRoleOpenPropagation.consistent initial
#guard CommonRoleOpenPropagation.consistent (completeState env roles wf occurrences initial)
#guard (saturate env roles wf occurrences []).isEmpty
#guard !(saturate env roles wf [occ 0 1] [.tyLe (.var 0) (.base .str)]).contains (.tyLe (.var 1) (.base .int))
#guard (saturate env roles wf occurrences.reverse seeds.reverse).all fun a => result.contains a
#guard result.all fun a => (saturate env roles wf occurrences.reverse seeds.reverse).contains a
#guard (saturate env roles wf (occurrences ++ occurrences) (seeds ++ seeds)).all fun a => result.contains a
#guard result.all fun a => (saturate env roles wf (occurrences ++ occurrences) (seeds ++ seeds)).contains a

def conflict := CommonRoleCandidateStateFrontier.extend initial 3 .str
#guard CommonRoleOpenPropagation.consistent conflict
#guard !(CommonRoleOpenPropagation.consistent (completeState env roles wf occurrences conflict))

def registry : List CommonRoleStablePaterson.Declaration := [⟨0,0,[.int],[]⟩]
def badRegistry : List CommonRoleStablePaterson.Declaration := [⟨0,0,[.var 0],[(0,[.var 0])]⟩]
def slots (_ : Nat) : Fin 4 := 3
def sources : CommonRoleGuardedIntervalPlans.Sources := fun _ _ x => x
def goal : CommonRoleIntervalPaterson.Goal := ⟨0,[(.var 0,.var 0)]⟩
def run := CommonRoleStructuralAssociatedReplay.run env roles wf occurrences registry slots sources goal initial
#guard run.isSome
#guard run.map CommonRoleStructuralFrontierReplay.Replay.rebuilds = some 2
#guard run.map (fun r => r.snapshots.length) = some
  (1+(CommonRoleStructuralAssociatedReplay.generated env roles wf occurrences seeds).length)
#guard (CommonRoleStructuralAssociatedReplay.run env roles wf occurrences registry slots sources goal conflict).isNone
#guard (CommonRoleStructuralAssociatedReplay.run env roles wf occurrences badRegistry slots sources goal initial).isNone
#guard (CommonRoleStructuralAssociatedReplay.run env roles wf [] registry slots sources goal initial).map
  CommonRoleStructuralFrontierReplay.Replay.rebuilds = some 1
#guard (CommonRoleStructuralAssociatedReplay.runGraphs env roles wf occurrences registry slots sources goal initial (fun _ => [])).isSome

example (a : Atom (Fin 4)) : a ∈ result ↔ Derives env roles occurrences seeds a :=
  saturate_exact env roles wf awf occurrences seeds a
example (v : Fin 4 → Comp Common.model) :
    All Common.model v (completeState env roles wf occurrences initial).atoms ↔ All Common.model v result :=
  completeState_models env roles wf awf occurrences initial v
example (a : Atom (Fin 4)) : Derives env roles occurrences (completeState env roles wf occurrences initial).atoms a ↔
    Derives env roles occurrences initial.atoms a := completeState_stable env roles wf awf occurrences initial a
example (a : Atom (Fin 4)) : a ∈ saturate env roles wf occurrences.reverse seeds.reverse ↔ a ∈ result :=
  saturate_congr env roles wf awf occurrences.reverse occurrences seeds.reverse seeds
    (by simp) (by simp) a
example : CommonRoleStructuralSaturationTrace.Execution
    (CommonRoleStructuralHornClosure.rules seeds (clauses env roles wf occurrences)) []
    (CommonRoleStructuralAssociatedReplay.generated env roles wf occurrences seeds) :=
  (CommonRoleStructuralHornClosure.generated_execution_complete seeds (clauses env roles wf occurrences)).1
end AssociatedBoundary

```

### schedule-boundary.lean

```lean
import Yulang.CommonRoleStructuralHornSchedules
open Yulang PresenceNormalForm Core.PresenceGeneration
open CommonRoleStructuralHornSchedules
open CommonRoleStructuralHornClosure (Clause)
set_option maxRecDepth 16384
namespace ScheduleBoundary
abbrev A := Atom (Fin 2)
def a : A := .rowLe (.var 0) (.var 1)
def b : A := .rowLe (.var 1) (.var 0)
def c : A := .rowLe (.var 0) (.var 0)
def seeds := [a,b]
def r : Clause 2 := ⟨[a,b],c⟩
def clauses := [r]
example : Execution seeds clauses [] [a,b,c] := by
  apply Execution.step a (by simp) (.seed a (by simp [seeds]))
  apply Execution.step b (by decide +kernel) (.seed b (by simp [seeds]))
  apply Execution.step c (by decide +kernel)
  · apply Step.clause r (by simp [clauses])
    intro x hx
    simpa [r,or_comm] using hx
  · exact .done _
example : Execution seeds clauses [] [b,a,c] := by
  apply Execution.step b (by simp) (.seed b (by simp [seeds]))
  apply Execution.step a (by decide +kernel) (.seed a (by simp [seeds]))
  apply Execution.step c (by decide +kernel)
  · apply Step.clause r (by simp [clauses])
    intro x hx
    simpa [r] using hx
  · exact .done _
theorem initial_step (x : A) (step : Step seeds clauses [] x) : x ∈ seeds := by
  cases step with
  | seed _ member => exact member
  | split _ _ member _ => cases member
  | trans _ _ _ member _ _ => cases member
  | clause rule member premises =>
    have same : rule = r := by simpa [clauses] using member
    subst rule
    exact False.elim (List.not_mem_nil (premises a (by simp [r])))
example : ¬ Execution seeds clauses [] [c] := by
  intro h
  cases h with
  | step _ _ step _ =>
    exact (show c ∉ seeds by decide +kernel) (initial_step c step)
#guard (CommonRoleStructuralHornClosure.generated seeds clauses).length = 3
#guard (CommonRoleStructuralHornClosure.saturate seeds clauses).length = 3
#guard (CommonRoleStructuralHornClosure.saturate seeds clauses).contains c
example (trace : List A) (run : Execution seeds clauses [] trace) : trace.length ≤
    (CommonRoleStructuralHornClosure.carrierAtoms seeds clauses).length := by
  simpa using execution_bounded run (by simp) (by simp)
example (left right : List A) (lrun : Execution seeds clauses [] left)
    (lclosed : Closed seeds clauses (finish [] left))
    (rrun : Execution seeds clauses [] right) (rclosed : Closed seeds clauses (finish [] right))
    (x : A) : x ∈ finish [] left ↔ x ∈ finish [] right := schedules_confluent lrun lclosed rrun rclosed x
end ScheduleBoundary

```

### named-boundary.lean

```lean
import Yulang.CommonRoleStructuralNamedInputs
open Yulang PresenceNormalForm Core.PresenceGeneration
set_option maxRecDepth 16384
set_option maxHeartbeats 32000000
namespace AssociatedBoundary

def decl : Roles.Impl := ⟨80,[.var 0],[],800⟩
def annotated : Roles.AssocImpl := ⟨decl,[(0,.app 0 [])],by decide⟩
def env := Roles.AssocExamples.singletonEnv annotated
def signature : Roles.RoleDecl where
  arity := 1
  assoc := fun name => if name = 0 then some none else none
  defaultsScoped := by intro name rhs h; split at h <;> simp_all
def roles : Roles.RoleDecls := fun _ => signature
theorem wf : Roles.WellFormed env.cores := by
  simp [env,Roles.AssocExamples.singletonEnv,Roles.AssocEnv.cores,Roles.WellFormed,
    annotated,decl,Roles.Impl.WellFormed]
theorem awf : Roles.AssocWellFormed env roles := by
  intro i hi
  have same : i = annotated := by simpa [env,Roles.AssocExamples.singletonEnv] using hi
  subst i
  simp [Roles.AssocHeadVars,Roles.AssocComplete,Roles.AssocDeclared,annotated,decl,roles,
    signature,Roles.Term.occurrences,Roles.argsOccurrences]
def ty : Inference.Base → Roles.Term
  | .int => .app 0 [] | .str => .app 1 [] | .bool => .app 2 [] | .unit => .app 3 []
def occ (receiver output : Fin 4) : CommonRoleFiniteAssociatedClosure.Occurrence 4 :=
  ⟨receiver,output,0,fun head => ⟨80,[ty head]⟩⟩
end AssociatedBoundary

namespace NamedBoundary
open CommonRoleStructuralNamedInputs
open AssociatedBoundary (env roles wf awf)
def template : CommonRoleStructuralAssociatedTemplates.Template := ⟨⟨80,[.var 0]⟩,by decide⟩
def q (receiver output : Nat) : CommonRoleStructuralAssociatedTemplates.Occurrence :=
  ⟨receiver,output,0,template⟩
def source : Source where
  program := [q 1000000 2000000,q 3000000 4000000]
  atoms := [.tyLe (.pair (.var 1000000) (.var 2000000)) (.pair (.base .str) (.var 3000000)),
    .tyLe (.pair (.base .str) (.var 3000000)) (.pair (.var 1000000) (.var 2000000))]
#guard names source = [1000000,2000000,3000000,4000000]
#guard capacity source = 5
#guard (slot source 1000000).val = 0
#guard (slot source 4000000).val = 3
#guard (slot source 99).val = 4
#guard readName source (slot source 3000000) = 3000000
#guard grammar source
#guard (prepare source).isSome
#guard (run env roles wf source).isSome
#guard (run env roles wf source).map (fun state =>
  CommonRoleOrdinaryKnownness.candidates state.atoms (slot source 4000000)) = some [.int]
#guard (run env roles wf source).map (fun state =>
  CommonRoleOrdinaryKnownness.candidates state.atoms (slot source 99)) = some []
def conflict : Source := {source with atoms := source.atoms ++
  [.tyLe (.var 4000000) (.base .str),.tyLe (.base .str) (.var 4000000)]}
#guard grammar conflict
#guard (prepare conflict).map CommonRoleOpenPropagation.consistent = some true
#guard (run env roles wf conflict).isNone

def empty : Source := ⟨[],[]⟩
#guard capacity empty = 1
#guard (prepare empty).isSome
#guard (run env roles wf empty).isSome

def rows : Source := ⟨[],[.rowLe (.join (.var 100) (.var 200)) (.var 300)]⟩
#guard names rows = [100,200,300]
#guard grammar rows
#guard (run env roles wf rows).isSome

def badRows : Source := ⟨[],[.rowLe .empty (.join (.var 100) (.var 200))]⟩
#guard !(grammar badRows)
#guard (prepare badRows).isNone
#guard (run env roles wf badRows).isNone

def widthMissing : Source := ⟨[],[.tyLe (.record 0 (.base .int) (.var 100)) (.var 200)]⟩
def widthPresent : Source := {widthMissing with atoms := widthMissing.atoms ++ [.tyLe (.var 100) .emptyRecord]}
#guard !(grammar widthMissing)
#guard (prepare widthMissing).isNone
#guard grammar widthPresent
#guard (prepare widthPresent).isSome

def nested : Source := ⟨[],[.tyLe
  (.arrow (.pair (.var 7) (.var 8)) (.var 9) (.variant 0 (.var 10)) (.var 11))
  (.var 12)]⟩
#guard names nested = [7,8,9,10,11,12]
-- A variant child in an arrow is outside the existing upper-child grammar.
#guard !(grammar nested)
def nestedGood : Source := ⟨[],[.tyLe
  (.arrow (.pair (.var 7) (.var 8)) (.var 9) (.required 0 (.var 10)) (.var 11))
  (.var 12)]⟩
#guard grammar nestedGood
#guard (prepare nestedGood).isSome

example : Good source := (grammar_exact source).mp (by decide +kernel)
example : slot source 1000000 ≠ slot source 4000000 := by decide +kernel
example (v : Nat → Comp Common.model) :
    All Common.model (v ∘ readName source) (atoms source) ↔ All Common.model v source.atoms := allocated_models source v
example (state : CommonRoleSettledConstraints.State (capacity source))
    (returned : run env roles wf source = some state) (v : Fin (capacity source) → Comp Common.model) :
    All Common.model v state.atoms ↔ SourceModels env roles source v :=
  run_source_models env roles wf awf source state returned v
end NamedBoundary

```

### stress-boundary.lean

```lean
import Yulang.CommonRoleStructuralNamedInputs
open Yulang PresenceNormalForm Core.PresenceGeneration
set_option maxRecDepth 16384
set_option maxHeartbeats 32000000
namespace AssociatedBoundary

def decl : Roles.Impl := ⟨80,[.var 0],[],800⟩
def annotated : Roles.AssocImpl := ⟨decl,[(0,.app 0 [])],by decide⟩
def env := Roles.AssocExamples.singletonEnv annotated
def signature : Roles.RoleDecl where
  arity := 1
  assoc := fun name => if name = 0 then some none else none
  defaultsScoped := by intro name rhs h; split at h <;> simp_all
def roles : Roles.RoleDecls := fun _ => signature
theorem wf : Roles.WellFormed env.cores := by
  simp [env,Roles.AssocExamples.singletonEnv,Roles.AssocEnv.cores,Roles.WellFormed,
    annotated,decl,Roles.Impl.WellFormed]
theorem awf : Roles.AssocWellFormed env roles := by
  intro i hi
  have same : i = annotated := by simpa [env,Roles.AssocExamples.singletonEnv] using hi
  subst i
  simp [Roles.AssocHeadVars,Roles.AssocComplete,Roles.AssocDeclared,annotated,decl,roles,
    signature,Roles.Term.occurrences,Roles.argsOccurrences]
def ty : Inference.Base → Roles.Term
  | .int => .app 0 [] | .str => .app 1 [] | .bool => .app 2 [] | .unit => .app 3 []
def occ (receiver output : Fin 4) : CommonRoleFiniteAssociatedClosure.Occurrence 4 :=
  ⟨receiver,output,0,fun head => ⟨80,[ty head]⟩⟩
end AssociatedBoundary


namespace FinalStress
open CommonRoleStructuralNamedInputs
open AssociatedBoundary (env roles wf awf)
def template : CommonRoleStructuralAssociatedTemplates.Template := ⟨⟨80,[.var 0]⟩,by decide⟩
def q (r o : Nat) : CommonRoleStructuralAssociatedTemplates.Occurrence := ⟨r,o,0,template⟩
def cycle : Source := ⟨[q 0 1,q 1 2,q 2 3,q 3 0],
  [.tyLe (.var 0) (.base .int),.tyLe (.base .int) (.var 0)]⟩
#guard (run env roles wf cycle).isSome
#guard (run env roles wf cycle).map (fun state =>
  (names cycle).all fun name => (CommonRoleOrdinaryKnownness.candidates state.atoms (slot cycle name)).contains .int &&
    (CommonRoleOrdinaryKnownness.candidates state.atoms (slot cycle name)).all (· == .int)) = some true
def contradiction : Source := {cycle with atoms :=
  [.tyLe (.var 0) (.base .str),.tyLe (.base .str) (.var 0)]}
#guard (prepare contradiction).map CommonRoleOpenPropagation.consistent = some true
#guard (run env roles wf contradiction).isNone
def unseeded : Source := {cycle with atoms := []}
#guard (run env roles wf unseeded).isSome
#guard (run env roles wf unseeded).map (fun state => state.atoms.length) = some 0

def nest : Nat → TyTerm Nat
  | 0 => .var 0
  | k+1 => .pair (.base .int) (nest k)
def closedNest : Nat → TyTerm Nat
  | 0 => .base .str
  | k+1 => .pair (.base .int) (closedNest k)
def deep : Source := ⟨[q 0 1,q 1 2],
  [.tyLe (nest 8) (closedNest 8),.tyLe (closedNest 8) (nest 8)]⟩
#guard (prepare deep).isSome
#guard (run env roles wf deep).isSome
#guard (run env roles wf deep).map (fun state =>
  CommonRoleOrdinaryKnownness.candidates state.atoms (slot deep 2)) = some [.int]
end FinalStress

```

### scoped-axiom-gate.lean

```lean
import Yulang.CommonRoleStructuralNamedInputs
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules := #[`Yulang.CommonRoleStructuralHornClosure,`Yulang.CommonRoleStructuralAssociatedClosure,`Yulang.CommonRoleStructuralAssociatedSolver,`Yulang.CommonRoleStructuralAssociatedReplay,`Yulang.CommonRoleStructuralHornSchedules,`Yulang.CommonRoleStructuralNamedInputs]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      let moduleName := environment.header.moduleNames[index.toNat]!
      if modules.contains moduleName then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "Forbidden dependency: {name} depends on {dependency}"
  if checked = 0 then throwError "No new declarations were checked"
  logInfo m!"Scoped allowlist passed for {checked} declarations from six new modules"

```
