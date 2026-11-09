# Cycle33: directed self-output search and environment recovery

## 時刻と復旧
通知: 2026-11-09T09:57:19Z。実着手: 10:02:52Z。25分期限は10:22:19Z。
基点 integration/m1-final: 4871ea4c1d6f535007ec134e6ade91ea28e4dbbd。
最新standing orders/inbox: ACTIVE、上限なし。前回cycle32のcompleted心拍と報告あり。
旧workspace yulang-cycle6 と旧elanは無く、新clone yulangから再開。公開済み成果は失われていない。
指定Lean v4.35.0をelan経由で再導入、lake version確認、焦点ビルドキャッシュを再構築。
新しい環境の空き開始60GB。並行writerなし。

## 部分目標
有向scalar上下界の正規化を、自己出力で全候補表・兄弟経路を再検証する有限探索へ接続する。
この部分目標は閉じた。一般の意味的含意や全言語の推論器は構成していない。

## 共通の量化と前提
以下は全て任意のslot数n、Registry、SourceRequest n、関連型環境env、role宣言roles、
core環境のWellFormed証拠wf、route/宣言ごとの入力注釈requests、seed State nについて。
独立宣言版の2定理だけAssocWellFormed env rolesも明示前提。
表・割当・route等の追加量化と前提は各項に記す。主型性を示した定理はない。

- `CommonRoleDirectedGlobalChoices.output_canonical`: 補助: 任意の候補表の正準化は実出力状態を変えない。
- `CommonRoleDirectedGlobalChoices.output_evidence`: 補助/健全性・完全性: 任意slot iとscalar bについて、出力の証拠 iff 生の関連型出力から上下両方の有向scalar boundsを独立に導出できる。
- `CommonRoleDirectedGlobalChoices.output_models_raw`: 健全性・完全性: 任意表と割当について、有向正規化後のモデル iff 生の関連型出力のモデル。空のモデル集合も含む。
- `CommonRoleDirectedGlobalChoices.check_exact`: 健全性・完全性: 任意表について、実行チェック成功 iff 新しいStable（自己出力でValidかつ全選択要求が解決）。
- `CommonRoleDirectedGlobalChoices.search_exact`: 健全性・完全性: 任意表について、探索に属する iff 有限宇宙の部分列候補であり新Stable。
- `CommonRoleDirectedGlobalChoices.complete`: 完全性: 任意の新Stable表に対し、その正準代表が探索に属し、所属と出力状態を保存。
- `CommonRoleDirectedGlobalChoices.search_capacity`: 補助: 探索結果数はchoiceSpace長を指数とする2のべき以下。
- `CommonRoleDirectedGlobalChoices.resolved`: 健全性: 任意の探索済み表・選択route/宣言・その任意注釈要求について、Computedなheadが存在。
- `CommonRoleDirectedGlobalChoices.output_models`: 健全性・完全性: 任意新Stable表と割当について、出力モデル iff seedモデルかつ全選択注釈のComputed等式。
- `CommonRoleDirectedGlobalChoices.infer_models_exact`: 健全性・完全性: 任意割当について、列挙出力のどれかのモデル iff seedモデルかつ任意の新Stable表が存在しその全選択注釈等式を満たす。
- `CommonRoleDirectedGlobalChoices.searched_tree_complete`: 健全性: 任意探索済み表とその診断treeの訪問routeに、一意な表候補が存在し全注釈要求が解決。
- `CommonRoleDirectedGlobalChoices.stable_declarative`: 健全性・完全性: AssocWellFormedを追加前提として、新Stable iff 自己出力のValidかつ全選択注釈に独立宣言的導出が存在。
- `CommonRoleDirectedGlobalChoices.infer_declarative_models_exact`: 健全性・完全性: AssocWellFormedの下、任意割当について探索出力のモデル存在 iff seedモデルかつ自己出力Validな表が存在し、全選択要求の独立導出の存在とその全等式を満たす。
- `CommonRoleDirectedGlobalChoices.searched_tree_models`: 健全性・完全性: 任意探索済み表と割当について、出力モデル iff seedモデルかつ訪問routeの全選択注釈のComputed等式。

## 正確なLean型（証明部分を除く）
~~~lean
theorem output_canonical (table : Table registry root) :
    output registry root env roles wf annotations seed (canonical registry root table) =
      output registry root env roles wf annotations seed table

theorem output_evidence (table : Table registry root) (i : Fin n) (b : Inference.Base) :
    CommonRoleOrdinaryKnownness.Evidence
      (output registry root env roles wf annotations seed table).atoms i b ↔
    CommonRoleDirectedBounds.Derived
      (CommonRoleStableGlobalChoices.output registry root env roles wf annotations seed table) (true,i,b) ∧
    CommonRoleDirectedBounds.Derived
      (CommonRoleStableGlobalChoices.output registry root env roles wf annotations seed table) (false,i,b)

theorem output_models_raw (table : Table registry root)
    (assignment : Fin n → Comp Common.model) :
    All Common.model assignment (output registry root env roles wf annotations seed table).atoms ↔
    All Common.model assignment
      (CommonRoleStableGlobalChoices.output registry root env roles wf annotations seed table).atoms

theorem check_exact (table : Table registry root) :
    check registry root env roles wf annotations seed table = true ↔
      Stable registry root env roles wf annotations seed table

theorem search_exact (table : Table registry root) :
    table ∈ search registry root env roles wf annotations seed ↔
      table ∈ CommonRoleSupportSearch.subsets (choiceSpace registry root) ∧
      Stable registry root env roles wf annotations seed table

theorem complete (table : Table registry root)
    (stable : Stable registry root env roles wf annotations seed table) :
    canonical registry root table ∈ search registry root env roles wf annotations seed ∧
      (∀ p, p ∈ canonical registry root table ↔ p ∈ table) ∧
      output registry root env roles wf annotations seed (canonical registry root table) =
        output registry root env roles wf annotations seed table

theorem search_capacity : (search registry root env roles wf annotations seed).length ≤
    2 ^ (choiceSpace registry root).length

theorem resolved (table : Table registry root)
    (found : table ∈ search registry root env roles wf annotations seed)
    (r : Route registry root) (d : Declaration) (chosen : (r,d) ∈ table)
    (q : Request n) (hq : q ∈ annotations r d) : ∃ head, Computed env roles wf q head

theorem output_models (table : Table registry root)
    (stable : Stable registry root env roles wf annotations seed table)
    (assignment : Fin n → Comp Common.model) :
    All Common.model assignment (output registry root env roles wf annotations seed table).atoms ↔
      All Common.model assignment seed.atoms ∧
      ∀ r d, (r,d) ∈ table → ∀ q ∈ annotations r d, ∀ head,
        Computed env roles wf q head → Common.Equivalent (assignment q.output).1 (.base head)

theorem infer_models_exact (assignment : Fin n → Comp Common.model) :
    (∃ out ∈ infer registry root env roles wf annotations seed,
      All Common.model assignment out.atoms) ↔
    All Common.model assignment seed.atoms ∧
      ∃ table : Table registry root,
        Stable registry root env roles wf annotations seed table ∧
        ∀ r d, (r,d) ∈ table → ∀ q ∈ annotations r d, ∀ head,
          Computed env roles wf q head → Common.Equivalent (assignment q.output).1 (.base head)

theorem searched_tree_complete
    (table : Table registry root)
    (found : table ∈ search registry root env roles wf annotations seed)
    (r : Route registry root)
    (visit : Visit registry root
      (diagnose registry root table (output registry root env roles wf annotations seed table)) r) :
    ∃ d, (r,d) ∈ table ∧ (∀ e, (r,e) ∈ table → e = d) ∧
      ∀ q ∈ annotations r d, ∃ head, CommonRoleAssociatedStateFlow.Computed env roles wf q head

theorem stable_declarative (awf : Roles.AssocWellFormed env roles)
    (table : Table registry root) :
    Stable registry root env roles wf annotations seed table ↔
      CommonRoleGlobalChoices.Valid registry root
        (output registry root env roles wf annotations seed table) table ∧
      ∀ r d, (r,d) ∈ table → ∀ q ∈ annotations r d, ∃ head,
        CommonRoleAssociatedDeclarationExact.DeclarativeComputed env roles q head

theorem infer_declarative_models_exact (awf : Roles.AssocWellFormed env roles)
    (assignment : Fin n → Comp Common.model) :
    (∃ out ∈ infer registry root env roles wf annotations seed,
      All Common.model assignment out.atoms) ↔
    All Common.model assignment seed.atoms ∧
      ∃ table : Table registry root,
        CommonRoleGlobalChoices.Valid registry root
          (output registry root env roles wf annotations seed table) table ∧
        (∀ r d, (r,d) ∈ table → ∀ q ∈ annotations r d, ∃ head,
          CommonRoleAssociatedDeclarationExact.DeclarativeComputed env roles q head) ∧
        ∀ r d, (r,d) ∈ table → ∀ q ∈ annotations r d, ∀ head,
          CommonRoleAssociatedDeclarationExact.DeclarativeComputed env roles q head →
            Common.Equivalent (assignment q.output).1 (.base head)

theorem searched_tree_models
    (table : Table registry root)
    (found : table ∈ search registry root env roles wf annotations seed)
    (assignment : Fin n → Core.PresenceGeneration.Comp Common.model) :
    PresenceNormalForm.All Common.model assignment
      (output registry root env roles wf annotations seed table).atoms ↔
    PresenceNormalForm.All Common.model assignment seed.atoms ∧
      ∀ r, Visit registry root
        (diagnose registry root table
          (output registry root env roles wf annotations seed table)) r →
        ∀ d, (r,d) ∈ table → ∀ q ∈ annotations r d, ∀ head,
          CommonRoleAssociatedStateFlow.Computed env roles wf q head →
            Common.Equivalent (assignment q.output).1 (.base head)

~~~

## 検証
`ELAN_HOME=/workspace/scratch/1d0b4aaa3394/elan` とそのbinをPATHへ設定。
`elan toolchain install leanprover/lean4:v4.35.0`: exit0。
`lake --version`: Lake 5.0.0-src+eb6cafb, Lean 4.35.0。
`timeout 8m lake build --wfail Yulang.CommonRoleDirectedBoundsCheck`: exit0、cold 312 jobs。
`lake build --wfail Yulang.CommonRoleDirectedGlobalChoices`: exit0、313 jobs。
`lake env lean --trust=0 /tmp/cycle33-audit.lean`: exit0、14定理、標準三公理のみ。
全体build・全Audit・verify-lean.shは常設指示に従い未実行。全体PASSではない。
読取りレビューで問題なし。レビュー担当の独立ビルドは行っていない。

### 新モジュール検証の出力全文
~~~text
✔ [311/313] Built Yulang.CommonRoleEvidenceNormalization (942ms)
✔ [312/313] Built Yulang.CommonRoleNormalizedGlobalChoices (1.0s)
✔ [313/313] Built Yulang.CommonRoleDirectedGlobalChoices (1.1s)
Build completed successfully (313 jobs).
'Yulang.CommonRoleDirectedGlobalChoices.output_canonical' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDirectedGlobalChoices.output_evidence' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDirectedGlobalChoices.output_models_raw' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDirectedGlobalChoices.check_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDirectedGlobalChoices.search_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDirectedGlobalChoices.complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDirectedGlobalChoices.search_capacity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDirectedGlobalChoices.resolved' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDirectedGlobalChoices.output_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDirectedGlobalChoices.infer_models_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDirectedGlobalChoices.searched_tree_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDirectedGlobalChoices.stable_declarative' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDirectedGlobalChoices.infer_declarative_models_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDirectedGlobalChoices.searched_tree_models' depends on axioms: [propext, Classical.choice, Quot.sound]
~~~

## B4と未達
主要5橋は全て一般形では未完。今回の定理は橋1/3/4内部の有限診断断片を接続した。
sourceからの注釈/receiver生成、状態依存receiver、role feedback停止、一般意味的正規化、
解の存在・一意性・主型性、言語候補選択/分類、X13〜X16外側PROVEDは未達。
Stable自体は充足可能性を保証しない。旧Stableとの同値は主張しない。
次: (1)state依存receiverのsource生成、(2)role再生成を含む有限進捗尺度、(3)独立最終分類。
意味論判断なし、質問ノートなし。

## Yulang2との照合
既存取得済み `notes/audit/y2-claims-role-boundaries-cycle-2.md` ROLE-MORE-001〜008を再読。
最新audit枝取得と新実機照合は未実行。有向scalar証拠は部分型推移律の断片で、role選択規則を新規決定しない。

## 公開と制限
GitHubアプリ経由でwork/dots-mainのみ。個別blob後SHA treeの一括非force expected-head更新を使用。
使用量枠は不明。新Lean 1ファイル、root/Audit/README追記、設計ノートと索引、報告、心拍を公開予定。
早期終了は復旧と明示部分目標の検証が完了し、公開・照合を残すため。
