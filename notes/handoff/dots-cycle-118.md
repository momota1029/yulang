# Cycle 118: arbitrary scalar registries, source expressions and saturation

開始: 2026-11-11T13:23:04Z。検証・報告時点: 2026-11-11T14:11:06.392269+00:00、経過 48.04 分。最終公開・tree 照合を含め約50分で終了する。復旧と4つの連続した部分目標は25分では収まらなかった。終了理由は I-15(a) の時間枠。

**B4Bridges の未証明フィールド**: 旧 target は12/12。I-17 の新 target の構造体はまだ作っていないため、新しい k/m を旧構造体の数字で代用しない。I-17 は14:03 UTCに受領し、次サイクル最初に B4TargetV2 と改訂骨格を作る。一般の B4Statement が完成したという主張はしない。

## 成果と途中公開

- 復旧（13:23–13:35、約12分）: cycle116 の15ファイル差分のうち14の証明・文書を保持。古い心拍だけ除外。faed371c21ff07b086fd4a9b76af232bbf153e98 に公開し全 blob の SHA を照合。復旧10分上限を約2分超過した。独立した証明準備と並行したがリポジトリの書き手は一人。詳細は dots-main-crash-117.md。
- P1/P2/P3（復旧中の準備を含め13:23–13:39、約16分）: 任意の有限 int/str 実装レジストリについて独立分類、実行 iff、実際の辞書の全モデル健全性、可視集合による結果の不変性を閉じた。CommonRoleScalarRegistry、438行、24定理。公開 c2506b4476fb10e16c6fdd9737a9276f12acfe50。
- ソース式からの接続（13:39–13:44、約5分）: 閉じた既存 Inference.Expr と明示 int/str 注釈から検査、制約生成、solver、materializer、辞書まで接続。CommonRoleScalarExpressionRegistry、127行、7定理。公開 0a965febfdb21de039eef91ef6ccf71a7cc6e1c7。
- 飽和後のソース名からの接続（13:44–13:56、約12分）: 既存の名前付き通常・関連制約の閉包で計算した状態を分類。元のソース名と独立 Derives で iff と全モデル健全性を証明し、入力の並べ替え・重複に対しても同じ結果を保持。CommonRoleSaturatedScalarRegistry、211行、11定理。公開 22226a25dc98d81b39058ed6ba8356419448fed4。
- 旧 target の具体的阻害（13:56–14:02、約6分）: 実際の scalar registry と実モデルを持つ空状態で旧分類の pending/rejected 重複を示した。任意の executor について旧 B4Statement と旧 B4Bridges が成立しない具体的境界を証明。CommonRoleScalarTargetObstruction、105行、9定理。コード最終公開 ad4abbb3cec877fe712479ab366840bc3cb5954d。

新規は4モジュール、881行、51定理。復旧5モジュールの既存68監査宣言は新規51に数えない。P1/P2/P3 の scalar leaf 断片として frontierLocal/evidenceNode と順序独立の義務を縮めたが、一般の橋のフィールドは未実装。

## 主定理の主張・量化子・前提

1. CommonRoleScalarRegistry.run_exact: 任意の自然数 n、有限 entries、role、receiver : Fin n、state : State n、out について、実行が some out を返すことと state.Models かつ独立 Classify が同値。Models は caller が仮定として渡すのでなく iff の右辺。Classify の Known は元の通常制約の int/str の両側証拠、Candidate は実ソース宣言の所属・role・scalar。同じ結果を実行版の定義で言い換えてはいない。
2. 同 run_all_models / successful_dictionary_exact: 任意の上記入力と返された Plan、および元の全 atoms を満たす任意の Common assignment に対して、その receiver の型で実際の辞書が Implements を満たす。候補一つだけに固定せず任意のレジストリ。成功の iff に全モデル健全性を加えた定理もある。
3. 同 run_visible_set: 任意の同じ所属関係を持つ二つの entries、role、receiver、state について、実行結果そのものが等しい。selected の辞書 payload を捨てない。permutation と duplicate は帰結。空・未知は pending、既知で候補ゼロは rejected、単一は selected、同じ head で異なる key は ambiguous の回帰を含む。
4. CommonRoleScalarExpressionRegistry.run_exact: 任意の entries、role、int/str annotation、既存 Inference.Expr、Answer について、実行の ready Answer と独立 Evaluates および Ready が同値。run_all_models は任意の元の式の Meaning 値について、注釈を満たす全モデルで返した辞書を証明する。型検査器が選んだ代表値だけではない。never_pending は注釈・構文検査に成功した経路で known となることを反映する。検査不成功は none。
5. CommonRoleSaturatedScalarRegistry.run_exact: 任意の associated env、role 宣言、WellFormed と AssocWellFormed の証拠、既存 Program、通常 Input、entries、role、ソース名 root、out について、実行結果が some out であることと、root が計算済み名前表に含まれ、元の名前付き Models が存在し、独立 Classify が成立することが同値。run_all_models は通常入力と全 Derives の事実を満たす任意の元の名前付き values に対して返した辞書の Implements を示す。run_input_congr は同じ入力所属関係を持つ二つの Input に対し、割当 slot の並びが違っても同じ結果を返す。
6. CommonRoleScalarTargetObstruction: 空 entries、State.empty、任意の role に実際の checked/model/pending を構成し、旧 B4Target.Classify が pending と rejected の両方を導く。Steps は状態を変えない境界なので、任意の executor が都合よく状態を変更して回避できない。old_target_impossible はこの明示した vocabulary/boundary の任意の executor に対する否定、old_bridges_impossible はさらに任意の旧 frontiers に対する否定。意図された言語の一般 B4 が不可能という意味ではない。

分類 iff は健全性・完全性。辞書の全モデル定理は健全性。可視集合不変性は補助不変条件。旧 target の反例は仕様モデルの検証。主性の新しい一般定理は主張しない。

## 正しい対象を証明したか・限界

- scalar materialization は int/str の明示的な両側証拠だけ。bool/unit/一般構造を pending とする adapter の制限を、言語全体の knownness と同一視しない。矛盾状態の none は新しい言語拒否規則ではない。
- 最終レジストリの辞書は where 子なしの leaf。一般 K2、子失敗を含む診断 tree、一般 Form の materialization、method body、parser/module visibility、effect は未証明。
- 式の入口は既存の閉じた literal/variable/let と明示 scalar 注釈。一般の開環境・構文を追加したのではない。
- 飽和側の associated env と最終 scalar registry は別入力であり、同じ言語可視宣言から双方が導かれるという一致は未証明。WellFormed/AssocWellFormed は引き続き前提。SourceModel は明記した通常入力と関連導出のモデル。
- spec 6.2/6.3、および既存 audit の ROLE-MORE-001（0/1/異なる key の重複候補）、ROLE-MORE-002（specificity 優先を導入しない）と照合した。今回新しい Yulang2 実機 oracle 実行はしていない。
- I-17 は保留を拒否より先とし、完全な診断 tree を exactness の対象にするユーザー決定を反映している。14:03 の integration 30f49167ab45a500c39e96993c099cb047af6390 を取り込み、最新 inbox と承認済み草稿補遺をそのまま保存。検証済み Lean 内容はマージ前後で不変。旧 target の阻害は修正を要求する回帰として残す。解決済みの意味論を再質問しない。新規質問ノートは0。

## 検証

PATH にキャッシュ済み Lean 4.35.0 を指定。全プロジェクト lake build、全 Audit.lean、AxiomGate はローカルで実行していない。明示した9対象のみの focused build。

コマンド（lean/）:
`lake build --wfail Yulang.B4Skeleton Yulang.CommonRoleRawStructuralSource Yulang.CommonRoleSaturatedScalarRegistry Yulang.CommonRoleScalarDictionaryModels Yulang.CommonRoleScalarExpressionRegistry Yulang.CommonRoleScalarRegistry Yulang.CommonRoleScalarTargetObstruction Yulang.CommonRoleSettledRootClassification Yulang.CommonRoleSettledVisibleOrder`

出力全文: `Build completed successfully (529 jobs).` 終了コード0。

9対象の各ソースに `lake env lean --trust=0 Yulang/<module>.lean` を実行し全て終了コード0。新規および復旧の119監査宣言だけを抽出した `/tmp/yulang118/FinalAudit.lean` に `lake env lean --trust=0` を実行し終了コード0。116は propext / Classical.choice / Quot.sound の許可集合のみ、3は公理依存なし。51の新規定理は全て監査対象。検証コマンド・出力全文・監査本文は隣の dots-cycle-118-validation.txt。

`bash tools/verify-lean.sh . origin/integration/m1-final --no-build` 出力全文:

verify-lean: yulang @ e4168b25a (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)

終了コード0。`git diff --check` も終了コード0。I-17 マージ後に `git diff --exit-code a6f4938b9 HEAD -- lean/` が終了コード0で、検証した Lean 木との一致を確認。

GitHub CI（ad4abbb3cec877fe712479ab366840bc3cb5954d、14:08 UTCに再取得）:
- Core CI: completed / success、https://github.com/momota1029/yulang/actions/runs/43034634733
- Lean inference kernel: completed / success、https://github.com/momota1029/yulang/actions/runs/43034634849
これは上記コード commit の結果。報告・心拍と I-17 文書を含む最終 commit の CI まで先取りして合格とは書かない。

## 公開・中断・資源

公開先は work/dots-main のみ。各部分目標ごとに blob を用意し一つの tree/commit を作り、expected-head、非 force の ref 更新で公開。統合ブランチには書いていない。コード ad4 までの全ファイルを remote tree で照合済み。最終公開は最新 integration を親にもつ merge commit に全差分16ファイルを載せ、公開後に全 SHA を再照合する。

一度 expression 公開の update_ref が timeout。ref を読み実行前のままと確認してから expected-head の同じ更新を一度だけ再試行し、成功を検証。未確定の更新は残っていない。大きな全内容 tree 送信は使わず、個別 blob と小さい SHA tree の正規 API に変更。開発中の Lean simplifier の timeout は大きな閉包の不用意な展開が原因で、明示 Option.bind と直接 iff 構成に直して解消。最終 focused build は成功。

心拍は開始時と約10/20/30/40分に公開し、最後は completed と本報告を公開。開始時の空き容量は測っておらず不明。14:04 時点は42GiB空き（63GiB中、31%使用）。使用量枠は不明。

## 次サイクルの最初の部分目標

1. I-17 P0: 新 B4TargetV2。候補ゼロ・RootK2・CandidateK2 に pending と重ならない条件、診断 tree の Resolves iff、Completed のみの4分類、同じ量化子の新 Statement、新 B4Bridges と合成、Classify の関数性。旧 target/骨格は残す。新しい k/m を数える。
2. その後 I-16 P1/P2: 今回の scalar leaf の独立分類と実辞書を、新 target の局所診断判断・証拠に接続。閉じない一般義務を明記する。
3. 一般化はその義務を閉じるのに必要な範囲に限定。関連環境と最終可視 registry のソース上の一致、where 子と一般 K2 は未解決の接続として追う。

## 新規定理の完全な名前と型

以下は各モジュールの namespace 内。上の日本語の主張・前提を補助定理まで省略せず確認できるよう、型をそのまま列挙する。

### Yulang.CommonRoleScalarRegistry

```lean
theorem wellFormed (entries : List Entry) : Roles.WellFormed (visible entries)
```

```lean
theorem leaf (entries : List Entry) (implementation : Roles.Impl)
    (member : implementation ∈ visible entries) : implementation.constraints = []
```

```lean
theorem matches_entry (entry : Entry) (role : Nat) (term : Roles.Term) :
    Roles.Matches entry.impl (goal role term) ↔ entry.role = role ∧ term = entry.scalar.term
```

```lean
theorem candidate_exact (entries : List Entry) (role : Nat) (term : Roles.Term)
    (implementation : Roles.Impl) :
    implementation ∈ Roles.candidates (visible entries) (goal role term) ↔
      Candidate entries role term implementation
```

```lean
theorem unique_exact (entries : List Entry) (role : Nat) (term : Roles.Term)
    (implementation : Roles.Impl) :
    Roles.candidates (visible entries) (goal role term) = [implementation] ↔
      Unique entries role term implementation
```

```lean
theorem elaborate_selected (entries : List Entry) (role : Nat) (term : Roles.Term) (out : Plan) :
    RoleDictionaries.elaborate (visible entries) (wellFormed entries) (goal role term) = .resolved out ↔
      ∃ implementation, Unique entries role term implementation ∧ out = .node implementation []
```

```lean
theorem resolve_leaf (entries : List Entry) (role : Nat) (term : Roles.Term) :
    Roles.resolve (visible entries) (wellFormed entries) (goal role term) =
      match Roles.candidates (visible entries) (goal role term) with
      | [] => .noImpl
      | [_] => .resolved
      | _ :: _ :: _ => .ambiguous
```

```lean
theorem elaborate_rejected (entries : List Entry) (role : Nat) (term : Roles.Term) :
    RoleDictionaries.elaborate (visible entries) (wellFormed entries) (goal role term) = .noImpl ↔
      ∀ implementation, ¬ Candidate entries role term implementation
```

```lean
theorem elaborate_ambiguous (entries : List Entry) (role : Nat) (term : Roles.Term) :
    RoleDictionaries.elaborate (visible entries) (wellFormed entries) (goal role term) = .ambiguous ↔
      ∃ first second, Candidate entries role term first ∧ Candidate entries role term second ∧
        first ≠ second
```

```lean
theorem elaborate_exact (entries : List Entry) (role : Nat) (term : Roles.Term) (out : Answer) :
    RoleDictionaries.elaborate (visible entries) (wellFormed entries) (goal role term) = out ↔
      Ready entries role term out
```

```lean
theorem materialize_exact (state : State n) (receiver : Fin n) (models : state.Models) (term : Roles.Term) :
    materialize state.atoms receiver = some term ↔ Known state receiver term
```

```lean
theorem run_exact (entries : List Entry) (role : Nat) (receiver : Fin n) (state : State n) (out : Outcome) :
    run entries role receiver state = some out ↔ state.Models ∧ Classify entries role receiver state out
```

```lean
theorem scalar_term_injective (first last : Scalar) (equal : first.term = last.term) : first = last
```

```lean
theorem run_all_models (entries : List Entry) (role : Nat) (receiver : Fin n) (state : State n)
    (out : Plan) (returned : run entries role receiver state = some (.ready (.resolved out)))
    (assignment : Fin n → Comp Common.model) (models : All Common.model assignment state.atoms) :
    Implements entries role (assignment receiver).1 out
```

```lean
theorem successful_dictionary_exact (entries : List Entry) (role : Nat)
    (receiver : Fin n) (state : State n) (out : Plan) :
    (run entries role receiver state = some (.ready (.resolved out)) ∧
      ∀ assignment : Fin n → Comp Common.model, All Common.model assignment state.atoms →
        Implements entries role (assignment receiver).1 out) ↔
      state.Models ∧ Classify entries role receiver state (.ready (.resolved out))
```

```lean
theorem run_visible_set (first last : List Entry)
    (same : ∀ entry, entry ∈ first ↔ entry ∈ last) (role : Nat)
    (receiver : Fin n) (state : State n) : run first role receiver state = run last role receiver state
```

```lean
theorem run_permutation (first last : List Entry) (permutation : first.Perm last)
    (role : Nat) (receiver : Fin n) (state : State n) :
    run first role receiver state = run last role receiver state
```

```lean
theorem run_duplicate (entries : List Entry) (role : Nat) (receiver : Fin n) (state : State n) :
    run (entries ++ entries) role receiver state = run entries role receiver state
```

```lean
theorem empty_pending (entries : List Entry) (role : Nat) (receiver : Fin n) :
    run entries role receiver State.empty = some .pending
```

```lean
theorem inconsistent_unavailable (entries : List Entry) (role : Nat)
    (receiver : Fin n) (state : State n) (inconsistent : ¬ state.Models) :
    run entries role receiver state = none
```

```lean
theorem run_recorded (entries : List Entry) (role : Nat) (receiver : Fin n) (scalar : Scalar) :
    run entries role receiver (CommonRoleCandidateStateFrontier.extend State.empty receiver scalar.base) =
      some (.ready (RoleDictionaries.elaborate (visible entries) (wellFormed entries) (goal role scalar.term)))
```

```lean
theorem known_empty_rejected (role : Nat) (receiver : Fin n) (scalar : Scalar) :
    run [] role receiver (CommonRoleCandidateStateFrontier.extend State.empty receiver scalar.base) =
      some (.ready .noImpl)
```

```lean
theorem recorded_singleton_selected (entry : Entry) (receiver : Fin n) :
    run [entry] entry.role receiver
      (CommonRoleCandidateStateFrontier.extend State.empty receiver entry.scalar.base) =
      some (.ready (.resolved (.node entry.impl [])))
```

```lean
theorem recorded_overlap_ambiguous (role firstKey secondKey : Nat) (scalar : Scalar)
    (distinct : firstKey ≠ secondKey) (receiver : Fin n) :
    run [⟨role, firstKey, scalar⟩, ⟨role, secondKey, scalar⟩] role receiver
      (CommonRoleCandidateStateFrontier.extend State.empty receiver scalar.base) = some (.ready .ambiguous)
```

### Yulang.CommonRoleScalarExpressionRegistry

```lean
theorem run_exact (entries : List Entry) (role : Nat) (annotation : Scalar)
    (expression : Inference.Expr) (answer : Answer) :
    run entries role annotation expression = some (.ready answer) ↔
      Classify entries role annotation expression answer
```

```lean
theorem run_exists_iff (entries : List Entry) (role : Nat) (annotation : Scalar)
    (expression : Inference.Expr) :
    (∃ answer, run entries role annotation expression = some (.ready answer)) ↔
      Evaluates [] expression annotation.base
```

```lean
theorem initial_models (annotation : Scalar) (expression : Inference.Expr)
    (evaluated : Evaluates [] expression annotation.base) (value : Common.Ty)
    (meaning : Meaning expression annotation.base value) :
    PresenceNormalForm.All Common.model (fun _ => Comp.pure Common.model value) (initial annotation).atoms
```

```lean
theorem run_all_models (entries : List Entry) (role : Nat) (annotation : Scalar)
    (expression : Inference.Expr) (dictionary : Plan)
    (returned : run entries role annotation expression = some (.ready (.resolved dictionary)))
    (value : Common.Ty) (meaning : Meaning expression annotation.base value) :
    Implements entries role value dictionary
```

```lean
theorem successful_dictionary_exact (entries : List Entry) (role : Nat) (annotation : Scalar)
    (expression : Inference.Expr) (dictionary : Plan) :
    (run entries role annotation expression = some (.ready (.resolved dictionary)) ∧
      ∀ value, Meaning expression annotation.base value → Implements entries role value dictionary) ↔
      Classify entries role annotation expression (.resolved dictionary)
```

```lean
theorem run_visible_set (first last : List Entry)
    (same : ∀ entry, entry ∈ first ↔ entry ∈ last)
    (role : Nat) (annotation : Scalar) (expression : Inference.Expr) :
    run first role annotation expression = run last role annotation expression
```

```lean
theorem never_pending (entries : List Entry) (role : Nat) (annotation : Scalar)
    (expression : Inference.Expr) : run entries role annotation expression ≠ some .pending
```

### Yulang.CommonRoleSaturatedScalarRegistry

```lean
theorem lookup_sound (names : List Nat) (root : Nat) (slot : Fin names.length)
    (found : lookup names root = some slot) : names[slot] = root
```

```lean
theorem lookup_exists (names : List Nat) (root : Nat) :
    (∃ slot, lookup names root = some slot) ↔ root ∈ names
```

```lean
theorem known_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (program : Program) (input : Input) (slot : Fin (table program input).length) (term : Roles.Term) :
    CommonRoleScalarRegistry.Known (CommonRoleNamedOrdinaryInputs.run env roles wf program input) slot term ↔
      Known env roles program input (name program input slot) term
```

```lean
theorem classify_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (program : Program) (input : Input) (entries : List Entry) (role : Nat)
    (slot : Fin (table program input).length) (out : Outcome) :
    CommonRoleScalarRegistry.Classify entries role slot
      (CommonRoleNamedOrdinaryInputs.run env roles wf program input) out ↔
      Classify env roles program input entries role (name program input slot) out
```

```lean
theorem run_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (program : Program) (input : Input) (entries : List Entry) (role root : Nat) (out : Outcome) :
    run env roles wf program input entries role root = some out ↔
      root ∈ table program input ∧ CommonRoleNamedOrdinaryInputs.Models env roles program input ∧
        Classify env roles program input entries role root out
```

```lean
theorem run_all_models (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (program : Program) (input : Input) (entries : List Entry) (role root : Nat) (dictionary : Plan)
    (returned : run env roles wf program input entries role root = some (.ready (.resolved dictionary)))
    (values : Nat → Common.Ty) (models : SourceModel env roles program input values) :
    Implements entries role (values root) dictionary
```

```lean
theorem run_visible_set (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (program : Program) (input : Input)
    (first last : List Entry) (same : ∀ entry, entry ∈ first ↔ entry ∈ last) (role root : Nat) :
    run env roles wf program input first role root = run env roles wf program input last role root
```

```lean
theorem known_input_congr (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (program : Program)
    (first last : Input) (same : ∀ q, q ∈ first ↔ q ∈ last) (root : Nat) (term : Roles.Term) :
    Known env roles program first root term ↔ Known env roles program last root term
```

```lean
theorem classify_input_congr (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (program : Program)
    (first last : Input) (same : ∀ q, q ∈ first ↔ q ∈ last)
    (entries : List Entry) (role root : Nat) (out : Outcome) :
    Classify env roles program first entries role root out ↔
      Classify env roles program last entries role root out
```

```lean
theorem domain_input_congr (program : Program) (first last : Input)
    (same : ∀ q, q ∈ first ↔ q ∈ last) (root : Nat) :
    root ∈ table program first ↔ root ∈ table program last
```

```lean
theorem run_input_congr (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (program : Program) (first last : Input) (same : ∀ q, q ∈ first ↔ q ∈ last)
    (entries : List Entry) (role root : Nat) :
    run env roles wf program first entries role root = run env roles wf program last entries role root
```

### Yulang.CommonRoleScalarTargetObstruction

```lean
theorem empty_checked : boundary.Checked []
```

```lean
theorem empty_has_model : ∃ model, boundary.Models State.empty model
```

```lean
theorem empty_pending (role : Nat) : boundary.RootPending [] State.empty role
```

```lean
theorem empty_survivors (state : State 1) (role key : Nat) (children : List Nat) :
    ¬ boundary.Survivor [] state role key children
```

```lean
theorem old_target_double_classification (role : Nat) :
    B4Target.Classify boundary [] State.empty role .pending ∧
      B4Target.Classify boundary [] State.empty role .rejected
```

```lean
theorem actual_source_pending (role : Nat) :
    CommonRoleScalarRegistry.run [] role (0 : Fin 1) State.empty = some .pending
```

```lean
theorem steps_unchanged (entries : List Entry) (role : Nat) (before after : State 1)
    (trace : Steps (boundary.Step entries role) before after) : after = before
```

```lean
theorem old_target_impossible (executor : Executor vocabulary) : ¬ B4Skeleton.B4Statement boundary executor
```

```lean
theorem old_bridges_impossible (executor : Executor vocabulary) (frontiers : B4Skeleton.Frontiers vocabulary) :
    ¬ B4Skeleton.B4Bridges boundary executor frontiers
```
