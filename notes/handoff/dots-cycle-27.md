# Yulang Lean cycle27

開始 2026-11-09T04:57:58Z（通知04:57:19Z）。最新integration `74e630f93`を取得し、standing orders/inbox I-12まで再読。ACTIVE・上限なし。前回completedと報告を確認、同一作業場/キャッシュを使用。前回の本文に対する監督役の語の訂正を優先してmerge衝突2件を解消。新規部分以外の既存Leanの意味変更なし。

## 部分目標と達成範囲

**外部の観測状態を与えず、各候補表が自分で生成する関連型方程式の出力で再検証され、全選択annotationが実解決される有限証拠のモデル族を正確に探索する。** この診断用部分目標は閉じた。

前回は観測状態が入力で、未解決requestは式を課さなかった。今回は全表を静的choiceSpaceで正準化して全annotationを実associated batchに渡し、その出力で候補・全兄弟経路をValidとして再検査する。全requestの実解決成功もBoolean検査する。正準化で出力そのものが等しいので、任意のStable表を漏れなく探索する。意味論上の候補選択や言語拒否は決めていない。

## 定理（量化・前提、主張、効く側）

S=CommonRoleStableGlobalChoices、M=CommonRoleStableGlobalModels。
全て任意の自然数n、Paterson検査済Registryとsource rootを量化。
出力を使う定理はさらに任意のAssocEnv、RoleDecls、core WellFormed、route/declarationごとのannotation写像、ordinary seedを量化。
表は全祖先履歴付き(route,declaration)の有限列。sourceは既存int-only/unary/capture-bearing断片。
Stable表は「全表の正準化から作った出力状態でValid」かつ「全annotationのComputed出力が存在」。Validは登録済・同表の経路で到達可能・独立Candidate・同routeの候補一意・全到達routeの選択を要求する。

- S.canonical_mem: 任意tableと項pで、正準表所属 iff 静的choiceSpace所属かつ元表所属。（補助）
- S.canonical_ext: 任意のmembership同値な2表の正準表が等しい。（補助）
- S.canonical_idempotent: 任意表の正準化は冪等。（補助）
- S.requests_exact: 任意表・request qで、集めたrequest所属 iff 静的領域と元表に属する選択項のannotationである。（健全性/完全性補助）
- S.output_canonical: 任意表について正準化前後の出力状態は厳密に等しい。（補助）
- S.check_exact: 任意表で、実検査true iff 独立Stable。（健全性/完全性）
- S.search_exact: 任意表で、実探索所属 iff 静的部分列列挙所属かつStable。（健全性/完全性）
- S.complete: 任意Stable表は探索された正準代表を持ち、全項のmembershipと出力状態を厳密に保存。（完全性）
- S.search_capacity: 探索表数は2^(choiceSpace.length)以下。（有限性補助。実用計算量ではない）
- S.resolved: 任意の探索表・選択項・そのannotation qについて、Computed出力headが存在。（健全性補助）
- S.unknown_request_excluded: 任意表・選択項・annotation qで、receiver argsBoundが0でなければ、その表は探索に属さない。この完全証拠形式の不成立だけであり言語拒否ではない。（境界）
- M.output_models: 任意Stable表・assignmentで、出力モデル iff seedのモデルかつ全選択項の実Computed等式を同じassignmentが満たす。（健全性/完全性）
- M.supported_view_models: 任意Stable表・assignmentで、自己出力でguardを再検査した旧viewのモデル iff 直接生成した出力のモデル。（健全性/完全性補助）
- M.stable_declarative: AssocWellFormedを追加した任意表で、Stable iff 自己出力でValidかつ全選択annotationに独立DeclarativeComputed出力が存在。（健全性/完全性）
- M.siblings_at_output: 任意の探索表・選択親・その任意のsource childについて、同じ表の自己出力で拡張routeが到達可能で、同表にその選択がある。（健全性補助）
- M.infer_models_exact: 任意assignmentで、実探索された出力のいずれかのモデル iff seedのモデルかつ全選択等式を満たすStable表が存在。（健全性/完全性）
- M.infer_declarative_models_exact: 前項にAssocWellFormedを追加し、自己出力Validと全annotationの独立宣言導出の存在、全その出力等式を使ったiff。（健全性/完全性）

主型性を証明した定理はない。全選択annotationの解決を要求するのは強い診断用の証拠条件で、K2や言語の拒否範囲を新たに決めたものではない。

## 限界と次の橋

Stable自体は充足可能性を要求しない。表・解の存在、一意性、言語の候補選択は未証明。annotation写像とfirst-order receiverは入力で、sourceからの生成や網羅性、状態依存receiver生成は未証明。自己出力guarded viewの**モデル同値**は示したが、反復driverの構造的固定点・停止とは異なる。別履歴のsource node合流の一致も未達。
一般B4は依然5橋: source boundary、全generated work閉包、飽和停止/意味閉包、独立最終分類、辞書健全性/順序同値。今回は橋2〜3内部の自己支持・全解決証拠で、外側X13〜16のPROVEDは未達。
次の候補: (1)自己支持証拠と未完成診断treeの接続、(2)source loweringからannotation/receiver生成、(3)有限観測表現を用いた反復driverの停止。
新たな設計判断はせず、新質問ノートなし。cycle24の問いを継続する。

## Yulang2照合

取得済みauditのROLE-MORE-001〜005（`y2-claims-role-boundaries-cycle-2.md`）とspec6.3を再読。旧実機は複数role候補を曖昧とし、where前提の効力も現specと異なる。今回の全解決証拠は言語selected/拒否とはしない。以前のaudit読取り拒否を回避せず、最新audit再取得・新実機は未実施。

## 検証・制限

`cd lean && lake build --wfail Yulang.CommonRoleStableGlobalModels`: exit0、304 jobs。
`lake env lean --trust=0 /tmp/cycle27-audit.lean`: exit0、17定理、標準三公理のみ。
全体lake build・全Audit・verify-lean.shは指示に従い未実行。全体PASSの主張なし。
最初のコマンドは既存elanのPATH未設定でexit127。その後ELAN_HOME=/workspace/scratch/1d0b4aaa3394/dots-probe-elanを設定して再実行し成功。禁止構文なし。独立読取りレビューでannotation網羅性・充足可能性・driver固定点の非主張を確認。git diff --check成功。
空き開始19GB。キャッシュ複製なし。使用量枠不明。環境再生成なし。
開始心拍は実時計04:58:59Zで公開、elapsed_minを3と誤記（実際約1.02分）。終了心拍は実時計から算出して訂正。

### focused build・公理監査全文
```text
Build completed successfully (304 jobs).
'Yulang.CommonRoleStableGlobalChoices.canonical_mem' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStableGlobalChoices.canonical_ext' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStableGlobalChoices.canonical_idempotent' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStableGlobalChoices.requests_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStableGlobalChoices.output_canonical' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStableGlobalChoices.check_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStableGlobalChoices.search_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStableGlobalChoices.complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStableGlobalChoices.search_capacity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStableGlobalChoices.resolved' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStableGlobalChoices.unknown_request_excluded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleStableGlobalModels.output_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStableGlobalModels.supported_view_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStableGlobalModels.stable_declarative' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStableGlobalModels.siblings_at_output' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStableGlobalModels.infer_models_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStableGlobalModels.infer_declarative_models_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## 公開

9ファイル（新Lean2、追記3、design1、index1、report1、heartbeat1）。個別blobの後SHA tree/commitを作り、非force・expected-head付きでwork/dots-mainのみ更新する。公開後tree照合と終了時刻は親への報告で確定する。
部分目標が閉じ検証まで終わったため、時間埋めの追加補題は作らず公開して区切る。

### 公開照合と中断記録

05:09:38 UTC、公開 `c5b7a7d67` を再取得、検証済みローカル全treeとのdiff空・cleanを確認。9ファイル公開。空き終了19GB。
公開準備時にexec transport disconnectedが数回発生。環境listはconnectedで、同環境へ再attachしたら読取りが復帰した。再attach後read-onlyになったので、公開照合用fetchと本追記は明示的なsandbox審査を経て実行。環境のファイル消失や再生成は観測していない。
大きいREADME/Auditのblob作成待ちで10分心拍を出せず、開始公開04:58:59から最終公開05:09頃まで約10分超の間隔になった。成果公開は完了し、本記録と心拍時刻を追記して再公開する。25分上限内。
