# Audit cycle 5 — resource-limited continuation

開始: 2026-11-08T14:56:09Z。最新取得 integration `9b619434c`、A-1 ACTIVE、上限12。前回心拍cycle4 completedと報告・短い復旧メモを読み、開始心拍を公開した。ユーザー最新の25分上限を優先する。

## 実施

- GitHubで最新 standing orders/inbox/heartbeats/報告を読み、`git fetch origin integration/m1-final` は成功。
- 旧Y2の既存binary・ソースを再利用。新しいビルドやLeanソース変更はしない。
- `yulang cache stats` は以下。重い標準prelude処理は開始しない。

```text
cache: /home/agent/.cache/yulang
control-ir: 0
mono: 0
poly: 0
compiled-unit: 0
realm-resolution: 0
```

- F1 の unused / identity / duplicated use と direct / higher / eta の9入力を、check・dump --mono・VM run・interpreter runの4段階、計36回実行した。
- ただし全入力は no-prelude 下で未定義の `+` を使っていたため、36回すべてexit1。この試験からF1の意味論やeffectの回数に結論を出さない。先行cycle3/4の結果を今回の再確認済みとして扱わない。
- 出力の末尾（全入力共通）:

```text
hint: define `#op:infix:+` before this use, or import the module that provides it
```

- 原本JSON、全ソース・コマンド・stdout/stderr・時刻・各所要時間は `/tmp/audit5/probe.json`。実行スクリプトは `/tmp/audit5/probe.py`。今回は完全rawログを公開していない。

## 資源障害

新しい独立worktree作成は以下で失敗:

```text
Preparing worktree (detached HEAD 9b619434c)
fatal: could not create directory of '/workspace/scratch/1d0b4aaa3394/yulang-audit-cycle2/.git/worktrees/yulang-audit-cycle5': No space left on device
```

その後、容量・inode・算術primitiveを読むためのシェル操作自体も開始できなくなった:

```text
bwrap: Can't create file /workspace/shared/.git: No space left on device
```

容量とinodeのどちらが不足したかは未確認。既存ファイル・キャッシュ・成果を勝手に削除していない。GitHub APIは動作するので、この報告と終了心拍を公開する。新規ローカルcommitは未作成。過去の原本`1794212d8`や未公開大ログを破棄していない。

## 判定・次の一手

新しい文書主張の分類は0件。X1〜X25の既存判定を変更せず、新spec/Leanに欠落を追加判定しない。意味論判断・質問ノート・spec編集なし。Lean全体ビルドも未実行。

1. 作業領域の容量/inodeを回復してシェルを起動可能にする（削除対象は承認された生成キャッシュに限定）。
2. `+` を定義した自己完結コードで36試験を修正・再実行し、effect回数を直接観測する。
3. 先行復旧の未公開rawログを小さい単位で保全する。

このサイクルは資源障害を隠さず終了し、同じ失敗を再実行し続けない。使用量計上は不明。

## 復旧後の完了追記（2026-11-08 15:04 UTC）

親が別作業の再生成可能キャッシュを解放した後、こちらで4.3GB空き・inode77%空きを確認した。こちらの作業ではファイルを削除していない。通常シェルが再び使え、独立worktree作成にも成功した。上の「終了」は資源障害時の暫定報告であり、回復後に次の短い試験を続けた。

### 新しい観測

効果handlerはpingごとに7で再開し、再開結果を同じhandlerで包み直して100を加える。ordinary actualの本体と呼出経路の9組を比較した。

|actual本体|direct|higher actual|higher(\\x -> actual x)|
|---|---|---|---|
|42|142|42|142|
|x|107|107|107|
|x+x|114|mono段階で失敗|114|

VMとinterpreterで結果は一致する。全9入力check exit0。higher(x+x)はmonoで `conflicting type candidates: [ping] vs []`、runも同じcompile errorでexit1。したがって「高階の二重使用で効果が2回起きる」とは言えない。direct/etaの114は、この具体例では引数効果1回を観測する。一方unused ordinary関数を高階へ渡すとpingが起きない42となり、新spec5.5cの起動時放出と違う。これは有限matrixの結果で、一般の必要十分条件・新しいLean定理ではない。

追加の4＋4対照では、pure add100 7は107、handler armの `k 7` 単独は7。ordinary addへ `k 7` を直接渡すとcheck/monoは成功するがVM/interpreterはthunkをintとして消費するruntime error。 `add 100 (handle(k 7))` は107となる。shallow handlerの再設置自体が不要だと主張するものではなく、この具体的な継続結果消費の境界の記録。一般的なroot causeや修正方針は決定しない。

### 記録と分類

新しい主張表 `y2-claims-f1-cycle-5.md` は7行（4一致、2違う、1未確認）。既存X表は変更しない。

試験は合計176 CLI呼出、exit0=97、exit1=79、timeout0、合計計測3.087秒。うち初回36件は未定義operatorによる無効な準備試験として分離。残る2つのhandler形の72件も途中観測として最終matrixとは区別。最終matrix36件とcontinuation対照32件は自己完結コードで、全コマンド・出力を以下に公開した。

- runtime-cycle-5-invalid-prelude.md
- runtime-cycle-5-primitive-handler.md
- runtime-cycle-5-let-handler.md
- runtime-cycle-5-effect-count.md
- runtime-cycle-5-controls.md
- runtime-cycle-5-continuation-wrap.md

rawにはcache writeのread-only警告も保存。成功exitだけを診断なしと解釈しない。途中のPythonスクリプト生成でSyntaxErrorが2回あり、修正後の実行を採用（その2回はYulangの176呼出に数えない）。最初の進行心拍に未計測の未来時刻を書いた誤りは、直後に時計の実測15:02:36Zへ訂正した。

### 境界・残件

Lean/spec/処理系ソースの変更なし、全体build未実行。dynamic demand slot provenanceはinstrumentしておらず、旧specializer単独行を確定原因としない。新しい意味論選択・質問ノートは追加していない。前サイクルの大きな未公開ログは別件として残り、本サイクルはその完全保全を主張しない。使用量計上不明。

実行は約8分で完了予定、25分上限内。最終の正確な完了時刻は心拍に記録。成果8ファイル（この報告、主張表、raw6）と心拍をwork/dots-auditのみに公開し、全成果を再取得して一致確認する。
