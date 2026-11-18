# cycle257：実 I45 family の有限 journal 観測と初期境界

開始 2026-11-18 13:27:08 UTC。50分を経過後の14:17 UTCから最終報告。
前回cycle256の公開状態とwriter停止を確認し開始。最新 integration は
`f894530e18ba3e50f5ed0c593a44493382ae0c40`、I50 ACTIVE、上限なし。
開始時33cf8d490から変わったのは監督役による既存254監査のimport修正などの統合で、standing orders/inboxは不変。
統合時は監督役の `Audit/Cycle254Full.lean` 1行削除をそのまま採用し、旧数学Leanは変更せず、barrelは追加分を維持した。

## 成果

25新規数学module、171明示宣言。各量化子・前提・日本語の個別説明は
[宣言案内](../verification/cycle257/declaration-guide.md)、全elaborated型は
[型一覧](../verification/cycle257/alltypes-final.txt)。一覧の全171件と順序を照合済み。

1. 実到達I45 familyの全段階nについてlower/upper定義blockを実ordinaryから取り出し、全過去展開を計算した。16n個の累積ordinaryを、重複縮約後は初期空・正段階4種類の事実に正確に縮約した。一般の分配的正規形ではない。
2. 当前rawの型観測を5slot・最大8ordinaryのViewへ縮約し、Known/PointAtと当該packet Reportの運搬を証明した。元stateはn+5slotで、投影は非単射。有限Viewだけでは旧反復を止められない。
3. raw Modelsからjournal Modelsへの誤った強化に、実到達state上の明示assignment反例を構成した。固定binderの条件2atomを残すと、このterminal familyでは正段階n+1で同一assignmentの `journal Models ↔ raw Models ∧ binder Holds` を証明できた。したがって5slot・最大10ordinaryの有限Viewでjournalの意味を表せる。ただし無条件同値の右辺は `solve(history(n+1)) assignment`。公開射影は初期0〜4・実binderの全Compと全rowを固定する存在モデル同値である。

**重要な制限:** history再構成は依然増大する。実state/証明書のサイズ有限化、新Step、一般sourceのpool閉包、I50出力依存深さ、非流出、Accは未証明。空child/outputを用いた特定familyの証明を一般packetに拡張していない。固定binder条件は内部証明書であり、public aggregate basisにprivate名を加える許可ではない。

さらに初期段階を除く必要性を2つの追加exampleで確認した。初期journalが満たす具体的seedを有限View(0)は満たさない。したがって上のn+1制約を削る命題は偽である。これは新しいプログラム拒否・言語意味変更ではない。

## 検証と監査

- `LEAN_PATH=lean/.lake/cycle257-final ../toolchain244/bin/lean --trust=0 -DwarningAsError=true ...` により全25本を新規cacheで再build。14:02:07〜14:03:09、exit0。[全文](../verification/cycle257/final-build.txt)。
- `timeout 5m python3 -u notes/verification/cycle257/rebuild-final-critical.py`：実依存層240〜257の193本を別の新規cacheで再build、14:10:04〜14:14:00、exit0。[全文](../verification/cycle257/final-critical-build.txt)。全25本を含む。先行182本の実行も成功。古い残りの依存は再利用であり、全1615本を再buildしたという意味ではない。
- Complete / Full / Usage / Types / AllTypes / Reachをfresh193 cache上で再実行し14:14:27終了、全6出力が先の最終監査とbyte一致。171明示宣言、生成/privateを含む296宣言、標準propext/Classical.choice/Quot.soundのみ。Usage29example。Reachは選択17rootから150/171、残り21は別の境界・回帰結果で全件監査対象。
- `InitialBoundary.lean` の追加2exampleは同fresh193 cache、strict Leanで14:16:08 exit0。[ソース](../verification/cycle257/InitialBoundary.lean)／[結果](../verification/cycle257/initial-boundary-check.txt)。独立読取レビュー後の追加検査であり独立レビュー済みとはしない。
- 全依存1615file/2755import行のhashを照合。旧256の1593file、旧255の1549file不変。旧数学Leanの凍結とbarrel追記を確認。唯一の旧Audit変更は最新統合版とbyte一致し、strict再検証済み。[検査](../verification/cycle257/source-check.txt)。
- 全25数学moduleを4回（8+6+4+7）独立読取レビューし問題指摘なし。独立再buildは未実施。[自己点検](../verification/cycle257/self-review.md)。
- **全体lake build、verify-lean.sh、Yulang2実行は未実施**。全体検証は監督役へ委ねる。work/dots-auditの公開記録を読み、旧runtime結果を今回の証明のoracleとして扱っていない。[spec/runtime照合](../verification/cycle257/spec-runtime-check.md)。

## I50に対する位置づけと次の穴

正規化された観測・共有binderを残す必要性について、実到達familyで強い局所結果を得た。一方、一般sourceのI50受け入れ条件を完了したとは報告しない。

1. `VersionedPlans231.Holds` の各consumer（historical raw、ProjectionModels、input site、mode-sensitive schema、child、live effect）を覆う有限証明書の閉包。普通のsubtype atomだけでは不足する。
2. growするhistory再生なしでprivate値を復元する表現と意味保存。public owner identityへprivate名を戻さないこと。
3. I50出力依存グラフのsource起源・加算深さ/K2境界を示してから、新しい厳密progress関係とAccへ接続する。旧非停止Stepを有限Viewだけで停止化したと言わない。

[設計・consumer分解](../design/2026-11-18-cycle257-full-history.md)。新たな言語意味判断を要する質問は積んでいない。明示反例は誤ったraw→journal強化と初期段階の境界を対象とし、既存定理や新kernelの反例とは混同しない。

## 公開・時間・制限

数学25本は `f6728cc509077f99a778fbdda37795efe92556d3` から不変。
検証・最新integration取込はe0cf46d9、193本再検証は6c3f9494、初期境界は
`424a99f892f0cd1361d2b93609940f54b57f9627` に公開し、14:16:59にfetch/tree差分0を確認。
最終報告とinventoryの公開後の照合結果は [publication-receipt.md](../verification/cycle257/publication-receipt.md) に記録する。
研究・検査成果82file、報告とinventoryを加え84file（前cycle256基準）。receiptを加え最終85file。
心拍・checkpointを継続し、公開先はwork/dots-mainのみ。使用量の残枠は不明。
未追跡の過去recovery/lockは今回成果に混ぜず、触れていない。未完の一般停止性を成功扱いしない。
