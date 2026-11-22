# C337: standalone record 削除を actual capture と再帰辞書へ接続

## 仕様と範囲

2026-11-22 04:30 UTC 枠。開始 04:28:27 UTC。開始時と終了前に `integration/m1-final` の固定版 `61ad358f5e031f8295dc48c60400887e212083d0` を照合し、指定された standing orders・inbox I-61・spec §4.3/§6.5 を読んだ。開始 work pin は C336 `3c878eabd74db107b7db9d7f74c6d0a254de0c1b`。この周の checked proof pin は `a4dc88479763de5131e5c2eac1a274b754beec45`。公開先は `work/dots-main` のみ、expected-head / nonforce。

## 型推論の健全性

1. **mask ではない型付き削除。** `GeneralDeclarativeExactDelete337.subtract` は record spine 上の捕捉済みラベルを実際に取り除く。元の payload や非 record 成分を書き換えず、exact と width の閉開を保つ。元の有限観測を本当に存在しない照会に対応させる構成から、任意の観測深さで full carrier の部分型順序を保つ。上下端の双方が exactEmpty なら結果も exactEmpty と同値。取り除いたラベル自身への optional 照会は、standalone と mask で異なる。連続削除は `ExactCompose337.sequence` で、連結した削除リストの一回の適用に**型の等式**として一致する。
2. **由来と二つの端点。** `ExactDeleteAuth337.literal/canonical/supported` は、本物の `Read` 証明の lower・upper の literal spine から、それぞれ正規化・削除した端点を得る。全ての同じ現モデルで、actual center から計算した削除結果はその間に入る。上下端そのものを中心にせず、元 center の RHS も要求しない。 `ExactOverlay337.approved` は元の有限順序・名前割当のまま field と exact residual の投影を持つモデルへ拡張し、以前の名前を保存する。
3. **現 compiler と辞書。** `ExactDictionary337.local_sound/dictionary_sound` は元の `compileBody` と ordinary receipt を使う。同じモデルで、選定後 I-58 が各 occurrence の**実中心**を body が使う capture と同値にし、各 actual child と関連型の固定出力を再帰証拠へ輸送する。実回帰は親の出力 **6=11**、実子 **(13,8,14)** とその出力 **5=8** を変更せず、親の residual center が **exactEmpty** であるモデルと同じ辞書を確認。追加の exact lower 行 **10=endL** は証明付きの endpoint 由来であり、center 行や未完了出力を source に見せかけない。別の checked 回帰は反復 binder が実際に候補として選ばれ、tie 前はモデルあり、tie 後は exactEmpty と int の矛盾で **rejected** となる。旧 I-60 の成功証人木は `ExactCompatibility337.old_success` により、旧 mask の仮定なしで同じ木・順序・辞書として残る。
4. **入れ子の一段を実際にコンパイル。** `ExactNested337.compile_nested` は投影済み field/residual の認証された上下端が次の literal record spine を持つとき、同じ `Read → ready → prepare` を再度実行する。内側 pattern の変数順に名前を割り当て、古い足跡の割当を変えず、旧・新の全 projection receipt が一つのモデルで成立する。入力は実際に得られた endpoint 行・その由来を要求する。任意の承認済み compound pattern の normalization/selection からその前提が自動的に出るとはまだ言わない。

## 残り

- **(4)** 旧 I-60 の witness-based 辞書健全性は **0 群**。I-61 の追補は **1 群**。standalone 削除、literal 由来、既存 compiler の辞書接続、証明付き入れ子の読み直しは今回検証。残るのは、任意の承認済み nested/compound head の正規化済み source から、その capture・ordered receipt を同じ選定規則で作る一般の producer。証拠を新たな受理条件にしたり、未承認の優先順位を定めたりしていない。
- **旧 Local との到達可能な対応**は **1 群**。今回証明した前向きの旧 I-60 成功木の保持は、任意の実 raw/旧 Local への逆対応ではない。
- **(2)** 成功停止に限る部分正当性は **2 群**。(A) 実 raw 成功停止の各 occurrence から現在の source/出力 provenance と、記録済み・未 install 両方の実 receipt を得る橋。(B) 実診断木・辞書と同じ固定出力を一つのモデルに射影する全体定理。今回の parent/child は実 declarative compiler の結果だが、raw solver の成功停止ではない。停止性や Rust 実行の主張はしない。

## 検証と引き継ぎ

一時 executor が停止したため、認証済みの元 ref から作業用 checkout を復元し、公式 Lean 4.35.0 の配布 SHA256 を照合した。停止中の有限サンプルは［別記］(../design/dots-cycle-337-exact-deletion.md) の通り、補助的な機械計算であって Lean 証明とは区別した。13 の新 Lean module は focused Lake --wfail（1280 jobs）、全 source と独立 8 検査（7 axiom audit と依存境界）を trust=0 / warningAsError で確認。53 定理の公理は標準の propext・Classical.choice・Quot.sound のみ。範囲限定 gate は 65,803 宣言、境界検査は C337 の 283 定数から 5,800 件の型・値依存を走査し物理 solver 依存なし。別 detached checkout に固定 commit を取得し、13 module と 7 audit の exact bytes を再照合して直接 Lean 再検証。変更前後の git diff --check とリポジトリの diff-only checker も PASS。

`lean/Audit.lean` / `lean/README.md` は変更せず Git blob を比較。`lean/Yulang.lean` は元全バイトおよび Git blob を照合し、新規 module の import のみを末尾追記。各公開で変更パスを限定し、固定 commit のファイルを完全に読み戻した。全 repository の Lake/Rust build・実行は行っていない。

範囲と再現: [cycle337 verification](../verification/cycle337/reproduce.md)。次は、実 compound source が `compile_nested` の二つの endpoint・captured-pattern 前提を構築する橋を先に。特に、同一または異なる名前を持つ内外 binder の実 occurrence 順序と、where/output へ入る実名称を一つの読みで得る。次いで (2) の A の実出力 provenance へ進む。
