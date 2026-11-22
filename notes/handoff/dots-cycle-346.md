# dots-main cycle 346: where 入力の物理スロットと版の出所

- 開始 2026-11-22 13:33:21 UTC。指示元 `593a1441a382b4bb1c454bb912e2d4b6e095a63b` と C345 完了 `3d7915a31136306b1e62eac6ccee23c55db458e8` を先に確認。standing/inbox/spec 6・10/B4 草稿の blob は前周と同一。I-62 に従い旧 `Local` 対応は復活させない。途中の executor 切断後、同一の承認済み Yulang 環境へ接続して検証を継続。

## 検証した主張

1. **物理 where 入力を生成する小さなコンパイラ。** scalar・pair・record（名前付きの tail を含め、全オペランドが物理スロットとして引ける場合）・variant・join の意味を、どの割当てでもそのまま raw `TyTerm` に移す。実際のモードの名前を使い、順序と重複込みの読み列を物理スロット列に一致させる。構造断片と全参照スロットがそろう場合に出力が存在し、足りない場合は成功を捏造しない。nominal 自体は既存 `TyTerm` のコンストラクタではなく、ここでは拒否を返す。この拒否は補助コンパイラの表現域であり、Yulang の受理規則ではない。
2. **RawTicket の導出。** 各実 `Cell` の target スロットに二方向の raw 制約を追加すると、正確にそのモードの実 materialized equation と同値。対象バッチが現 layout の同じ名前を読み書きすれば、旧モデル＋実 packet から正しい deferred 物理拡張の RawTicket が従う。出力 Ready、同値による再ターゲティング、未実在のスロットは使わない。C319 では fresh lower の実 atoms を厳密に生成し、active context と同じ raw モデル条件として再現。旧 upper を新規書き込みには数えない。
3. **実再観測と履歴。** 任意の実版付き `InstallStep` の compound Cell について、節の canonical 番号、物理子番地、引数番号、極性、target と journal stamp を取得。C319 の実 nominal 再観測は基底の物理名を変えず、旧 stamp #0 に由来する upper の構文・版・オペランド順・モードを保つ。一方で記述子は狭まるため、旧記述子を意味でなく同じ構文として保存する `Refines` はこの例で成立しない。versioned store の保存はそれを前提にしない。
4. **非点と独立支持。** 両端は同じ実子の物理引数に対応し、center はその子の実 center として保持。C319 の旧区間は真に非点、現区間は別の物理端点IDを持ちながらこの例では意味上の一点で、一つの実終モデルで確認。普通式をモデルが満たすことと、入力観測に使えることは別。完成した所有者に加えて、使う版・物理子・引数・極性そのものの release 証拠を渡す版では、同じ ownership だけで旧行を使えるようにはならない。C319 の fixture では二行とも成立しても指定された現行だけを使う場合を検証（fixture の release 指定は言語の新規規則ではない）。任意の実 compound Cell について両端と center 間の実 bound を普通ビューへ移し、両実 release があれば同じ支持付きビューで両端の EquationRead を得る。
5. **名付き nominal は別経路。** 実物理名が指す登録済み descriptor に対し、型の tag と全 point 型引数の実名列を照合し、任意の正当なモデルで同じ nominal 式になることを証明。nominal 内では外側の極性を引き継がず actual 名だけを読む。C319 の実再観測後の root descriptor は現 `[2,2]` を確認し、旧 `[4,2]` の物理並びを拒否する。現 descriptor の読出しと元の独立した入力ラベルが同じリテラル行を与えることも、完成済み出力を一つも許さない設定で確認した（`WhereNamedSource346.independent_at_actual_point`）。未登録 descriptor を追加する手順や非点 nominal 引数の完全性は対象外。
6. **元の実行器に対する境界。** 元 C316 の停止 root は出力 Ready でも、修正版の上下両方の物理作者アドレスを raw layout に持たず、新コンパイラをそこで走らせても atom は作れない。旧 lower 行への fallback はしない。C319 の成功は、実 native nominal 再観測を挟む版付きの隔離試作に対するもので、元の実行器に producer が存在するという証明ではない。

## 残り

- **(4) 1群**：I-61 の一般の独立支持つき nested/compound・open/closed/nonpoint 読みを最新の証人つき分類に接続。今回 source-backed release は前提を明示した。式の lowering、普通モデル成立、物理スロット存在だけからは出せない。登録済み point nominal の読出しは別に閉じたが、nominal descriptor を新たに生む一般 producer、非点／row引数 nominal はその範囲外。
- **(2) 2群**：① 任意の native 成功停止から実現行の clause/arg/mode/version に対応する物理入力 producer・独立支持を取り出すこと（C316 元 root はこの証拠を欠く）。② その結果と最新証人つき分類／診断／順序付き辞書をつなぐこと。次は「実 native event がどの時点でその作者証拠を生むか」を観測・履歴契約として切り出し、C319 の隔離証拠を native のものと混同しない。並行して、named nominal source を実 descriptor で読む独立 fragment を進める。
- 質問ノートなし。実行器や意味論の変更、停止性、Rust 実行、全体 Lean ビルドは主張しない。利用量は不明。

## 検証と公開

- 証明固定点 `e0c2f839b07caccf162d39478ad50d71acd1df36`。Lean 4.35.0、24 新規モジュール対象の `lake build --wfail` 成功（依存 3542 jobs）。固定 Git tree の detached exact bytes で24 ソースと 6 独立 Audit をそれぞれ `lean --trust=0 -DwarningAsError=true` にかけた。52 の名前付き宣言（うち1件は公理なし）と、scope の非プラットフォーム宣言 103,204 件の公理を検査し、許可標準公理以外なし。
- C345 以降の証明固定点の39変更パスを全バイト照合。差分検査（凍結除外、ビルドなし）成功。既存 barrel の 325,778 bytes は同一、末尾の import 24 行だけを追加。凍結2ファイルは前回・指示元・作業点の blob ID のみ確認し、内容は読まずに比較。
- 記録: [focused Lake](../verification/cycle346/focused-lake.txt)、[固定ソース・独立監査](../verification/cycle346/exact-trust0.txt)、[名前付き公理](../verification/cycle346/exact-named-axioms.txt)、[scope公理 gate](../verification/cycle346/scoped-axioms.txt)、[差分チェッカー全文](../verification/cycle346/diff-only-full.txt)、[限定構造 smoke](../verification/cycle346/structural-smoke.md)、[次の source/descriptor 境界](../design/dots-cycle-346-next-input-source.md)。
- 最終公開開始: 2026-11-22T14:23:23.399Z（開始後 50.03 分）。対象は `work/dots-main` のみ。integration、実行器、spec の意味は変更していない。
