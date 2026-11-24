# Yulang cycle 395

閉じた補題なし・分けた補題なし（I-69 の S13bbba のみ）

## 実選択から source RHS への接続

- [選択済み head から型種を得る](https://github.com/momota1029/yulang/blob/2569050cec0c7f0eead7577b071645ee00de35e4/lean/Yulang/GeneralDeclarativeI65SelectedHeadBindings395.lean)。C367 の actual 完全候補 tape が選んだ visible index を、その順序を崩さず元宣言表の厳密な ordinal へ戻した。元 head 引数位置と C366 の実 DeepRead leaf 位置、元 lexical binder、value/row と lower/upper を同じ proof から読む。C394 evaluator がこの読み取りで元 Body と出力位置を使うため、実選択と無関係な capture 表を与えずに、表現範囲内で exact RHS を生成できる。旧 projection が定まる出力では、同じ元 occurrence・ordinal・Supply・fixed target の receipt を得る。未対応の入力は未検証であり、言語の拒否ではない。
- [元 where binder から同じ有限 child の辞書を得る](https://github.com/momota1029/yulang/blob/524ef2edd09449cd21644150d085c9c6f52db10d/lean/Yulang/GeneralDeclarativeI65SelectedWhereBindings395.lean)。元 Produced rule から実 clause/output ordinal と元 lexical point を選び、同じ State・元順の finite where forest から、同じ child request/occurrence の辞書と選択導出を取り出した。親の完成 RHS・帳簿・モデルを使わない。これだけでは、任意 child の frame とその selected local body の同一性や型種は戻らない。
- [実本体準備の後の value 読み取り](https://github.com/momota1029/yulang/blob/c6618dadf4d36938eba8c1a4a68f958cef638a70/lean/Yulang/GeneralDeclarativeI65PreparedSourceBindings395.lean)。実 C324/C350 の準備は center を同じ名前に保つ一方、下端・上端を両方 fresh にする。元の point literal は同じだが、元の invariant interval literal とは実際に異なることを証明した。実準備が生成した両端の双方向 value 原子を prepared state から読む。原子を同じ ambient State で読め、同じ一つの選択 tape・raw ordinal・actual native leaf に value の権限がある場合、準備後の実 port で C394 の型付き読み取りを作る。row を数値や value 原子から得ない。準備済み frame の where 順は実生成された C322 children と同じ。ここから同じ元 child の有限選択も取り出せる。固定 output batch を用いず、選択規則を変更しない。

[設計メモ](https://github.com/momota1029/yulang/blob/c6618dadf4d36938eba8c1a4a68f958cef638a70/notes/design/dots-cycle-395-selected-source-binders.md) に、初期 head と実準備後の端点を区別する理由、same-state で必要な条件、where 側との接続を記した。

## 検証

- 公式 Lean 4.35.0、exact `lakefile.toml`。新規 module 三件それぞれ `lake env lean --trust=0 -DwarningAsError=true -o …` と単独 import audit（六件・三件・六件）が exit 0。すべて標準公理 `[propext, Classical.choice, Quot.sound]` の範囲で、C383 forest 抽出は `[propext, Quot.sound]`。全体 build、Rust、checker は未実施。
- 公開した六つの exact source/audit blob とローカル Git hash が一致。public commit の固定 bytes から head・where の両 module の build と単独 audit を別出力で再実行して exit 0。第三 module は事前 build と単独監査が exit 0、固定 blob 読み戻し一致。クラウドが unavailable になり、第三 module の別出力再実行は未実施。 
- expected-head non-force の work/dots-main のみ。凍結二件は blob ID のみ、barrel は三 import の追記のみ、累積10パス。Lean 枠は不明。

## 残り

**S13bbba は未完。** 実 Classifies の全選択に対して、元の選択規則自身から、同じ本体準備全体と actual where/default/row の型種を得る source rule がまだない。既存 C386 の .declared は Pattern 全体を保つが、任意の mixed compound をその既存 literal write に対応づける元の生成規則も未了。別の平坦化や出力仕様を選ばなかった。言語仕様の新しい判断を迫る差異は確認していない。S13bbbb は未作業。

**未解決14件 = 未証明3（S01・S10・S13bbba）+ 一部11（S02–S09・S11–S12・S13bbbb）。** 固定文と最上段・checklist は変更なし、分割なし。Step 1 未完、Step 2・3 未着手、C は後回し。旧 Local/C334、停止性、fixture、受理範囲は扱わない。質問ノートなし。
- 最終照合開始 `2026-11-24T15:20:55.817Z`（50 分経過）。
