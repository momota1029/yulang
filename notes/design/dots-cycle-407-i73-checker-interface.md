# I-73: checker の接続口の調査（実装は未着手）

固定 I-65 §2・3 と I-73 を読む。R₀ の integration 掲載が完了の判定であり、この調査はその判定を先取りしない。既存の各 checker を起点に、固定 Problem・Result・Witness との接続で何を同一としなければいけないかを整理した。

| 既存入口 | 同一 state/root で再生できるもの | 足りない接続 |
|---|---|---|
| `GeneralDeclarativeWitnessCycle350.check / rooted` | `p.state.core.current.ordinary` と `p.root.demand` を直接渡す。元の引数番号から始まり、名なしの構造下降を1回以上行って同じ alias class に戻る証拠。Witness は data-only `Wire`。 | 固定 Result の diagnostic tree と verdict がともに rejected、固定出力 receipt が空なのを一緒に比較する。C402 `SourceTrace.rootK2` と直接同じ述語。旧 pending manifest は不要。 |
| `GeneralDeclarativeWitnessWhole350.check` | 独立に compile した宣言表・manifest・元の demand から scoped tree と固定 equation を再生。 | 同じ元の occurrence と入力/出力子順、source table、ordinary state とすべての child layout へ結び付ける。成功の意味は旧 `ExactDictionary337.Evidence` で、同じ root/dictionary に見えるだけで固定 C402 `Classifies R₀` を得ない。 |
| `GeneralDeclarativeWitnessRecordWhole350.check` | 同じ旧レイアウトの record 用枝。 | 現 R₀ の正の source head は直接変数か authored unary のため、record head を含む旧成功を丸ごと承認してはいけない。固定 R₀ に落ちない形は false。これは言語拒否ではない。 |
| C351–356 の tagged/covariant/mixed の scoped checks | 検査済み宣言表・出力・root/child ordinal など、同じ Problem に結べる有限データは再利用可能。 | solver の completion/release は R₀ の宣言側完了ではない。R₀ の有限同状態 `SupportForest` と元 B6 receipt を反映できる枝だけ通す。R₀ 外の形（C402 の固定証拠を持たないもの）は false。 |

`GeneralDeclarativeWitnessTree349.Report.outputs : List GeneralSourceState.Output` は要求名/固定先の確認で、C402 `Ledger.written` の元の出現・番号・body・型付き右辺の一致ではない。`Tree349.eqTree/eqResult` は再利用できるが、`Tree349.agrees` だけでは固定 I-65 ReportEvidence の出力条件を検証していない。

次の実装順: (i) Problem から取り出した同一 State/元要求に root raw K2 の既存 Wire を直結し拒否 tree と空の実書込みまで照合する。(ii) 元 B6 lookup・元の実子位置・全元出力の有限な data-only wire を canonical に比較できる、実際に R₀ の選択根を生成する既存枝を加える。(iii) hash やモデル値で receipt を代用しない。関数値を含む `NamedMixedReceipt401.slots` 全体の比較を先に要求せず、実際の型木の参照先を決定データとして照合し、原文の型木を意味に保つ。証明を witness に入れず replay が求める。判定不能な枝は false。

経路調査だけ。統合 checker も check_sound も未実装。