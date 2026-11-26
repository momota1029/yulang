# C432: 同じ State の元 Wrap→Container 実選択木と固定書き込み

独立局所規則 `OriginalAssociatedWrap432` は、元の invariant list head、元 capture、実可視リスト、raw K2 の根、元出力専用 binder、実 B6 plan と元固定 row を検査条件とする。モデル・成果値・辞書・子の選択証明は局所選択の前提に含めない。既存 R15 の選択規則/endpoint と合わせた提案カーネルに `dictionary_sound_for_associated_where_kernel432` を証明した。

実 fixture の親は Wrap(list a, out=list b) の保持済み原 head、子 Container(a,item=b) の確定した元 clause 0。既存 public checker が選んだ元 Event と型つき child writeを、同じ State の SourceTrace/WhereForest にそのまま接続。親 target 12 は list(assignment 4)、子 target 4 は item の元 read。実適合モデルも存在。記録順は親の元 receipt に次いで、元 where 順の子 receipt。この順序は表示の走査順であり、solver の実行順とか安定化の証明ではない。

この監査は宣言的な実親子を一本で構成するが、親の公開 R16 witness/check branch を追加していない。親 frame と b の保持先はここでは、実 B6 / graph と照合した独立な固定証拠を用いる。次はそれらを公開入力の data-only witness から原始資料を見て失敗時 unsupported に保つ読み出し。C16 の公式行はまだ数えない。