# C459 / I-86: 元 head の同一 tag 重複と、訪れない pair 成分の切分け

G04 のみ。C458 は統合の Lean tree と一致。spec §6.3 の duplicate tag（統合の L111）・非変数 inspection (L495)・nominal body を開かない (L500) を変更しない。

- 元 visible singleton の宣言番号・元 head/where・署名・scope・実 query をそのまま得る。字面まで同じ variant の重複を除いた **補助** head の有限 check から StableSmaller を得るが、すべての capture 後の original normalize/count と同一なので、DeclarationReady は元の宣言に対して回復。異なる同 tag payload を勝手にまとめたり、join を訪れたりしない。
- 通常の C458 raw trail と、実 unary declared covariant point nominal の後に実 pair 第2成分を通る限定 trail を区別。後者は実 raw 子・両元 origin/route・同 issuer・既存 Alias・全 selected source term の字面を照合して、pair shell 第1成分を開かない。第1成分に推論された int|str があっても新しい graph edge は作らない。
- 元の通常ヘッダと補助投影ヘッダ、比較的狭い二つの trace を一つの累積入口から照合。新しい場合の独立有限導出から同じ original report のデータ witness を再現し、逆方向と任意の同一 FullState 適合モデルでの soundness を証明。旧 C458 witness Bool は全入力で完全委譲する。
- 実対照: 通常／厳密重複／未訪問 union／二つの同居。同じ State の真正 fitting モデルと正しい終点。異なる duplicate payload、誤った pair ordinal、元の metadata・報告終点を照合し、未支持はこの checker の未収録扱い。open tail は G06/G07、nonpoint/general modes は G20/G21、G05 へ進まない。任意の元 inline/bound pattern と上流 carrier の全面一般化ではない。
