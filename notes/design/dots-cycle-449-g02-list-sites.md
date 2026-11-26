# C449 — G02: 独立な実調査位置と有限 raw K2 証人

I-83、正本 integration/m1-final@48926909d6d38edf13ea0dead90d673417b3aaf4。spec §6.3/§6.5: raw K2 は根または非変数の head が読む場所の実循環。名前付き body は開かず、単なる binder の payload は新たに調査しない。今回 where 子・一般候補は対象外。

- 独立 `WrittenListSite` は実入力の位置・元 authored origin・宣言された invariant value mode と元 plain binder の捕捉。 `ListFrameVisits` は書かれた head と入力順に根を積む。binder は payload を保持するが調査位置を足さない。
- `checkSiteTable` は実位置順に有限の split 証人だけを zip し、余りや不足を拒否する。各位置の正確な raw AliasCycle 不在とその有限表の存在の両向き。元の unfiltered raw graph で有向 Bound の grade と単純 Alias の側を分ける。
- 公開入口 `check_full449` は C448 をそのまま委譲し、一つの元 list-binder 宣言について新しい形式から既存の独立な local choice と元の report を同じ FullState で再現する。モデル・判定成功は choice 側の前提ではない。元 R2 報告の意味を変更せず、同じ Fit 全モデルの定理を示す。一般の site family と、この実行入口の実装範囲は区別する。
- 対照は同じ元 raw graph の多枝、片向き Bound、flat Alias、調べない payload にある実循環。根に戻りを加えたときの実 AliasCycle で新 branch を拒否する。全グラフ rank・戻りのない payload の検査を使わない。

## 同じ C449 の実装結果: 実 list 入力列

- `AuthoredFrame` と `ListFrameChoice` は、実可視候補一つ・where/要求出力なし、異なる binder の実 list-binder head の非空入力列を扱う。元の候補、入力順、authored origin と role、宣言 mode、各実捕捉、全根の raw 安全性を持ち、checker やモデルは前提にしない。
- データだけの `FrameWire` は origin index と有限の cut を位置ごとに渡す。`OriginOrder` と nth cut の反映で、各 wire の index と cut が同じ実位置に対応する。複数位置でも全グラフの rank 不要。実 Event、元の辞書と書き出し列、全 FitsFull モデルを保つ。
- 正式な累積入口は `ListSites449.Frame.check_full449`。旧 C448 までの witness を不変に委譲する。 `exact_frame_wire_iff_independent_report449` と `check_full_sound449` は同じ FullState の独立選択・正確な報告の両向きと健全性を示す。
- 実例は根 [0,5]、捕捉 11→1・12→6。別々の cut を対応させ、未調査 payload の循環は妨げない。第二の根だけへの本物の alias return、payload を実際に第二 head として読む場合、cut/位置の改変は新分岐で通らない。別の where、繰り返し binder、任意の構造 head は含めない。
