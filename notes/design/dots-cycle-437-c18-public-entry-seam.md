# C437 / I-79: C18 を公開 entry へつなぐ残り

C437 の検証済み技術 pin は `ed7e39f81d521b556dd37962b3b4baa5cb9b2351`。ここでは source-backed Seed と Observe の実 scoped 証拠まで通った。**R18 の宣言側をインストールしたわけではなく、既存 check の分岐も追加していない。** C18 は未完了のまま。古い source に変更・応急 alias を入れない。

| 次の実装点 | そのまま使える検証済みのもの | まだ必要なもの |
|---|---|---|
| 元 producer の proof-free input | `CompletedNativeHeader437.checkedHeader` は native scope と旧署名等の全検査を保持。`CompletedSeed437.SeedBasis.origin` は実 singleton tape と元の宣言番号を結び、`readOneOutput` は actual typed output と raw row locator から finite support を返す | 外から与えるのは locator と元 request 情報だけ。source metadata、key/mode、origin の同じ occurrence、point input、raw root escape から `SeedBasis` を計算する。元 B6 本文は `readOriginalOutput432`（実 body lookup, atlas, substitution, exact raw row）を使う。fixture proof や selected result を witness に入れない。 |
| actual consumer の独立選択 | `CompletedUnaryGate406`／`PreselectedUnary406` の真の same-State 実例と model proof は Audit 合格。`readCenterAt`／`buildEmptyInvocation` は実 locator、issuer、範囲を確かめて同じ選択を scoped invocation にする | consumer 原引数の root raw safety を**最初**に調べ、後続の source 限定・candidate checks・実 upper origin/endpoint/types の read から Gate を組む。selected support は上の result だけを使い、同じ target-name／actual typed point／declared mode／比較 atom を読む。center はその後。凡例の singleton unary variable child, no where/output の場合だけをまず扱う。 |
| R18 と I-65 | `lower_retention_uses_original_B6_value437`、`exact_support_preserves_one_model437`、`exact_empty_invocation_reads_original_capture437`。既存 R17 は完全に手付かず | 新モジュールで旧分類＋独立した新 rule／旧辞書証拠＋新 head evidence を加える。旧 `classification_has_exact_lane_rule426` は旧二枝を全称で尽くすので旧型を in-place で変えない。高層で実同一 `SourceTrace` と typed receipt の索引を保持、lower payload に逆依存を加えない。exact I‑65 量化・前提・結論で `dictionary_sound_R18`。 |
| 公開 checker と strict 検査 | 同一 raw への対照は official Lean で検証済み。元 q では原 source/center、raw row 一行追加のモデル未仮定側では root K2 | data-only 新分岐と、旧 `.previous` の全入力 Bool 定義等式、同じ外形 `check_sound`。producer は consumer where child でも再発行 write でもない。元 root raw K2 の枝は旧関数を変えない。正負の実 use を public entry から通し、scoped の証明だけで閉じたと言わない。 |

**焦点を絞った再開:** C437 では必要な既存 94 production を strict 個別再生した。これを再使用できるなら、正本 `fdab2230…` 上で `PendingAssociatedEntry434` と `StructuralWhereOutputRead432` までに増える依存を source import DAG から数えると 182 production（先に検証した 94 本は除く）。この 182 本は source blobs/依存の確認のみで、当周はコンパイルしていない。既存キャッシュが保たれる場合に exact path と hash を検査して最小 closure の strict ビルドを行う。全体 build、Rust 確認、C19、solver witness producer の完全性や停止性に広げない。

