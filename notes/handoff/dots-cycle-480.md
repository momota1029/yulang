# dots cycle 480: G04 の局所存在と、累積入口・Audit の短縮設計

道具: モデル名不明、Lean 4.35.0、GitHub; 委譲: モデル名不明、1 回、task `/root/yulang302_resume`（追加委譲・Codex thread なし）

**I-96 の `G04Producer` は、定義された範囲で証明済み。G04 全行は未完、残り 20 / 24。** 一つの関数を与える形と、正確な prior phase がある各独立 event に忠実な有限 wire が存在する形を、古典的選択で同値にした（`g04_producer_iff_eventwise_exists480`）。既記録 authored 順と既に対応づけられた release はそのまま再生する。未証明だった一箇所は、**順序未記録の authored event から、実 root を先頭にし、同じ独立な `Read` を保存する finite raw/author 列を作ること**。元 raw・元 author の実位置を使い、残りの authored facts を拾い、旧 `Read` の有限 footprint を輸送して埋めた。三分岐から `every_qualified_event_has_a_faithful_finite_wire480` と `g04_producer_proved_scoped480 : G04Producer` を得た。今後の `(h : G04Producer)` にはこの定理を渡せる。実処理の順序を復元する証明でも、compiler 側に生成機能を実装した結果でもない。I-96 のとおり、その実装は A の存在証明には要らない。

**残る一文:** I-83 の既存累積入口に、元 `Pose` と最小型商の正負を持つ I-93 の正確な報告を結び、同じ `check_full_sound` の外形で source の根拠まで反映する枝がまだない。C459 の現行 `.fieldK2` は旧 raw `AliasCycle` の正の枝で、I-93 の報告型は違う。既存の `selected_unrolled_sources_have_no_raw_cycle_but_exact_quotient_k2476` は、実際に raw では戻れない場所にも型商では K2=true があることを示す。今回の `ScopedRouteSound480` は data-only route の成功から、元の宣言 ordinal、元の構文位置・旧 raw の実経路、終端と正負まで独立に反映する。ただし局所 geometry adapter の成功だけを author 又は release の発行証明としない。独立 event と正確な根拠がある場合に同じ `FitsFull` で使える有限証拠は揃ったが、累積側の三条件は別。接続では、選んだ引数だけの安全性で要求全体の root 優先を代用せず、局所の K2=false を選択済みという意味にしない。全 NoFalseRejection A や solver 停止は未証明。

**短縮の設計:** `notes/design/dots-cycle-480-proof-compression.md`。C459 から C447（その下は既存 C446 への委譲）までの実 dispatch を一つのタグ付き入口へ写す対応表、G00–G03 と元 C 試験・依存の対応、Audit の共通化、全入力の Bool／exact report／同じ Fits の検証手順を記録した。I-65 固定声明と各旧 `check_full_sound` の外形を変えず、既存の失敗も保存する。今周は整理の設計だけで、**短縮実装も削除もなし**。削除は別承認後。新しい意味論の判断は求めていない。

## 対象検証と引継ぎ

- Lean 4.35.0 の独立対象検証（--trust=0 -DwarningAsError=true）で標準範囲内の結果 7 件、新しい実行ガードなし。新規 production 5、独立 Audit 5、既存集約は import 5 行だけ追記。I-94 の公式・単語境界の追加行検査に違反 0。集約を含む Lean 11 パス、設計・引継ぎ・heartbeat を含む全 14 パス。既存本体は変更なし。今回の Lean tree `2852afb6ae0882c04a6c08df0d45cf652a24d36e`。
- 権威 `68a3ab36cc67cc11fb0882fb1bd8c44559905fcf` が work の祖先と確認。実開始 `2026-11-28T03:25:55.000Z`。+10 `19ac37e0093305e4703744af7f612e8dcbe5e6a0`、+20 `4e9e6df380a063aea4fc086791d329e5055551dc`、+30 `4f309f53270d4cfc6019e5197e640dad78ef0e71` で Lean 凍結、+40 `e4a7fa20700feffb3398f19f46a13222970ca0d5` は heartbeat のみ。開幕に C479 の Lean の完全な採用と I-96 を確認し、それ以後の inbox は変更なし。+20 は同じ短縮設計ノートの対応表の精密化だけで Lean 不変。追加 import の組合せも対象検証済み。全体の verify-lean.sh と Lake build、および Yulang2 実機は dot では未実行。作業者を解放し、次回は最新 inbox を最初に読む。具体的なモデル名・使用量は不明。
