# Yulang cycle 396

閉じた補題なし・分けた補題なし（I-69 の S13bbba のみ）

## 元 where 出力から型種を得るための設計

[設計と対象ソース](https://github.com/momota1029/yulang/blob/ee881865bcf9b626135d09940452c1e3f9200d4f/notes/design/dots-cycle-396-selected-child-body-origin.md) を確認。C395 で照合した同じ parent の元 where clause/output ordinal から、実の子部分木を読む。元 child request の output 名が宣言済みであることは親の実 Clause.Signature から、元 child の宣言 ID と role は実 subtree の literal event から得る。この二つに既存 `declared_covered` と `lookup_exact` をつなぐと、子が選んだ元宣言の explicit Body（なければ role default）を、子の出来上がった receipt やモデルを使わず同じ位置で得る。default の変数は元 role の `defaultsScoped` と選択 head の arity から元 demand ordinal を読む。元 capture の数値と一致しても、named lookup にはしない。

**実 writer の境界。** 元 output binder の where equation は同じ名前の変数なので、C327 の `entry` はその式に `some []` を返す。親が子のために別の自己等式を出さない。さらに C350 の ordinary where/fixed batch の後段は `State.equations` を足すだけで、準備後の `State.normal` を変えない。既存 signed atom を使うのは構わないが、書き込み成功や point の reflexivity だけでは C366 の型種証拠を作れない。一方、すでに独立に構成した WrittenBody の C330 `Receipt.constraints` は、実 preparation の normal atom を同じ current State に移せる実所属の包含。全 raw equation/interval の包含（Extends）と同一ではない。詳細は最初の設計メモ。

**経路を保持する場所。** C367 の DeepHead と ordered head の All₂ は Prop で、証明自体は元 ModeWindow/DeepRead の値を識別しない。既存 authored_node はさらに shallow projection で DeepRead を落とす。全 Classifies の exact head を得るには、独立した source rule が実経路のデータを消去前から保持するか、元 endpoints の一意性を別に示す必要がある。言語に合法な二経路が実在するという反例ではない。

## 検証・公開

C395 の Lean tree `2beb65360b182988cfea9131f450969b5ef647ad` をそのまま保持。今回の追加は immutable Git source と突き合わせた設計だけ。クラウドが offline で、今回の proof draft を Lean で実行していない。未検証の Lean は公開していない。exact nonforce expected-head の work/dots-main で、設計・心拍・報告の計3パス、凍結2件は blob ID のみ。全体 build・Rust・checker は未実施、使用枠不明。

## 残り

S13bbba は未完。**同じ実 child の元 Body を、同じ独立 local rule が持つ型付き環境で評価し、その型種を元 where slot に渡す規則**、実 default/row の型種、任意 mixed compound と既存 .declared receipt の対応が残る。抽象 eventAt や同じアドレス・target・モデル値から逆算しない。言語上の新しい判断は見つけていない。新規受理・拒否・wire は定めず、S13bbbb、旧 Local/C334、停止性、fixture は未着手。

固定文と checklist 変更なし。**残り14件 = 未証明3（S01・S10・S13bbba）+ 一部11（S02–S09・S11–S12・S13bbbb）**。Step 1 未完、Step 2・3 未着手、C は後回し。質問ノートなし。
- 最終照合開始 `2026-11-24T16:22:46.853Z`（50 分経過）。
