# Yulang C398 I-70 中間引き継ぎ（通常完了ではない）

閉じた補題なし・分けた補題なし。

[設計と実 source の根拠](https://github.com/momota1029/yulang/blob/d5ee50dc88ea477c54bf682bd45eca1e4729bcc4/notes/design/dots-cycle-398-b4-symbolic-source-substitution.md)。B6 が渡す記号的 typed Body は、実選択前の明示／role default の元 source site に対応する。B4 は元 impl から `Supplies` を lookup し、その Body の計画のみに actual lexical/positional slot を代入し、元出現・元 `Fin` output ordinal・固定 target を保持した論理等式を作る。B6 metadata の有無で明示/default を選び直さず、不成功の位置も ledger から詰めない。value/row と point/invariant interval は元計画のまま。B4 で式の型を推論し直さない。

旧 ordinary の literal 経路は混在 wire から独立。B6 の同じ元 `translate` による記号的 Expr を読み、B4 が C393 の実 capture を代入し、同じ raw ordinary 等式を得る。明示 RHS の実 slot 存在は `Declaration.Scoped` と実 frame の capture table、default は元 role の scope と actual arity による。[Lean source](https://github.com/momota1029/yulang/blob/a5f0a227d4f8425f1d56839ce6e939fdb28905ed/lean/Yulang/GeneralDeclarativeI65B6OrdinarySource398.lean) と [独立監査](https://github.com/momota1029/yulang/blob/a5f0a227d4f8425f1d56839ce6e939fdb28905ed/lean/Audit/Cycle398B6OrdinarySource.lean) を検証して掲載。実 receipt の occurrence・ordinal・固定 target と、成功した slot の元 `bodyCapture` との一致、および well-scoped な明示 RHS の全 lexical slot を証明。ordinary の入力は同じ元 code の変換結果で、B6 coverage や全 Classifies の producer ではない。

[B4 型つき論理置換](https://github.com/momota1029/yulang/blob/f514c8b292c42328b7e0c4266e679038e19454c1/lean/Yulang/GeneralDeclarativeI65B6SymbolicSource398.lean) と [独立監査](https://github.com/momota1029/yulang/blob/f514c8b292c42328b7e0c4266e679038e19454c1/lean/Audit/Cycle398B6SymbolicSource.lean) を追加。B6 から元 Body に対応する plan と同じ State の実 slot の kind 適合性が与えられると、実 supplier を選び直さず、C394 の構造的な source 関係を満たす論理 RHS を、元 output 位置・固定 target のまま返す。逆向きは既存 C394 がすでに表現した RHS の範囲で、同じ slot に対する正確な再現を証明。未表現箇所で default を試さず、出力位置を詰めない。元 Body への対応は正規化済み Pattern の source で、未決の mixed literal wire ではない。B6 の実入力供給と全 Classifies の slot kind 接続までは証明していない。

[where の接続](https://github.com/momota1029/yulang/blob/c19176a9dcb476f233e0cedf6b53851a3fcb328e/lean/Yulang/GeneralDeclarativeI65B6WhereComposition398.lean) と [独立監査](https://github.com/momota1029/yulang/blob/c19176a9dcb476f233e0cedf6b53851a3fcb328e/lean/Audit/Cycle398B6WhereComposition.lean) では、与えられた子 frame の B4 出力を、元 where の子 occurrence・出力 ordinal・要求された固定 target で同じ位置に接続。その位置の有限選択証明と dictionary も、元の forest の同じ子から取得した。ただし occurrence 一致だけでは、与えられた子 frame の宣言が有限選択証明の選んだ宣言だとはならない。この接続は一般の選択判定や B6 の供給健全性を代替しない。

混在 `.declared` は既存質問の回答待ちで保留し、再質問しない。B6 の入力 coverage/型付け健全性、全 Classifies の実 source frame とその出力の exact literal 対応が残る。S13bbbb、Steps 2/3、旧 Local/C334、fixture、停止性は対象外。S13bbba は未完・未分割、**14件 = 未証明3 + 一部11**。固定文と一覧は変更なし。

## 照合

Lean 4.35.0 (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`) で、immutable GitHub ref から再取得した新規三 source と、それぞれの standalone audit を `lake env lean --trust=0 -DwarningAsError=true` で別ディレクトリに再構築・再検証。全部 exit 0、16 定理の公理は `propext`、`Classical.choice`、`Quot.sound` の範囲。追加三 import の同時 import も同じ strict オプションで exit 0。リポジトリ全体の build や Rust は未実施。全変更の差分と本文、barrel の既存全文不変＋三 import 追記、凍結二ファイルの blob ID、固定 theorem/一覧の blob ID を照合。 実開始 `2026-11-24T17:35:28.025Z`、照合開始 `2026-11-24T18:21:44.242Z`（46分）。予定枠の上限内には実50分の完了ゲートに到達できないため、この照合済み中間地点を引き継ぐ。通常の最終報告や completed 心拍は作らない。
