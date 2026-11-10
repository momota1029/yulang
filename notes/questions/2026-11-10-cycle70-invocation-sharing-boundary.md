# 再訪時の局所binder共有の境界

状態: 未決定の橋の確認。2026-11-10、I-13。意味論の変更は未採用。

spec/06-roles.md 6.3は、兄弟と親を更新ごとに再計算し、安定後に最終化する。
同じsource型変数に関連型の等式が流れ込むことも確定している。
一方、実装の候補照合が導入した局所binderの寿命を、再訪や候補の失活をまたいで
どうsource側の同一性に結び付けるかは、今の一般生成橋ではまだ証明していない。
番号やtableの形式を言語の仕様に固定したい、という問いではない。

仕様照合用の概形（parser/実機未検証）:

```yulang
impl Parent (box 'a) where Left 'a, Right 'a
-- Right の関連型等式が 'a を絞り、Left と Parent を再計算する。
```

cycle67の `CommonRoleFreshCaptureSources` は各captureで新しい需要名を作る。
cycle68/69の `CommonRoleRegisteredCaptureSources` /
`CommonRoleAddressedCaptureModels` は、同じinvocation/binderなら同じ需要名を再利用し、
過去の需要を残して全visitを一つのvaluationで満たす。
両方とも、それぞれの明示入力に対する定理はあるが、同じ元プログラムへの
adequacyを示したわけではない。特に異なる候補の制約まで無条件に蓄積するのは
既存cycle23/24のguard問題であり、この選択で解決したことにしない。

確認したい境界は、**同じsource義務の同じ候補を再計算する際、局所binderの
持続する共有をsource側の同一性として与えてよいか、それともfresh化と明示等式の
意味保存を先に導くか**。別のソース呼出し/別instantiationを共有する提案ではない。

1. **遅延案（推奨）**: 現在は両実装を局所部品のままにする。source側の独立な
   instantiation/再訪関係を定義し、同じsource制約を表すことを先に証明する。
   候補guardが変わる場合の履歴保持は既存cycle24の課題と一緒に扱う。
2. 同じ義務・同じ候補の局所binderを持続的に共有する境界を明記し、再訪時の
   制約が元のsource制約の保存的な追加であることを証明する。現在の構造アドレスは
   その実装候補であり、where順の書換えや別instantiationとの対応も別途必要。
3. 再計算ごとにfresh化し、元のsource変数への明示等式を生成する。既存sourceの
   全モデルと結果を保存し、不要な新名のために停止性を壊さない証明が必要。

2と3が観察同値であることを示せるなら、言語の新しい意味論の選択を避けられる。
今回はどちらも採用せず、1の局所境界のまま記録する。

関連: [台帳](../design/2026-11-10-boundary-inputs-ledger.md)、
[既存のcandidate guard問題](2026-11-09-cycle24-candidate-guard-policy.md)。
