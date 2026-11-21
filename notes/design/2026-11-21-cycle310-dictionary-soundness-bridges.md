# I-55 の (4) と (2): C310 のチェックリスト

## (4) 選択結果が辞書の証拠を持つ

- 済: checked, reachable, 選択から current Frame、ordered children、実 current
  effect、Ready、materialized、候補の安全性、cache の前提を既存の 235 の補題で得る。
- 済: **記録済みで再構成できる分岐**では、実 plan ledger にある packet の Holds・
  現 class 式・生成辺を全 Models から読み出す。ordinary extension と current Frame
  の再検証が必要で、モデル射影や履歴上の存在だけでは代用不可。
  `GeneralVersionedHistoryEvidence310` / `GeneralVersionedRecursiveBridge310.ReplayFrame`。
- 済: 未収載分岐で下の二橋を仮定すれば、同じ effect が実際に Installable となり、
  既存 B4 Stable の性質から全モデルの current Holds・class effect・生成辺を得る。
  子の証拠は同じモデルを共有し、与えられた有限辞書に関する帰納だけで根に伝播する。
  `GeneralVersionedRecursiveBridge310.evidenceNode` /
  `GeneralVersionedSelectedSoundness310.on_returned_snapshot`。
- **残り 2 本**、いずれも ordinary replay で覆えない実 selected（checked /
  reachable / 対象が生成済み / Stable / full Models 有り）に対して:
  1. **選択の互換** `ChoiceBridge`: 現在選ばれた候補の key が、現在 alias 類の
     過去 packet の key と一致する。過去 packet の無い類と、同じ発生点・ordinary
     extension・旧所有キーを再検証できる類は閉じた。別発生点を結ぶ alias や、
     本当に観測を変えた refresh 後を一般化していない。
  2. **共同モデルの完成** `JointBridge`: 互換な現 effect に対し、同じ m で
     現 Models、head+schema、ordered child materialization、output coverage、
     current class 式を同時に成り立たせる。個々の存在証人を混ぜない。
     実 Holds が得られた式について、明示ローカル出力＋名前ごとの代表＋同一モデルの
     同値だけで現 class 式を出す削減を証明。alias で新しい名前が入る場合・default
     の場合はこの削減の対象外。現 Holds そのものの一般製造も残る。

## (2) 停止して返った場合の部分正当性

- 済: 返された有限 tree の独立チェッカーは、認証済み current Local rows と
  照らして `Resolves` を与える。実 Step 路と停止証明が供給された返り値に対し、
  任意候補 tree との等号と宣言的 `Resolves` の両方向が成り立つ
  (`GeneralVersionedCheckedReturn310.exact_tree`)。
  selected な親の下の pending / rejected / ambiguous を親の失敗に潰さない。
- **残り 2 本**:
  1. **履歴付き一般観測・コンパイラ正当性**: source observer が同じ終状態の raw
     occurrence、現 frame、alias、旧 packet・現 class の制約を読み、実 Local の
     各行に正しい表現を供給すること。C310 の二点では実 merge の alias を読み、
     確かな表を得た。全モデル・全 Survivor・実発生点・辺・plan ledger が一致しても
     settle 前後で子の選択が変わるので、これらだけのビューは不足。
  2. **実 Sat 返り値に対する実行対応**: 成功返却のイベント列を実 Mixed Step 路に
     写し、返した地点の停止を検査し、その地点で上記の行と tree を照合する。
     成功返却は仮定で、停止保証・手数上界・有限商は証明義務に含めない。

本数は最終インターフェースの未証明の入力群を数えたもの。各群を本当に
閉じる補題の数を予測したものではない。C310 は回帰と一般削減の双方を証明したが、
四つの未証明入力群を消したわけではない。

## 実例をコードで読むと

字句を説明する擬似コード（Rust parser の検査結果ではない）:

```text
Outer(List[T]) -> out = z
  where Inner(T, item = z)  // 句20、名前付き出力
        Inner(T, item = z)  // 句10、出力専用 z の producer

Inner(Int) -> item = Int
```

意味論では二つの `Inner` 呼び出しは別発生点、順序は句10→句20。
両方の通常入力は source slot 1 の Int で、`z` を新たな入力
として仮定しない。外部要求 `Out : out` の対象も slot 1 だが、
`z` は別の fresh source identity。親の明示式がちょうど二つを関係づける。
merge 後は二発生点の class request の同じ名前が同じ値参照に結びつき、
二つの辞書 witness のうち片方だけを落とすことは許されない。
