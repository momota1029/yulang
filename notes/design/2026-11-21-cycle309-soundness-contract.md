# C309 の深掘り: 証明を持つ exact reader と、まだ残る健全性の入口

この作業は型推論の**健全性**を優先する。一般の停止性やスケジューリングの
改修は推進しない。固定された一例の到達相を閉じる補題は、
同じ source の据え付け前に未来の辞書を認めないことの検証用。

## 証明責務を分離

1. 実 source の Checked / Reachable と現 Frame を選択。
   checked registry / where 句 / ordered emitted children の証拠を保持し、
   テーブルの位置番号を source 需要そのものとみなさない。
2. full Models の同一割り当て全てに対する現在 packet の Holds と
   ClassEffects、および実生成辺を Committed から得る。
   個々の子に別の existential witness を選んで合成しない。
3. 局所候補一意性、SafeKnown、merged conflict がないことと実モデルを
   別に確認し、そこでだけ局所 V8 選定を導く。
4. supplied payload は順序付き表で検査する。全成功なら、
   全ノードに actual Generated と同一モデルの current Certificate を保持する。
   任意 path の証拠を再生でき、葉だけ別のモデルに替える必要はない。
   燃料が足りないと認められないのは実行上の理由で、source reject ではない。
5. journal の output slice の trust と、解決された子の Evidence は別。
   C309 では両葉に Evidence があり、親の明示出力も正当に証明されるが、
   両葉の packet は記録されず、親の output slice は Trusted にならない。

## 次の小さな健全性課題

`GeneralSelectedReadEvidence309.SelectionRow` の成立を入力とするだけでは、
現在の一般 B4 実装の正しさの証明にはならない。実 resolver が selected と返した
任意の reachable binary node で、output-bearing packet の
`∀ m, Models s m → Holds p m ∧ ClassEffects …` を、正確な現 frame・
保持済み journal の同じ capture/class/output と結びつける補題が必要。
`GeneralNominalVersionedDiagnostic232.ChosenHead` または個別存在 witness を
この全称条件と同一視しない。安全に進められる最小の候補は、
親の評価された出力が各 child の型拘束で実際に読み戻され、
保持 ledger と現 frame の class slice を比較できる branching fixture。
相互に無関係な枝の証拠と、現 output が子に読まれる枝を分けて試す。

この実例では別経路も閉じた。`GeneralPositiveForkCurrentSoundness309.current` が
既存 `Current` のフレーム、代替選択安全性および共通モデルを三つの発生点で構成し、
既存 `selected_node` を利用して同じ非空木の証拠を得る。これにより固有の
有限テーブルだけでなく upstream 側健全性入口にも実例が接続した。一般の
`InhabitedAvailable` は依然として別の義務である。
