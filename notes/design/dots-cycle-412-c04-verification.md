# C412: I-74 C04 / X10 bounded closure

対象は spec §6.3 の `impl Check {box: {tick: 'a}} where Check {box: 'a}` / `Check {box: μ}`、`μ = {tick: μ}`。元の閉じた record 点を知っている単一の同 role かつ実に書かれた候補、二段の閉じた head、literal where 一つ、空出力。親の元 observation と元 raw row を照合して、`box` を実際に開いて `{tick: 'a}` を検査する site を取り出す。候補を選ばないので where を実行せず、子需要を作らない。

1. 独立の `recordLocal412` は追加の `other` 診断だけ。元の唯一の可視候補・正しい declaration（stable Paterson は任意 capture 置換の後も）・head 構文・実 point と raw row・候補内 Visit を要する。raw graph は support で濾過せず、実 site に cycle がある。R4 は R3 の elected をそのまま、`dictionary_sound_R4` は固定の結論を保つ。
2. `RecordK2412.check` の data は origin ordinal、元 row ordinal、parent escape、実 site を巡る `checksHop / close` data。site 自体や子 Demand は証人が供給しない。親 root は安全で、候補内の site は alias でも親 root ではない。`replayField412` は実 role・元 declaration・where の形・空 tail の元 metadata を検査。旧 `WhereCycle411.check` をそのまま呼ぶ。
3. `RecordK2412.check_sound` は同じ元 Problem・exact report と全 fitting model の evidence を保持。report の表現 `rejected / rejected / []` は旧 raw root と同じ DTO だが、今回の証拠は `SourceTrace.other`、実 where の selected-parent tree や `.rootK2` ではない。全 R4 trace の同じ形、旧・新 branch の排他、成功報告の一意性を証明。未対応の false は言語拒否ではない。

実例は物理名 0 が親、実 field 在処 1 が `μ`。root alias return を足すと新 branch false、旧 raw root branch true。循環しない入力や未到達 cycle、別 row、別 origin、where child report、親根証人は false。実行ベクトル `[true,false,false,false,false,false,false,false,true]`。同じ正則 record 模型で実 cycle の一段展開と全有限深さでの一致を示し、`Fits` と元報告 evidence を監査した。複数候補・open tail・一般 interval の例は別行。Rust／parser・停止性・NoFalseRejection は対象外。
