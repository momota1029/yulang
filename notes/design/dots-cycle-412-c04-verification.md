# C412: I-74 C04 / X10 bounded closure

対象は spec §6.3 の `impl Check {box: {tick: 'a}} where Check {box: 'a}` / `Check {box: μ}`、`μ = {tick: μ}`。元の閉じた record 点を知っている単一の同 role かつ実に書かれた候補、二段の閉じた head、literal where 一つ、空出力。親の元 observation と元 raw row を照合して、`box` を実際に開いて `{tick: 'a}` を検査する site を取り出す。候補を選ばないので where を実行せず、子需要を作らない。

1. 独立の `recordLocal412` は追加の `other` 診断だけ。元の唯一の可視候補・正しい declaration（stable Paterson は任意 capture 置換の後も）・head 構文・実 point と raw row・候補内 Visit を要する。raw graph は support で濾過せず、実 site に cycle がある。R4 は R3 の elected をそのまま、`dictionary_sound_R4` は固定の結論を保つ。
2. `RecordK2412.check` の data は origin ordinal、元 row ordinal、parent escape、実 site を巡る `checksHop / close` data。site 自体や子 Demand は証人が供給しない。親 root は安全で、候補内の site は alias でも親 root ではない。`replayField412` は実 role・元 declaration・where の形・空 tail の元 metadata を検査。旧 `WhereCycle411.check` をそのまま呼ぶ。
3. `RecordK2412.check_sound` は同じ元 Problem・exact report と全 fitting model の evidence を保持。report の表現 `rejected / rejected / []` は旧 raw root と同じ DTO だが、今回の証拠は `SourceTrace.other`、実 where の selected-parent tree や `.rootK2` ではない。全 R4 trace の同じ形、旧・新 branch の排他、成功報告の一意性を証明。未対応の false は言語拒否ではない。

実例は物理名 0 が親、実 field 在処 1 が `μ`。root alias return を足すと新 branch false、旧 raw root branch true。循環しない入力や未到達 cycle、別 row、別 origin、where child report、親根証人は false。実行ベクトル `[true,false,false,false,false,false,false,false,true]`。同じ正則 record 模型で実 cycle の一段展開と全有限深さでの一致を示し、`Fits` と元報告 evidence を監査した。複数候補・open tail・一般 interval の例は別行。Rust／parser・停止性・NoFalseRejection は対象外。

### 発現の固定

`checked_record_fixes_actual_site_and_trace_before_models412` は、元の candidate・実 field と `SourceTrace.other` を一つ先に固定し、後から同じ State の全 fitting model を量化する。別の使える origin ordinal があっても、同じ point に一つの literal endpoint を読む fitting 入力では、両方の証人は同じ宣言・field label・論理 site を照合する（`same_fitting_input_cannot_change_checked_field412`）。型の値をモデルで等置して別名へ乗り換える証明ではなく、元の endpoint 構文の一致だけを用いる。

### 独立の位置・cycle 対照

- ここで閉じた「record head」は tail 束縛を持たず、正本の `{}` に対応する `.emptyRecord` で終わる literal syntax を指す。幅の部分型付けを狭めたり、列挙しなかった field がないことを要求したりはしない。元の有限 graph decoder を使うには、この例の outer row をその形で読める必要がある。
- 同じ X10 の形で、元の origin と outer row は両方 1 番、親は名前 5、実 `box` field の site 8 が二つの異なる record 行 `8→11→8` で循環する別入力を検査。実の証人だけ true。別 origin/row・一辺の未閉路・元 point と raw row が別の payload を指す・違う field label・変数捕捉だけ・fallback role の対照は false（言語上の拒否とは区別）。`[true,false,false,false,false,false,false,false]`。元の二節点周期を展開する同じ fitting model と evidence も示した。
- `only_binding_record_field_does_not_visit_inner_site412` は根の record 書式に変数 field しかないと、その field の内部を訪れないことを任意 View で証明。`original_outer_record_is_seen_and_holds_in_same_model412` は同じ fitting model に最初の記録 literal endpoint と実 raw row の意味の両方を保持する。

### 既存報告を変えずに実診断位置を読む

追加の pure `RecordK2412.locate` は fixed Result を変えない補助読取りで、実 X10 witness と exact report が通る場合に限り位置を取り出す。本来の occurrence `[71]`、宣言 ID 218、元引数 ordinal 0、実 field label 20、親 slot 0、実 site 1 を確認。where 風の結果では `none`。一般の反映定理は結果に記載した site が判定した実 `Visit` の site であり、親の非循環を保存することを示す。親の occurrence に架空の子 ordinal を足していない。

### raw cycle の閉じ方を照合する対照

実 field site 8 で構造辺 `8→11` を踏み、元の flat `11=8` で閉じる対照では true。片方向 Bound だけ、別の名への flat、閉路のない短絡は false（`[true,false,false,false]`）。この実同一モデルの報告証拠を再検証し、flat があっても診断 site は実 field の 8 のままで、戻り辺の別名 11 に移らないことも確認した。新しい判定規則は足していない。

### R3 に対する成功保存

`selected_exact_reports_conservative412` は、同じ元 State・request・exact report で verdict が selected のとき、R4 の分類と R3 の分類が同値であることを示す。`previous_success_trace412` は成功木と各 output support の導出に帰納し、同じ発現の event、同じ where 順、同じ literal writes を保つ。C04 に足した rejected-only の規則が成功辞書・成功出力の由来を作らないことの形式証明で、solver が証人を作るという主張ではない。
