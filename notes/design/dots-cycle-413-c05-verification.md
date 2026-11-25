# C413: I-74 C05 / X11 bounded closure

元の §6.3 X11: `Check {box:'a}` と `Check {box:{next:'b}}` の両方が可視、値は `{box: μ}`、`μ={next:μ}`。外側実 point と元 raw row により box の実 site を得る。実 nested pattern が μ を検査し K2。親根は循環せず、where は生成しない。

1. `MixedTape` は元の全 visible list と索引が同じ。実 nested 候補一つと、一つ以上の literal binding-only 候補を元順で保持する。普通の `EquationRead.whole` を元 raw row（元 capture を代入したもの）に使い、各 binding-only rival が本当に `SourceHead` で完全に一致することを証明した。この変数自身が内部を訪れることはない。nested は元 field へ本当に入り、raw graph の実 site で循環する。R5 は `mixedRecordLocal413` の rejected-only 診断を R4 に加え、同じ `dictionary_sound_R5` を示す。
2. `scanAll413` は実可視リストを最後まで検査する。実 role、全 candidate の合法な宣言、実 row/demand、ID の相異、R4 root priority を照合。nested の ordinal は計算し、証人が候補を与えない。元 origin/row と raw path だけの certificate で `check`。旧 `RecordK2412.check` はそのまま。別の/未対応候補を捨てて拒否を通すことはない。
3. `check_sound` は同じ State と同じ exact `rejected/rejected/[]`、全 fitting model の証拠。新 branch の元 trace は `SourceTrace.other`、選択・曖昧さ・親 raw K2・実 where rejection tree にすり替えられないことを証明。旧・新 branch は排他で checked report は一意。

実 X11 で両順が true。実 binding-only 二つの曖昧さ候補があっても true。元 nested ordinal は `[binding,nested]` では 1、`[nested,binding]` では 0、候補 ID はともに 57。二つの別の束縛変数と元役割は別々に定義された一致候補（同じ declaration ID の複製ではない）。どちらの元順・二 binding match の実例にも同じ規則の fitting model と元報告 evidence が存在。binding-only・nested 単独・未対応の三候補・ID 複製・非循環・未到達 site は false、親に実帰路がある別入力では旧 raw branch のみ通る。実行 `[true,true,true,false,false,false,false,true]`。false は言語の拒否ではない。

### 順序・二つの実一致・再生の保存

- `full_scan_shape_independent_of_order413` は、同じ入力観測と constructor/role 表のもとで、全 row リストの任意の permutation に対する scan 独立性を証明する。`mixed_scan_recovers_tape_after_permutation413` は fresh ordinal の型付き tape を再生する。単なる２ケースのテストではない。別に、実 resolved snapshots で [binding, nested] とその逆順、二つの実 binding rivals を含む六通りの順を全部実行した。全 true、元 visible IDs と nested の actual ordinal を保持し、nested ID 57 と field site 1 は変わらない。
- `three_row_example_has_two_actual_matching_heads_and_K2_413` はその実三行の両 rival が互いに異なる ID の `SourceHead` 一致と証明。未対応の二 nested、他の形、空 scope はこの branch では証人がないだけ。
- `locate` は固定 Result に触れず元 occurrence・**全候補 ID の元順**・nested ordinal/ID・実 field site を取り出す。`same_tape_and_trace_before_models413` により、実 tape と exact trace はモデルより先に固定。`selected_exact_reports_conservative413` はこの rejected-only 拡張の前後で全 exact selected report・実 where 順・literal writes・同じ output support を保つ。solver completeness や termination ではない。

### 本当に一致する rival の意味的な対照

`actual_plain_rival_has_a_typed_leaf_payload413` は、各実 binding-only rival の元宣言、元 capture、空 where/outputs を用いて、任意の同じ fitting model で葉の意味証拠を構成する。これは選択を仮定または発生させる規則ではない。`same_X11_with_two_semantic_leaf_rivals_and_no_win413` は実三行の ID 56、58 の両方にこの同一モデルの leaf evidence がある一方、そのどちらの `selected` も R5 にはなく、同じ K2 report evidence があることを一つの定理にした。構文だけ似たダミーの rival、仮の外部 evaluator、言語変更はない。

### 同じ head が二つ一致しても循環しない対照

独立 `Cycle413I74MixedRecordFiniteControl.lean` では同じ二宣言・同じ外側 point の有限 record に、両方の真正な `SourceHead` 一致と実 fitting model がある。実 scan の前段で全 tape を取得できるが、実内部 site には cycle がないため、**どの report とどの witness でも** 新 `mixedHead` branch は false。元 graph には展開済みの nested row もある。検査未対応を言語の拒否や曖昧さの決着に読み替えない。実行 `[true,false]` は「全 tape を読める／K2 は通らない」を表す。

### 同じ snapshot で診断位置を取り違えない

`same_visible_list_has_same_opening_ordinal413` は、ある元 ordinal を一方で nested と読むなら、他方がそこを binding-only と読むことは構文的に不可能と証明する。同じ fitting State では元 point の native syntax により root・label・site も一致し、実行 witness を変えても `locate` の結果は同じ。`open_field_is_not_a_parent_alias413` はこの実 site が親の alias でもないことを示す（もし同じなら元 root が循環）。候補順を変えた **別** snapshot では元 ordinal を変えて記録するが、上の対照どおり候補実体と診断は同じ。
