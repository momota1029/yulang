# C411: C03 / X9 bounded closure

対象は §6.3 K2 の `impl Show (list 'a) where Show 'a` / `show [loop 1]`。B4 の解決元 snapshot、singleton の実宣言、invariant list 点入力、実 where 一つの同一 role・literal 変数、空出力。この checker true はソース言語上の受理でなく **その exact 拒否報告の証人を確認** したという意味。

- `whereListLocal411` は元の宣言・捕捉と本来の where を持つ event に限る、子 K2／certificate に依存しない追加規則。`R3 = R2 ∪ whereListLocal411` について固定 `dictionary_sound_R3`。parent から呼ぶ where は checked descent、名の shadow なし、元位置 `occurrence ++ [0]`、実 point capture を保持する。
- `WhereCycle411.check` の witness は parent の元 origin ordinal と escape palette、および既存の raw K2 の data。需要や role、経路、結果を witness の別 datum として採用しない。同じ元 snapshot の、実 where から組み立てた子 demand を `Cycle350.check` に渡す。旧 `List410.check` は分岐ごとそのまま、旧 branch と新 branch は同時に通らず、全成功報告が一意。
- `WhereCycle411.check_sound` は exact report `selected parent [.rejected]`（verdict rejected、書込み空）、元規則の exact trace、同じ State の任意 fitting model の `ReportEvidence`。子の拒否を親根の K2 や親の成功に置き換えない。実 `ν = :tag ν` の同じ regular model の fitting proof も独立監査。
- 実行結果順は X9、本来でない裸の親拒否・親成功・旧 X8 branch、子ループなし、親に実 alias 帰路がある場合の新 branch と旧 raw branch、偽の子 raw wire・origin・選択親 id。`[true,false,false,false,false,false,true,false,false,false]`。親の根に帰る別入力で raw K2 優先を保つ。親の literal 変数捕捉は実 structural visit ではない。
- 親 escape は C410 の有限十分条件を引き継ぐ。未対応 false は言語の拒否ではない。任意 interval、多候補、where 複数や成功する子、関連型、solver がこの witness を作ること、Rust、パーサ、停止性は含まない。別の C 行を閉じない。

## 追加で確かめた同じ C03 の整合性

`checked_where_child_keeps_same_trace_for_all_models411` は実 parent event と元 where 0 番の raw child を備えた一つの trace をまず選び、モデルを後から全称量化する。 `where_rule_is_a_new_local_family411` は同じ event が旧 R2 local family に属さないことを示す。さらに `checked_X9_tree_is_forced_in_fitting_state411` は、同じ入力に fitting model が存在すれば、その入力の **全 R3 declarative trace** が元の親 ID と単一 raw child rejection の木を持つことを示す。モデルの数値同値ではなく、元の slot に複数の observation があれば fitting native syntax は同一の literal endpoint を見るという整合性だけを使う。他の形・モデルのない矛盾 snapshot までの一意性や NoFalseRejection ではない。checker の入力・意味は変えていない。

## 独立再生の確認

- 完全な Git bytes の C410・C411 を別の出力ディレクトリで strict Lean 4.35.0 再生。12 production modules、8 standalone Audit、追記 import の同時読み込みは全て exit 0。C411 単独の sealed replay（6 production、5 Audit）も exit 0、37 unique audited names は標準 axioms のみ。
- 別の同一 X9 構造で、元の role・constructor・declaration ID・束縛名・source slot・子 payload・occurrence をすべて変更しても checker は true。書かれた束縛と別の名前、別 role の where、追加 clause、fallback arity のみで著者がいない role、可視候補が二つ、誤った子の argument index は、同じ新 branch で `false`。厳格な追加カーネル試験の結果 `[true,false,false,false,false,false,false]`。これらの false は言語上の拒否を主張しない。

## 循環の二段対照と witness の限界

- 同じ実 where 一つの source を、子 `1 → 2 → 1`（異なる constructor tags）の元 graph でも検査した。実際の二辺を渡すと true、閉じない一辺の短絡と別の偽行は false。二節点の正則モデルを構築し、両方の unfold の有限深さ全てでの一致と、この同じ snapshot の fitting/evidence を別 strict Lean 検証で得た。
- 混合制約を足した別の fitting snapshot では、同じ実子 rejection を `Classifies R3` と `ReportEvidence` が導出するが、公開 `WhereCycle411.check` の全種類の証人が false になる。具体的に元の `Bound 0≤1, 2≤0` と flat equation `1=2` があると、現 alias rank 証人は 0 と 1 を同じ側に強制する。一方、本来の raw graph では、方向 Bound と flat equation を混ぜて 0 を 1 の alias にする規則はなく、親根に raw 帰路はない。子は本当に循環する。拒否報告を証明したのに証人が範囲外になる対照であり、言語変更ではない。C410 の十分条件を引き継いだ制約を含め、C03 を閉じたというのは上の仕様例の三条件である。

- この条件差の再現証明は独立の [Cycle411I74WhereListCertificateBoundary.lean](../../lean/Audit/Cycle411I74WhereListCertificateBoundary.lean) に追加した。raw recurrence `ν ≈ list ν` の型に対する既存 raw ルールの例であり、別に宣言した既知の名付き recursive atom を展開する主張ではない。新しいルール、check の分岐、または C 行はここでは追加しない。
