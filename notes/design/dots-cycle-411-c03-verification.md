# C411: C03 / X9 bounded closure

対象は §6.3 K2 の `impl Show (list 'a) where Show 'a` / `show [loop 1]`。B4 の解決元 snapshot、singleton の実宣言、invariant list 点入力、実 where 一つの同一 role・literal 変数、空出力。この checker true はソース言語上の受理でなく **その exact 拒否報告の証人を確認** したという意味。

- `whereListLocal411` は元の宣言・捕捉と本来の where を持つ event に限る、子 K2／certificate に依存しない追加規則。`R3 = R2 ∪ whereListLocal411` について固定 `dictionary_sound_R3`。parent から呼ぶ where は checked descent、名の shadow なし、元位置 `occurrence ++ [0]`、実 point capture を保持する。
- `WhereCycle411.check` の witness は parent の元 origin ordinal と escape palette、および既存の raw K2 の data。需要や role、経路、結果を witness の別 datum として採用しない。同じ元 snapshot の、実 where から組み立てた子 demand を `Cycle350.check` に渡す。旧 `List410.check` は分岐ごとそのまま、旧 branch と新 branch は同時に通らず、全成功報告が一意。
- `WhereCycle411.check_sound` は exact report `selected parent [.rejected]`（verdict rejected、書込み空）、元規則の exact trace、同じ State の任意 fitting model の `ReportEvidence`。子の拒否を親根の K2 や親の成功に置き換えない。実 `ν = :tag ν` の同じ regular model の fitting proof も独立監査。
- 実行結果順は X9、本来でない裸の親拒否・親成功・旧 X8 branch、子ループなし、親に実 alias 帰路がある場合の新 branch と旧 raw branch、偽の子 raw wire・origin・選択親 id。`[true,false,false,false,false,false,true,false,false,false]`。親の根に帰る別入力で raw K2 優先を保つ。親の literal 変数捕捉は実 structural visit ではない。
- 親 escape は C410 の有限十分条件を引き継ぐ。未対応 false は言語の拒否ではない。任意 interval、多候補、where 複数や成功する子、関連型、solver がこの witness を作ること、Rust、パーサ、停止性は含まない。別の C 行を閉じない。
