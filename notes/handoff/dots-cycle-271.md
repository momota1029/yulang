# Cycle 271: record の実位置、入れ子の再帰判定、実例252の後継 Step

- 指示: I-52（有限 rebase Step と元の挙動との対応）・I-51 / I-53。work/dots-main のみ、expected-head 付き non-force。既存 Lean・spec・指示・凍結ファイルは未変更、barrel は末尾追記のみ。
- 開始: 2026-11-19 10:30:00 UTC。報告作成: 2026-11-19T11:20:06Z（50.10 分）。使用量の枠: 不明。
- 前周: 正常完了した cycle270 の公開 d272fe1eaf29cca645d48c28ad0a44c5eb0bc2fa と完了心拍を照合。ローカル開始 tree は公開 tree 15221b08dc48c47ec80178a4ccfc5b16286cff38 と一致。同じ repo の writer なし。
- 指示: 開始時 integration 499b87919b44c2d2acb8b573236a4b171bd92a32。後に 157c21459328db42119c52326288d8e672036535 に進んだ時点で公開を保留。新 head の standing orders・inbox の両 blob（7ae4d68d2ac7df80d1eadbd061dadd2296faf4c4、2f6b72446884d0e340537ac4b9aea1bb6c0e047d）に変更なし、STOP なし。最新 integration と tree 70cfa0e4b4a9d9c12e5c9c00f292546d72a83302 が一致するローカル祖先 9c415785a を静的検査に使用。
- 公開: 前周から報告・証跡込みで 94 ファイル。途中公開は 9897c53c、b5977d04、53a1fc51、e9a66370、a0182236、38a9fd84、b7202068、daf22f97、746ee3b6、535d178f。指示の再取得以外に作業中断なし。

## 検証された成果

1. **有限 record の semantic Edge を実位置で特徴づけた。**
   GeneralRebaseRecordLookup271.payload は任意の有限 record 二つが等価なら、共通ラベルのそれぞれ最初の payload が等価であることを示す。GeneralRebaseRecordOverwrite271.checked は first lookup が全ラベルで同一なら full carrier 型が等価であることを示す。GeneralRebaseRecordReadback271.hidden_not_same は任意の shadowed 位置を同一モデルで Int にも String にもできるため、全観測一致の相手がないことを示す。
   GeneralRebaseRecordEdge271.structural_edge_iff は、少なくとも一つの full model を持つ任意の journal の checked structural slot に対し、任意の Origin への元の semantic Edge は、記録済みのいずれかの child との all-model Equal と同値と示す。非正規の順序・重複を含む。exact-empty は幅可変の空 record と別で、子はない。
2. **可視位置の分類を任意の有限の入れ子へ合成。**
   GeneralRebaseRecordQuery271.locate_sound と GeneralRebaseRecordQueryCases271.total_on_record は、確認済み record root の任意の literal ラベル列・位置を分類する。可視ラベル集合が一致し対象が先頭なら、対応する canonical 子に全モデルで一致。後続重複・範囲外・違うラベル集合はどの Origin とも Equal でない。normalized shape 自体が不明なら unknown を残す。
   GeneralRebaseNestedRecordQuery271.resolve_sound は、この判断と既存の構造位置、tight な nominal 型位置を任意の有限な入れ子 query に合成する。単に Equal になれない親を、観測が存在しない親と同一視して否定を伝播しない。full model を明示した synthetic record 循環・非循環の両例では全 edge が確定。GeneralRebaseNestedQueryFixture271 は任意の長さで、並べ替え・重複付き record 列と variant/nominal の交互列の実判定と意味論の再帰を示す。synthetic 例の surface 到達性は主張しない。
3. **実 source 252 の初期 journal に query-local 検査を適用。**
   GeneralRebaseLocalOriginPocket271.atSlot_sound は raw 候補窓で見つけた正の閉路は証拠に使い、負結果には独立した forward closure チェックを要求する。GeneralRebaseLocalPocketProof271.pocket_closed は任意の起点から到達した全 raw slot が証明可能（nominal の型位置に tight 代表あり、deferred ではない）なら閉性チェックが通ることを示す。未知 slot を空の安全な葉とはみなさない。
   GeneralRebaseScalarSnapshot271.initial_models/initial_sites は未解決スロットの双方向 literal scalar 原子を読む検査用 view が、初期 journal の全モデル集合と site を変えないことを示す。実252は元の view では unknown。検査用 view でも全体に deferred が残るが、根からの窓は実際に [0,2] で閉じ、GeneralRebaseOutputDepthPocket271.actual_no_root_cycle は負判定を元の初期 journal へ戻す。既存の宣言的な非再帰結論に別の実行経路を与えたもので、readiness の同値は主張しない。
   GeneralRebaseRawIntoFull271.root_exact は、任意の journal に full model が少なくとも一つある場合、任意の根の raw K2 が full semantic RootCycle に埋め込まれるため、両枝を含む V8 RootK2 が semantic RootCycle と同値であることを示す。Actual252.actual_k2_clear はこの橋で V8 RootK2 全体をクリアする。GeneralRebaseK2ModelBoundary271.necessary_scope は矛盾する Int/Str 制約を持つ例で、モデルがなくても raw の直接循環が残る反例。モデルの証人なしでは両枝を潰さない。
4. **実252の後継 rebase Step、据え付け後の実 readback。**
   GeneralRebaseOutputDepthSuccessor271.dichotomy は、実初期 journal からの任意の元の到達列で、該当一出力の固定 basis が2要素のままか空に限られることを示す。bidirectional は実初期状態からの任意の元の可視 Weak 出口と有限 rebase Step の射影を双方向に対応させる。逆向きは実 V8 install が証人。computed、one_step、no_second_step は可視遷移1回を計算して終える。元の kernel の停止は結論でない。
   GeneralRebaseOutputDepthTrace271.classify_all は実初期状態からの任意の有限旧経路が、全無変化か、一回の本物の Weak 出口の後に全無変化の継続となることを示す。no_followup は実 install 後の任意の有限旧経路で可視射影が空のままという回帰。
   GeneralRebaseInstalledReadback271.Actual252.converse_fails は full model を持つこの実 installed journal で、強制された出力3から元の入力2へ semantic に二辺の経路があるのに、raw snapshot には出力3からの辺さえない反例。raw→full の橋の逆を経路には使えない。
5. **実 installed 252 の全 Origin と候補の非循環を別個に検証。**
   GeneralRebaseUnaryRank271.acyclic は、ある full model で有限の単引数 nominal 列（末端 scalar）を読み出せる Origin の深さが等価性で不変かつ semantic Edge で真に減るので、当該 Origin は非循環と示す。GeneralRebaseUnaryReadback271.cycle_sound は供給形状がそのモデルを表すとき、任意の入れ子 Origin で「有限形状」「そのモデルで観測なし」「不明」を区別して負判定を返す。
   GeneralRebaseInstalledOutputCycles271.no_cycle は実252 installed model の全 identity に対応する有限形状関数を使用し、任意の Origin を非循環と示す。combined_root_clear と GeneralRebaseUnaryCandidateCoverage271.Installed252.checked_candidates は、実 installed journal の raw/semantic 両枝を含む RootK2・CandidateK2 の否定を与える。一般の witness model 自動生成、候補照合、EvidenceNode を主張しない。

[設計ノート](../design/2026-11-19-cycle271-record-origin-exactness.md)。言語設計の追加判断が不要だったため質問ノートなし。[全モジュール・宣言一覧と監査出力](../verification/cycle271/) の各 *-modules.txt・*-declarations.txt・*-audit.txt を参照。

## 検証

- Lean 4.35.0、--trust=0 -DwarningAsError=true -R .。新規モジュール 34 個を旧依存キャッシュと区別した隔離出力へ再コンパイル、終了0。[出力全文](../verification/cycle271/final-fresh-recompile.txt)。
- 10 Audit を cd lean && lake env lean --trust=0 -DwarningAsError=true -R . Audit/<file>.lean で独立実行、終了0。331 宣言、標準公理のみ。隔離キャッシュで再実行した出力も同一。[監査集計](../verification/cycle271/final-audit-recheck.txt)、[14対象の再検証](../verification/cycle271/final-fixture-recheck.txt)。
- bash tools/verify-lean.sh . 9c415785a --no-build と前周基準 ... 7829ecdac --no-build は終了0。[integration同一tree基準の出力全文](../verification/cycle271/diff-gate.txt)・[前周基準の出力全文](../verification/cycle271/prior-cycle-diff-gate.txt)。[凍結とbarrel](../verification/cycle271/freeze-and-barrel.txt)（I-51/I-53）。全体 lake build、CI、Yulang 実機なし。

## 残り

- 任意の installed journal の full model・有限形状を取得する一般検査、複雑な deferred・非 unary 出力の扱い。モデルなしで今回の負判定を広げない。
- 任意の出力数・owner・到達状態につながる source 由来の有限 observer、公開モデル保存・反映、一般 rebase Step。
- V8 EvidenceNode、12性質・全回帰の移植。239/240 の元の kernel の非停止反例は変わらない。
