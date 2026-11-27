# C455 後半: 採用候補は original route を読む入口だけ

`RecordTrail455.check_full455` は前半の閉じた spine の raw-only **試験入口**。raw alias の物理 owner に authored observation があっても、元の論理位置への正当な route はそれだけでは分からない。この入口を累積入口に採用しない。前半の検証済みファイル・差分はそのまま残す。前半のテストの成功は元 source 採用の証明ではない。

C455 の採用候補は `RoutedRecord455.check_full455` (`GeneralDeclarativeI65I74RoutedRecordEntry455.lean`) のみ。そしてその `.previous` は C454 を直接呼ぶ。proper prefix ごとに、同じ orig index にある native record row、raw owner への actual Alias、および `OriginRoute`（物理 owner が違うなら logical/physical/issuer の実表）全てを読む。逆に到達した末端 K2 の判定は unfiltered raw graph のままで、その末端を開く source route は要求しない。試験では raw と native は同じでも route 又は issuer がないと false、真の route なら depth 3 が true、K2 が早く現れれば先を開かずその実位置だけ。

親の元 head と where の tree は利用者提出の候補ではなく、実宣言から翻訳。実閉じた record tail を持つ合流前の written tree なら、join を除く入れ子・枝について、任意の capture と正規化の可換性から数学的に Paterson の安定性を得る。既存の `ConservativeSmaller` を変えない。proper prefix が実 record field の範囲。mixed nominal / variant の途中を通る開き方や、open tail の著者証拠・where のより広い型は未確認。G04 全体の残りはこの境界として扱う。
