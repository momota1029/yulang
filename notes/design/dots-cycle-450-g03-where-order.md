# C450 / G03: 原 where の位置にある実 child K2

正本 `integration/m1-final@d0ffaea1ce9897d9b5a4ff3f3e9d9f46bb11fec0`、I-83。
設計の基点: `dots-cycle-443-no-false-rejection-design.md` G03/C03、spec §6.3 の raw 根 K2・原 where 入力、§6.5 の list mode。旧 C411 は単一親・子の入口を保つ。

1. 親は真の可視 singleton と、元の invariant point-list 入力の順序つき authored frame。子は任意個・任意位置の原 clause から、元の binder 捕捉を使って復元。literal 一変数入力・要求出力なし。元の clause/role・実 request の occurrence path を一切 witness から読まない。
2. それぞれの実 child を、同じ状態で原 raw K2 があるか、適合する G02 の真の成功 leaf であるかの独立な有限関係で判定。親 root には K2 不在を要求。途切れない森林と少なくとも一つの rejected を必要とし、親自身の K2 へ縮約しない。処理順で solver の schedule を主張せず、子の保持等式による状態更新は別行。
3. データ証人は元 origin index・実検査位置の有限 split escape、親が復元した子の並びに対応する生の row/index/path witness または既存の G02 leaf wire。任意の有限 actual Bound/Alias/structural 導出から raw Cycle350 wire を作る。全子を走査して元の木・verdict・空 writes を厳密に比較。
4. 独立な正確報告の有限証人（同じ正確報告との両向き）、以前の全 witness Bool 保存、同じ FullState の全 FitsFull で原 trace 各局所の意味・成功 leaf の辞書。辞書がない rejected の親には辞書を作らない。元の全選択規則・全体診断の完全性は主張しない。
5. 実状態の子2だけが K2、子3／先頭の原 clause 並び替えも確認。親の K2、親自身の rejected に書き換え、子切り詰め／余計な子／wire 入替／別根の循環は不受理であることを実入口で試す。
