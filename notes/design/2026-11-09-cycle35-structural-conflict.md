# Cycle35: rigid outer-head conflicts

部分目標: 実 ordinary TyTerm/Atom に対し、構造的payloadやrowを任意変数のまま保持し、剛な外側headの不一致を有限検査する。
staticHead は var/union/inter を unknown とする。底が左・上が右の場合は矛盾としない。recordの幅やpayload間の比較を勝手に否定しない。
独立 Certificate は (1) 実atom L≤U のhead不一致、(2) 実atom L≤x と x≤U のhead不一致の二規則。
任意の名前型・任意assignmentに対し、Certificate が存在すればそのatom集合のモデルはない。check=true iff Certificate、及び任意の状態リスト/assignmentに対しprune前後のモデル存在iffを示す。
既存自己出力探索にpruneを後置し、全モデル族の独立宣言導出とのiffを保存する。headが同じ構造の内部矛盾、長い辺を渡る構造boundsの推移、一般充足可能性、言語rejected分類は未達。
この証明はCommonRigidHeadInspectionの意味論的head分離に依存する。意味論の新規選択はない。
