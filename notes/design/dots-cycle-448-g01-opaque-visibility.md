# C448 — G01: opaque な名と呼び出し側の可視候補

I-83、正本 integration/m1-final@ca9762e1994c3276bab4a485404d256854fbf9ca。旧 `check_full447` と FullState/証拠は不変。spec §6.2/6.3 の呼び出し側の可視性を使い、空 arity 名の本体は照合しない。G10 の構造候補全般は今回の範囲外。

- 既存の解決済み入力: `visible` は元の解決済み registry 中の該当 role を、順序を保って全て取得する。証人に候補一覧を渡させない。独立局所選択はこの全一覧が singleton、同じ実宣言の元 authored nominal endpoint、該当役の宣言・coverage/checked、空 where/output、元 raw 位置の K2 不在。nominal body は開かない。
- 新 witness は元 origin の一覧中の位置と raw の有限順位/側表のみ。旧分岐はすべて元 checker を呼ぶ。任意の独立局所選択から正確な報告とこれを通す wire、任意の受理で同じ FullState の分類と任意の FitsFull モデルの報告証拠。既存 R1 報告を既存の保存補題で運び、上位の意味は変えない。
- 入口より上流: `ModuleVisibility` と同じ owner/current-or-loaded/access を、名前解決済みの owner と accessible ID に適用し、元の順序・宣言 ID を保った完全な元入力を作る。全候補行とアクセス結果は独立した source/name-resolution 入力であって checker witness の一部ではない。今の FullProblem 単独には owner, load, access がなく、未解決のカタログからの可視性を発見できない。呼び出し出現 + compile 結果が実 FullState と一致するときの橋を別に証明する。
- 同じ role と同じ実 nominal head の別 ID を、未ロード／アクセス不可と、ロードかつアクセス可で対照する。前者は正報告を保持。後者は両方の実 head が合致するため旧選択報告をこの分岐では認めない。一般に全可視列表が非 singleton の場合の非受理は実装範囲であり、一般言語の拒否ではない。
