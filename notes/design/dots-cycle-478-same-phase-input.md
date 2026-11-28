# C478: 元 input event から読み取る最小限の座標

I-95 の期限は C479。今回の対象は、同じ相の入力 event から受け取るべき source の情報と、すでにある raw / source table と元構文から再構成できる情報を分離すること。型商と旧 raw は変えない。古い compiler event、声明、公開入口を差し替えない。

与えられた実元 pose 一つと同じ structural actions について、元構文上の relative poses を独立な帰納的な判断で列挙する。相対 pose は一意に復元できるが、正規化した同一 join の二つの元位置は同じ compiled path / ordinal だけでは区別できず、どちらを入力 event が指すかを決めない。旧 capture 前の実 head と要求の情報に加え、元 raw ordinal、同じ相の authored ordinal をそれぞれ参照すれば、旧 wrapper に重複していた式と declaration frame を照合し復元できる。

`Attached` は既存式との照合にすぎず、compiler が source として発行した、または output が本当に完了したことを証明しない。同一 raw でも、渡された authored と未完 output の二つの table はどちらも attach でき、source-backed 適格性が異なる。I-92 の source branch と既発行 output の branch は別であり、どちらも今の入力を作った同じ event との対応を別途要する。戻り値 `none` はこの局所証拠が不足したことを示し、言語の拒否でも K2=false でもない。G04 は完了としない。
