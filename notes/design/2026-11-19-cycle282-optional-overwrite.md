# Cycle 282 — optional で同一 fixed ポートの二時点を区別
実 optional point 段階で最新の旧 plan は下端を公開 source 4 から読み、二回目 install の最新 plan は同じ固定アドレスに source 2 を書く。両方の型は区別されるため、同じ割当に二時点の live 表を同時に足す設計は不成立。全履歴を版付き定義として展開し、live 表だけを最新 plan で上書きする設計では、一つの witness がその時点の全 Models と recursive Evidence を保持する。
