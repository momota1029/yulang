# Cycle 281 — 239 / 240 実列の固定 replay 回帰
各 n の実 packet でタグ列は同じ binder/polarity の 4 行（inputNames の重複も保持）になり、左右の書き先は n に依らない。read だけは捕捉によって動く。以前の予約、既存の構造 slot、以前の raw atom の 3 項を分け、現 n の版付き上下 port は旧 source footprint にないことを示す。その上で実 replay の射影および Known の一致を全 n に示す。これは固定 port 化が言語の完全性を一般に満たす、あるいは古い無限実列が止まるという意味ではない。後継の停止性は別に phase/chart filter が担当する。
