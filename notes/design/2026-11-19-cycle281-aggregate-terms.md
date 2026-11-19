# Cycle 281 — 端点が異なる観測の raw replay
同一の捕捉だけでなく任意の packet を対象に、書き先の型値として pure TyTerm を使う。binder の入力が一つなら既存のまま、0 または複数なら raw merge と同じ union/inter を二つの polarity に持つ。定義を足し合わせず port ごとに置き換える。generic projection は安定支持にない書き先のみへ式の値をコピーし、支持内の書き先条件は保持する。式の支持は allocation の report が追跡した旧 raw source に限る。rollback/replay 全体にこの結果を誤用しない（旧 raw 支持には履歴 raw slot も含むので、それを古い無限実列に適用しても rank は得られない）。
