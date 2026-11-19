# Cycle 280 — 保持 effect の辺圧縮の対応

279 は current graph の membership を保つ置換で Step が存在すると証明したが、到着状態の履歴 effect に旧 graph が残るため、そのまま繰り返せない。現在と全ての版付き effect snapshot の raw 辺を独立に圧縮する。ID 固定化とは別（ここでは raw occurrence の辺 membership を保存）。

任意の effect を、親 packet・registry・準備・出力 ready の意味を変えず、その snapshot の辺だけを置換できる。任意の assignment に対し Effect.Holds / Live が不変。trusted facts の output だけ新旧 effect を対応させて、保持 snapshot の class 読み戻し・意味を transport する。旧 legacy effect は触らない。局所診断、merge、refresh、equate、reobserve への写像、install 時の new effect を足した後の関係を順に確かめる。任意の二つの辺列に対する関係として行い、歴史リストを等しいと偽って置き換えない。
