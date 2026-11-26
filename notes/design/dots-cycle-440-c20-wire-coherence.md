# C440 — 別 raw 行証明の同一適合モデル内での整合性

新しい scoped checker で二つの元の locator が同じ状態・同じ request に対して成功したとする。二つが返す結果、可視宣言、binder 名は一致する。任意の同じ適合モデルで、元の head と interval の両端名が一致し、両方の inner raw 行の指す中心の型が同値になる。実際の名前が同一とは言わない。元の raw outer/inner の unary nominal 方程式を同じ model で二段階に反転して得るので、単なる同じ report や入力 provenance の仮定から型の同値を作らない。

追加の手元対照では同じ original .listBox 入力・同じ origin・二つの raw inner rows で中心 locator 3 と 5 を実際に判別、両方が実入口で true で同じ元の状態に適合モデルも構成した。この対照は production の引数制約追加ではない。「一つのモデルの中では同値」と「別々の二適合モデル間で同じ中心名の値が変えられる」は両立する。

`two_accepted_nested_wires_agree440` および元 source に関する三つの補題: 公式 Lean 4.35.0 strict 個別 build、standalone Audit 4 行は標準のみ。今回の追加は C20 の既存 entry を変えない。
