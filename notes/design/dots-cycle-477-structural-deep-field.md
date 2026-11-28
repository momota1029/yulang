# C477: 同一 source trace 上の有限 named field 経路

I-93 の正負を、生の式を変更せず、すでに検査された有限観測の型商で判定する。対象は一つの実 source/GD head receipt、既存の authored/raw ordinal を持つ capture trace、閉形式の既存 named cell。各 hop の有限データは既存の構造 action、元 AST の相対 pose、実 trace の mark の ordinal、同じ観測表の checkpoint。最初の field は C476 の独立に固定した FieldOrigin と一致する必要がある。

独立判断は NamedPathTrace の stop/step。各 NamedPathHop は元の実 source pattern・compiled query・その exact old raw row に対する独立 ReadStep、延長した compiled path の実 mark、実 child の名への一致、raw/author 行と点の一致、出発点の安全と到着点の checked bit を要求する。List fold が与えられた判断を完全に再生し、すべての実 edge、全 proper prefix の安全、終点の checked 型商と元の literal pose を保存する。報告にする場合は最後の action が field（空の tail は元の field）。正側は正長の constructor walk で同じ型へ戻り、負側は完全な checked class への帰還がない。

現段階は named-to-named。別の独立 source receipt を選ばない。途中 inline、scope の完全な生成、同一相で実 compiler が発行する元 source 選択は未証明。旧捕獲結果、Rust のパーサ位置、型値の一致のいずれもその発行を代替しない。未知を負としない。G04 の閉鎖や canonical checker の変更ではない。
