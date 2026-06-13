# Yulang 仕様（spec/）

新世代パイプライン（`crates/sources → infer → poly`、入口 `crates/yulang2`）が
実装の根拠とする確定仕様を置く場所。`tasks/current.md` の方針どおり、設計が固まったものを
`notes/design/` からここへ昇格させる。旧 `yulang-*` 実装は動く oracle であって仕様ではない
（挙動が食い違ったら spec と手計算が正）。

ファイル名の日付プレフィックスは「いつ決めたか」の記録なので残してある。
テーマで引くときはこの地図を使ってね。

## 地図（テーマ別）

### 型推論コア（infer / poly）

4 本は相互に絡む。共通の土台は **不変区間** ＝ 中心を保存しない `(lower, upper)` 区間と、
同じ実引数を満たすための交差条件 `loA <: upB` / `loB <: upA`。この規則は role-system が定義元で、
ほかの 3 本がそれを参照する。

- [2026-06-02-role-system.md](2026-06-02-role-system.md)
  — role の通常引数・関連型、入力 variance の導出、**不変区間規則（交差条件の定義元）**、
  level 管理、簡約、解決と再帰的 discharge。
- [2026-05-31-effect-variable-subtractable.md](2026-05-31-effect-variable-subtractable.md)
  — effect subtraction を `stack(T, @S)` 型と不等式の重みで表す。floor / pop / weight、
  row 分解、注釈の上下分解、catch の制約、量化・cleanup。前半が規則、後半が手計算による検証。
- [2026-06-06-invariant-type-sandwich.md](2026-06-06-invariant-type-sandwich.md)
  — compact 表現（`CompactBounds` の enum 化）と sandwich による中心変数の消去。
  role-system の不変区間規則の上に立つ。
- [2026-06-04-method-selection.md](2026-06-04-method-selection.md)
  — `x.meth` の遅延解決、impl 候補の可視範囲、receiver demand を作らない理由。
  role 関連型による再帰解決ループの詳細は role-system 側に一本化。
- [2026-06-13-computed-fetch-value-restriction.md](2026-06-13-computed-fetch-value-restriction.md)
  — 変数取得時に計算が走る binding の値制限。`BindingFetch` metadata、量化境界の
  1 段引き上げ、multi-root SCC 内の computed fetch 診断、specialize の前提。

### 構文

- [2026-06-06-syntax-design.md](2026-06-06-syntax-design.md)
  — parser 実装から抽出した表面構文（字句・statement・expr・type・pattern・string・
  rule DSL・Yumark）。型推論・lowering・runtime の意味論は扱わない、独立した文書。

### 後段（単相化）

- [2026-06-07-principal-monomorphization.md](2026-06-07-principal-monomorphization.md)
  — 主型からの単一化（crate `specialize`）と単一化後 IR（crate `mono`）。infer の内部状態を
  覗かず、主型・erased IR・ref table だけから制約を作り直す。cast 挿入、関数 adapter、mono IR まで。
  computed fetch の値制限は 2026-06-13 の infer core 仕様を前提にする。
- [2026-06-13-runtime-guard-markers.md](2026-06-13-runtime-guard-markers.md)
  — specialize 後の effect hygiene を値と一緒に運ぶ runtime marker 仕様。`get_id`、
  dynamic `GuardIdList`、`add_id[n, path, id]`、関数起動時の push / pop、resumable effect を含む
  unwind 規則、lazy propagation と cost model。

### 参考文献

- [\[v1.9\] simple-essence-algebraic-subtyping_Marker.md](<[v1.9] simple-essence-algebraic-subtyping_Marker.md>)
  — Simple-sub 論文（Parreaux 2020）の Marker 変換。型推論コアの土台理論。

## 相互参照のかたち

- **不変区間・交差条件の定義** … role-system が定義元 → effect-subtractable /
  invariant-sandwich が参照
- **role 関連型の再帰解決ループ** … role-system が正 ← method-selection が参照
- **sandwich** … invariant-sandwich → 実装 `crates/yulang-infer/src/simplify/{compact,sandwich}.rs`
- **role 引数の中心表示** … role-system → 実装 `crates/poly/src/dump/type_format.rs`

## 注意：`notes/design/` の同名旧版

`notes/design/` に同名の 4 ファイル（role-system / method-selection /
effect-variable-subtractable / invariant-type-sandwich）があるが、これらは spec へ昇格する
前の **旧・短縮版**。現役の仕様は常にこの `spec/` 側を見ること。
