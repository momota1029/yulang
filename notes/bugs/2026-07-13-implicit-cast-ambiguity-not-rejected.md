# 通常の implicit cast が曖昧な候補を検出・拒否しない

日付: 2026-07-13。発見: Claude Sonnet 5 + Codex（generic role impl conformance
Stage 4 の cast policy 検討中）。
状態: **open / silent non-determinism**。Stage 3/4 の role impl conformance 作業とは
独立した既存問題。

## 症状

同じ `(source, target)` 型の組に対して複数の `pub cast` 宣言が存在する時、通常の
expected-type-directed な implicit cast はエラーにならず、宣言順に応じて黙って
最初に見つかった候補を選ぶ。

```yu
mod std:
    pub mod num:
        pub mod frac:
            pub struct frac { num: int, den: int }
    pub mod first_convert:
        pub cast(x: int): frac = frac { num: x, den: 1 }
    pub mod second_convert:
        pub cast(x: int): frac = frac { num: x, den: 2 }

my y: frac = 1
```

このプログラムは `check`/`run` ともに成功する。`first_convert`/`second_convert` の
宣言順を入れ替えると、`y` の実際の値（`den: 1` か `den: 2` か）も入れ替わる。

## 根本原因

`constrain_nominal_cast`（`AnalysisSession::route_constraint_events` から呼ばれる）は
`self.casts.candidates(source, target)` が返す候補を `to_vec()` した後、`candidates.len()`
が 0 かどうかだけを見て早期returnする。1 件かどうか・複数件かどうかの区別は無く、候補が
複数あってもそのまま全候補へ subtyping 制約を足すだけで、曖昧性チェックも診断も無い。

`crates/specialize/src/specialize2` 側も同じ構造を繰り返す。`constrain_direct_cast` が
`poly.cast_rules` の一致する全エントリへ制約を足し、emit 時に `cast_boundary_instance` が
呼ぶ `direct_cast_rule` は `arena.cast_rules.iter().find(...)` で最初に一致した value-cast
ルールを無条件に採用する。

診断側にも「曖昧な cast」用の variant が存在しない。`AnalysisDiagnostic` にも
`SpecializeError` にも cast 版の曖昧性エラーは無い。role/typeclass method 解決用の
`SpecializeError::AmbiguousTypeclassMethod` は存在するため、言語設計者は曖昧性検出という
概念自体は導入済みだが、cast には実装されていない。

## 実害

- 同じ `(source, target)` へ複数の cast が登録できてしまい、どちらが使われるかは
  宣言・import の順序に依存する非決定的な挙動になる。
- ユーザから見ると診断もエラーも出ないまま、意図しない cast が黙って選ばれうる。
- 大規模なコードベースで無関係なモジュールが同じ型変換を独立に定義した場合、
  静かに衝突する可能性がある。

## 境界

- 確認したのは value cast（`pub cast(x: T): U = ...`）の直接一致ケースのみ。
- generic cast scheme・型引数付きの cast 候補までは未確認。
- どちらの cast も同じ scheme（型シグネチャ）を持つケースで確認した。scheme 自体が
  食い違う場合の挙動（型エラーになるか、それも黙って片方が勝つか）は未確認。
- production の `check-poly-std` baseline（998/3/297/0）には現時点で影響していない
  （repository std に同じ組へ複数 cast を宣言している箇所は無いと推定されるが、
  網羅確認はしていない）。

## 関連

- `crates/infer/src/casts.rs`
- `crates/infer/src/analysis/session/*`（`constrain_nominal_cast` の呼び出し元）
- `crates/specialize/src/specialize2/candidate/surface.rs`（`constrain_direct_cast`）
- `crates/specialize/src/specialize2/emit.rs`（`cast_boundary_instance` / `direct_cast_rule`）
- `notes/design/2026-07-12-generic-role-impl-conformance-spec.md`（Section 18 point 3、
  cast policy の未確定事項）
