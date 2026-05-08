# Yulang TODO 索引

このディレクトリは Yulang の作業バックログ。`tasks/current.md` より広い範囲を扱う。
現在の作業は `tasks/current.md` に絞り、ここには設計上の問い、保留中の作業、
長めの実装トラックを置く。

## 現在の方向

Yulang には、コア言語の形、動く VM、wasm playground、標準ライブラリの試作、
ホスト effect、compiled-unit cache の試作、スクリプト言語としての体験を示す
例が揃ってきた。

次の大きなトラックは次の通り。

1. ネイティブ品質のコードへコンパイルする
2. パースを Yulang / ライブラリ側の第一級機能にする
3. ホスト / ファイルシステム仕様を安定させる
4. 静的解析と playground の遅延を低く保つ
5. 公開契約として diagnostics、docs、examples を改善する
6. 言語機能を小さく確かめられるテスト基盤を育てる

## 進行中のトラック

- `native-backend.md`
  - CPS / 明示的な control IR
  - Cranelift backend
  - VM と native の比較
  - 詳細設計: `../design/native-backend-plan.md`, `../design/cps-effect-lowering-plan.md`
- `parser-combinators.md`
  - parser result / error 型
  - 最小 combinator kernel
  - cut / commit と error merging
- `host-filesystem.md`
  - filesystem API の形
  - capability policy
  - `result` より先に詰める error handling
- `static-analysis-speed.md`
  - principal evidence execution
  - compiled-unit cache
  - playground latency の計測
- `language-surface.md`
  - 残っている言語機能と仕様の隙間
  - `error` sugar
  - `result`、casts、effects、optional records、references
- `diagnostics-docs.md`
  - source frame
  - ユーザー向け diagnostics
  - examples と public docs
- `testing.md`
  - Yulang code から書けるテスト
  - CLI / playground examples の regression 化
  - diagnostics / runtime behavior の fixture 化

## 近い優先順位

今の推奨順。

1. 安定した host API を進められる程度まで error handling を設計する
2. 意図的に小さい初期 subset から CPS / Cranelift 境界ノートを書き始める
3. static-analysis speed 作業は計測を保ち、hot path に debug evidence を増やさない
4. error / result / error reporting の語彙がもう少し固まってから parser combinators を設計する
5. 小さい言語機能を安心して増やせるように、Yulang-facing test API の最小形を決める

## 運用ルール

- `tasks/current.md` は短く、実行寄りに保つ。
- 大きめの保留案はこのディレクトリに置く。
- TODO ファイルには設計全体を重複させず、design note へのリンクを置く。
- TODO が実装作業になったら、具体的な次の一手を `tasks/current.md` に移す。
