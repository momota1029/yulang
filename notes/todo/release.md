# Release / Packaging TODO

目的: cargo 前提の起動・配布から離れ、触る人が `yulang` binary と bundled std だけで試せる状態にする。

## 目標の形

```text
release artifact
  -> yulang binary
  -> std bundle / installed std
  -> playground dist
  -> cache format contract
  -> LS/Zed discovery path
```

公開前は native backend の再開ではなく、現行 VM/control pipeline を安定して配ることを優先する。

## First slice

- release artifact の単位を決める。
  - `yulang` binary
  - std source bundle or embedded std artifact
  - playground `dist`
  - Zed extension / LS metadata
- cargo を介さない smoke を作る。
  - executable path を引数で受け取る。
  - `target/debug/yulang install std`
  - `target/debug/yulang check/run` with bundled std
  - `target/debug/yulang server` startup（初期 script では opt-in）
  - cache clear / cache path / cache format mismatch
- 初期 smoke script:
  - `scripts/release-smoke.sh`
  - `HOME` / `XDG_CACHE_HOME` / `YULANG_CACHE_DIR` を一時ディレクトリに向け、user cache を汚さない。
  - `YULANG_SMOKE_SERVER=1` で server startup も見る。
- release build で playground が使う wasm artifact と CLI が使う std/cache の対応を固定する。
- README には「開発者向け cargo」と「利用者向け binary」を分けて書く。

## Cache / std contract

- `POLY_CACHE_FORMAT` / `CONTROL_CACHE_FORMAT` の bump 漏れが release artifact に混ざらないようにする。
- std bundle の version、source hash、artifact format を manifest に入れる。
- cache miss の理由を diagnostics ではなく build/cache status として出す。
- old cache を読む場合は、意味論 mismatch を source hash だけに頼らない。

## LS / Editor contract

- `yulang server` は release binary から起動できることを smoke に含める。
- Zed extension は cargo build 済みの local path に依存しない discovery を持つ。
- std root が無い時は、LS diagnostic ではなく起動時 error/status にする。

## やらないこと

- release 作業のついでに native backend を復活させない。
- cargo install だけを public install story として固定しない。
- cache format bump を手順書だけに頼らない。
