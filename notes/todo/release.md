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
  - `yulang-<target>.tar.gz` / `yulang-<target>.zip`
  - archive root: `bin/yulang[.exe]`, `lib/std`, README, licenses,
    `release-manifest.txt`
  - `lib/std` は binary の embedded std を `install std` と同じ経路で展開したもの。
    runtime/LS は archive 同梱 std に固定せず、通常どおり `YULANG_STD`、近傍 `lib/std`、
    versioned user std root の順で解決する。
  - playground `dist` は初回 release workflow には含めない。CLI/LS release が安定してから
    Pages/deploy job と接続する。
  - Zed extension はこの repo の `yulang-zed/` を source copy とし、別 repository
    `momota1029/yulang-zed` へ同期する運用を別 slice にする。
- playground deploy の stable / nightly 分離を決める。
  - stable playground:
    - README / 記事 / public docs から飛ばす先。
    - release tag または明示した stable commit から deploy する。
    - `main` の solver 改修を自動で直結しない。
  - nightly playground:
    - solver / std / docs の実験を触る先。
    - 壊れてよい代わりに、deploy commit と build time を表示できるようにする。
  - 初期は deploy script の出力先を分けるだけでよい。
    stable URL / nightly URL / docs のリンク方針は別 commit で固定する。
- cargo を介さない smoke を作る。
  - executable path を引数で受け取る。
  - `yulang install std`
  - `yulang check/run` with bundled std
  - `yulang server` startup（`YULANG_SMOKE_SERVER=1` で opt-in）
  - cache clear / cache path / cache format mismatch
- 初期 smoke script:
  - `scripts/release-smoke.sh`
  - `HOME` / `XDG_CACHE_HOME` / `YULANG_CACHE_DIR` を一時ディレクトリに向け、user cache を汚さない。
  - `YULANG_SMOKE_SERVER=1` で server startup も見る。
- archive smoke script:
  - `scripts/release-archive-smoke.sh`
  - archive を展開し、`bin/yulang[.exe]` と同梱 `lib/std/std.yu` を確認してから
    `release-smoke.sh` を呼ぶ。
  - `release-manifest.txt` の `contract_runner=1` を確認し、packaged binary と同梱 std で
    filtered `yulang contract tests/yulang/cases.toml` を実行する。
- installer smoke scripts:
  - `scripts/release-install-smoke.sh` / `scripts/release-install-smoke.ps1`
  - ローカル HTTP release directory から installer を実行し、custom prefix install、
    prefix 直下の versioned std root、`check` / `run` / `server`、default uninstall、
    `--purge-cache` / `-PurgeCache`、`--all` / `-All`、unsafe prefix rejection を通す。
- packaging script:
  - `scripts/package-release.sh`
  - host native build 済み binary を受け取り、embedded std を archive root の `lib/` へ展開する。
- GitHub Actions:
  - tag `v*` push で Linux x86_64、macOS x86_64 (`macos-26-intel`)、macOS arm64
    (`macos-26`)、Windows x86_64 を build。
  - 各 OS 上で package と archive smoke を実行。
  - `SHA256SUMS`, `install.sh`, `install.ps1` と各 archive を GitHub Release へ upload。
  - `*-alpha.*` など hyphen 付き tag は prerelease とし、GitHub latest にはしない。
- release build で playground が使う wasm artifact と CLI が使う std/cache の対応を固定する。
- README には「開発者向け cargo」と「利用者向け binary」を分けて書く。

## Installer contract

- `scripts/install.sh`:
  - Linux / macOS 用。
  - public entrypoint は `https://yulang.momota.pw/install.sh`。
  - default は GitHub latest full release。
  - alpha / beta / rc は GitHub prerelease なので `--version v0.1.0-alpha.1` のように tag を指定する。
  - archive checksum を `SHA256SUMS` で検証し、`~/.yulang/bin/yulang` へ入れたあと
    `YULANG_LIB_DIR=<prefix>/lib yulang install std` を実行する。
- `scripts/install.ps1`:
  - Windows x86_64 用。
  - public entrypoint は `https://yulang.momota.pw/install.ps1`。
  - `~/.yulang/bin/yulang.exe` へ入れたあと `YULANG_LIB_DIR=<prefix>/lib yulang install std`
    を実行する。
- `scripts/uninstall.sh` / `scripts/uninstall.ps1`:
  - public entrypoint は `https://yulang.momota.pw/uninstall.sh` /
    `https://yulang.momota.pw/uninstall.ps1`。
  - default は `~/.yulang/bin/yulang*` と `~/.yulang/lib/yulang-*` だけを削除し、
    将来の realm / band 用データは巻き込まない。
  - `--all` / `-All` で install prefix 全体を削除し、`--purge-cache` / `-PurgeCache`
    で artifact cache も削除する。
- site deploy:
  - installer / uninstaller は repository root を source of truth にする。
  - `npm --prefix web run build` の最後に `web/scripts/copy-installers.mjs` が
    `web/dist/install.sh` / `web/dist/install.ps1` と uninstallers へコピーする。

## Cache / std contract

- `POLY_CACHE_FORMAT` / `CONTROL_CACHE_FORMAT` の bump 漏れが release artifact に混ざらないようにする。
- std bundle の version、source hash、artifact format、contract runner capability を
  manifest に入れる。
- 将来の realm/band release freeze では、固定した source snapshot と resolution metadata に加えて
  published band root の `.yucu` を生成する。
  `.yucu` は依存 prefix 用の cache artifact であり、release の正本は source snapshot と
  resolution metadata に置く。`.yuir` / `.yumo` / `.yuvm` は exact program cache なので
  default release artifact には含めない。
- installer で入れた binary は、同じ prefix の `lib/yulang-<stdlib-version>` を
  `YULANG_STD` / 近場 `lib/std` の次、user default std の前に発見する。
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
