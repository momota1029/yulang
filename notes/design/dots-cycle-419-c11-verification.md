# C419: C11 の focused 検証

対象: `momota1029/yulang@67bc8f0a7190cfcd6f39b574cf66b2f2e5060691` の Lean tree `c041981373f6e24053ab62e8795f5ea61161eb5a`。元の `integration/m1-final` `7d08c65efe086841811feb18e3391eaf2223aeda` の Lean tree は C418 と完全一致した。作業先は `work/dots-main` のみ。

## 仕様と局所規則

[spec 6.5 の Pick 宣言](https://github.com/momota1029/yulang/blob/7d08c65efe086841811feb18e3391eaf2223aeda/spec/06-roles.md#L395-L406) のうち、元の record が根拠のある一点で、`x:int,y:str` の二 field・別々の binder・where なし・出力一つの実例を扱う。非点／未完了 W までの例や、`Index str int … char` 自体ではない。[このピンの `Inference.Base`](https://github.com/momota1029/yulang/blob/7d08c65efe086841811feb18e3391eaf2223aeda/lean/Yulang/Types.lean#L13-L15) に `char` はないため、別の primitive に置き換えて例を通したとは扱わない。C11 の範囲は、**非空の既知入力**から元の明示 B6 RHS が固定出力に届く実経路。

- [局所規則と健全性](../../lean/Yulang/GeneralDeclarativeI65I74ExplicitPickRule419.lean): `selected_pick_local_sound419`、`dictionary_sound_R11`。独立した元の record head、元の捕捉、元の B6 と保持済みの行から同一モデルの意味を証明する。旧規則を左分岐にそのまま残す。
- [データ分岐・固定した健全性](../../lean/Yulang/GeneralDeclarativeI65I74ExplicitPickEntry419.lean): `check_sound`、`previous_entry_unchanged419`。入力は行添字・宣言添字・raw 根の有限検査データだけ。候補の選択、RHS、固定先、出力順や結論の証明は証人に入れない。未対応の `false` は仕様の拒否ではない。
- [意味](../../lean/Yulang/GeneralDeclarativeI65I74ExplicitPickMeaning419.lean)／[位置の照合](../../lean/Yulang/GeneralDeclarativeI65I74ExplicitPickLocator419.lean): 実 binder の三位置、および residual に正確に戻る。`retained_output_is_same_field_in_every_fitting_model419` は同じ元 field を返すこと、`check_has_original_typed_write_at_supplied_locator419` は元の宣言順・出力順 0・当該固定行を示す。二つの独立した行添字が同じ式を指しても、論理上の出力順や台帳は変わらない。元の固定先に別の右辺の literal 行もある場合、C11 の肯定分岐には入らない（一般の型エラー判定は加えていない）。
- [独立な優先・一意性](../../lean/Yulang/GeneralDeclarativeI65I74ExplicitPickPriority419.lean)／[台帳の整合](../../lean/Yulang/GeneralDeclarativeI65I74ExplicitPickCoherence419.lean): この狭い成功範囲で旧選択・旧診断は重ならず、異なる受理証人も同じ元宣言と台帳を返す。根の raw K2 は未確認 B6 によって隠れない。検査経路の外の実循環を持ちなおかつ `Fits` を満たすモデルでも、元の辞書を得る。

## 追試

Lean 4.35.0（toolchain commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc）。公開 pin から blob を独立に取り直し、git hash-object、元の barrel 全文との import-only 差分を照合。単体の lake env lean --trust=0 -DwarningAsError=true を各 source／standalone audit と追記 import に実行した。

| exact replay の範囲 | 追加 source | standalone audit | 公理報告 | 結果 |
|---|---:|---:|---:|---|
| C419 | 10 | 2 | 40 | PASS (exit 0) |
| C418〜C419 | 20 | 5 | 82 | PASS (exit 0) |
| C01〜C11 の作業差分 | 98 | 54 | 489（別宣言 485） | PASS (exit 0) |

公理は propext・Classical.choice・Quot.sound のみ。これは C01〜C11 に限った追試であり、全 Lean ファイルの build ではない。

最終入口で C01〜C11 の正負 32 操作をまとめて再実行し、予期した真 19・偽 13 に一致。行位置と元宣言順を別々に変更した試験、元 fixture の 8 種の位置をそれぞれ 8 通りに変えた有限試験、別の右辺が同じ固定先にある場合の負例、独立した元宣言からの診断木・台帳の一意性の確認も通った。この段落の開発時独立追試は、別の右辺の standalone 負例を除いて表の集計外である。

### C419 の exact blob

- `lean/Yulang/GeneralDeclarativeI65I74ExplicitPickOutput419.lean`: `d3075fbfe06ba0b3e8d00bf06d411c027f3d6710`
- `lean/Yulang/GeneralDeclarativeI65I74ExplicitPickSource419.lean`: `294c0eb9ca0dee6259f9cf0b64e1931110742f6f`
- `lean/Yulang/GeneralDeclarativeI65I74ExplicitPickReplay419.lean`: `4cd0f9f86760b74ac8935bd61a6bb8c16ff96242`
- `lean/Yulang/GeneralDeclarativeI65I74ExplicitPickRule419.lean`: `1ec64acbad91b5bf9876fdf3c74d42d698de4a62`
- `lean/Yulang/GeneralDeclarativeI65I74ExplicitPickReport419.lean`: `c23c559024aab3f616bf02558dfa9248e6c46603`
- `lean/Yulang/GeneralDeclarativeI65I74ExplicitPickEntry419.lean`: `fe2d848de46e2a0758df34e10eac98c42994ee1f`
- `lean/Audit/Cycle419I74ExplicitPickCore.lean`: `a2a203a9f1203cf78041b953bfe11356d31ab5bb`
- `lean/Audit/Cycle419I74ExplicitPickSpec.lean`: `dc3d8341fb99f231c99c936030644554ba6f0110`
- `lean/Yulang/GeneralDeclarativeI65I74ExplicitPickMeaning419.lean`: `a86f0325c882294473f51fc273a4e834c5193cdb`
- `lean/Yulang/GeneralDeclarativeI65I74ExplicitPickPriority419.lean`: `194e5be6e98952e8b1b89ca7c645e748e762e42b`
- `lean/Yulang/GeneralDeclarativeI65I74ExplicitPickCoherence419.lean`: `99d586d6a9462882c02673022f87098174669ca0`
- `lean/Yulang/GeneralDeclarativeI65I74ExplicitPickLocator419.lean`: `649d9bfa827d50d3471cd185a18f05e0d74f3e93`
- `lean/Yulang.lean`: `54f6876951dc0f14a8acbf247039d1363ac24232`

同じ State の全 fitting model に対する定理、実 fitting model の存在、元台帳を持つ具体例、根 K2 優先、非通過の実循環での同じ辞書、および間違った出現・宣言順・出力順・固定先・元本文・型木・残存行・出力数の負例を standalone audit から確認した。凍結対象は blob ID の一致だけ調べ、内容を読まず、編集もしなかった。追加モジュールと同じ差分で `lean/Yulang.lean` に import だけを追記した。

一般の制約矛盾診断は加えていない。この健全性は固定仕様どおり同じ State の全 `Fits` に対するもの。全 Lean suite、Rust、solver の NoFalseRejection、停止性は未実行・対象外。`C12–C22` の 11 行は未完了。
