# C420: C12 の focused 検証

対象: `momota1029/yulang@676f02753db405bd1e5c8c67e6e6079891626e46` の Lean tree `c76d9eaa32800c156be5fe79f9970e0da74b32c6`。統合側の `integration/m1-final 24309085b67f46a328252917ef4035a4a436d190` は更新前 C419 の Lean tree と完全一致した。

## 何を検証したか

- [spec 6.1、role default](https://github.com/momota1029/yulang/blob/24309085b67f46a328252917ef4035a4a436d190/spec/06-roles.md#L14-L18) と [spec 10.7、位置による置換](https://github.com/momota1029/yulang/blob/24309085b67f46a328252917ef4035a4a436d190/spec/10-inference-core.md#L263-L265): 選ばれた実装の要求名に同じ explicit がなければ、実 role の同じ名の既定本文を読む。同名 explicit に B6 がなくても fallback しない。別の名前の explicit があっても、該当名の default は使える。
- [RoleDefaultMeaning420](../../lean/Yulang/GeneralDeclarativeI65I74RoleDefaultMeaning420.lean): default の位置 0 は元の引数全体、explicit の head binder は field。数字が 0 と同じ場合でも、実台帳と固定先に異なる値が入る。真の位置、保持残余、元の typed tree を State から読む。
- [RoleDefaultReplay420](../../lean/Yulang/GeneralDeclarativeI65I74RoleDefaultReplay420.lean): 旧の明示宣言の照合を使い、実 role default は別途 native-aware な `ModeCoverage357.check` で全て照合。再帰 `tree` の実 `.declared []` が元 B6 に現れる場合も、その型木を実固定行へ保持する。型モードを旧 invariant だと偽らない。別の独立追試でも、実 native graph と矛盾する旧 invariant flag を後から与えると照合できないことを確認した。旧 header がこの実例を落とすことも同じ監査で確認した。
- [RoleDefaultCoherence420](../../lean/Yulang/GeneralDeclarativeI65I74RoleDefaultCoherence420.lean)／[RoleDefaultPlan420](../../lean/Yulang/GeneralDeclarativeI65I74RoleDefaultPlan420.lean): 実宣言・要求名・B6 plan が固定されれば、証人によらず元の診断木と台帳が一意。source-level の定理と executable checker の両方で調べた。同じ固定先に違う literal RHS があれば、成功分岐として扱わない。
- [RoleDefaultRule420](../../lean/Yulang/GeneralDeclarativeI65I74RoleDefaultRule420.lean) の `dictionary_sound_R12` と [RoleDefaultEntry420](../../lean/Yulang/GeneralDeclarativeI65I74RoleDefaultEntry420.lean) の `check_sound`。同じ State の全 fitting model の辞書と価値の定理、実 fitting model の存在、exact original ordinal、旧分岐の不変性、根 raw K2 の優先を別々に確認。

## exact replay

Lean 4.35.0、toolchain commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`。Git pin から再取得した source の `git hash-object`、完全な旧 barrel からの import-only 差分を照合し、`lake env lean --trust=0 -DwarningAsError=true` で focused source／standalone audit／追記 import を照合した。barrel の追記順は変更せず、新しい Plan の source を Coherence より先にコンパイルする依存順で再確認した。

| exact replay の範囲 | source | standalone audit | 公理報告 | 結果 |
|---|---:|---:|---:|---|
| C420 | 10 | 3 | 43 | PASS |
| C419–C420 | 20 | 5 | 83 | PASS |
| C01–C12 の対象差分 | 108 | 57 | 532（別宣言 528） | PASS |

標準公理 `propext`・`Classical.choice`・`Quot.sound` のみ。旧分岐を経由した最終入口の独立回帰 42 操作は、予期した真 24／偽 18 と一致。別の追試で、一つの State・一つの fitting model に二つの実 role の既定／明示を同居させ、台帳を交換できないことを確認した。選ばれた unary role の実署名では位置 1 以降が既定式に出現せず、既存 `Roles.defaultSubst` による位置置換と B4 の typed slot が実際に使う位置で一致することも別途検証した（いずれも表の集計外）。非対応の false は言語の拒否ではない。凍結二ファイルは blob ID だけ照合し、内容を読まず編集もしなかった。

### exact blob

- `lean/Yulang/GeneralDeclarativeI65I74RoleDefaultSource420.lean`: `25b2bcd00ff2e76d4d327bb6e48b07607beae3f0`
- `lean/Yulang/GeneralDeclarativeI65I74RoleDefaultReplay420.lean`: `b5d8b4cb1728df37a522626b30af0a396a57d213`
- `lean/Yulang/GeneralDeclarativeI65I74RoleDefaultRule420.lean`: `a99a546db6c5c829e26e99a64a35984e6a76e653`
- `lean/Yulang/GeneralDeclarativeI65I74RoleDefaultReport420.lean`: `b36ef22e7c820f46c50ceca181dfbdf50e096f1f`
- `lean/Yulang/GeneralDeclarativeI65I74RoleDefaultEntry420.lean`: `222fb36f4d4b4e0a6608109986fc279c65fac9c8`
- `lean/Yulang/GeneralDeclarativeI65I74RoleDefaultLocator420.lean`: `347bff54eceb1c3a6eb12e821577db2284a72459`
- `lean/Yulang/GeneralDeclarativeI65I74RoleDefaultMeaning420.lean`: `e8d366874b06a345616d77ccbc07bc34e17d3091`
- `lean/Audit/Cycle420I74RoleDefaultCore.lean`: `72143a5fc6e0062df5080e74943690e1658a9171`
- `lean/Audit/Cycle420I74RoleDefaultSpec.lean`: `efcbf897204b956b57f03a108b75f256d17beeab`
- `lean/Yulang/GeneralDeclarativeI65I74RoleDefaultPriority420.lean`: `ee98b8866c69d61085c2fed8d1361a633860995e`
- `lean/Yulang/GeneralDeclarativeI65I74RoleDefaultCoherence420.lean`: `96fbafdaeae8e425f959c5e6778afe6c98be6674`
- `lean/Yulang/GeneralDeclarativeI65I74RoleDefaultPlan420.lean`: `ed05e7272dbf7ea779ae5aacbd59fdd7a2bc27ee`
- `lean/Audit/Cycle420I74RoleDefaultNative.lean`: `8920e204aadfd6fff6ee6f129434522b4164b2fe`
- `lean/Yulang.lean`: `8bf0020ecccb7fd21f216a5792fc03c74d0aa0d5`

## 対象外

一点の二 field record・可視一候補・where なし・出力一つ・C403 の固定行へ exact reification がある範囲。仕様の `char` を他の primitive に置き換えていない。一般の制約矛盾診断、B6 の推論側の証明、全 Lean suite、Rust、NoFalseRejection、停止性は未実行・対象外。C13–C22 の 10 行は未完了。
