# nested undet `.list` JIT-only divergence — 縮約と仮説

> **RESOLVED**: `yulang_cps_set_resumption_anchor_from_selected_i64` で
> 派生 capture 時に inherited handler の threshold を slice 内の prompt-exit
> マーカー位置から再計算する `recalibrate_inherited_handler_thresholds` を追加。
> 全ての `runs_undet_*` テスト・縮約テスト・以下の CLI ケースが通過。
> 詳細は文末セクション参照。


## 状況

`crates/yulang-compile/src/lib.rs` に追加した 2 件の最小再現テストで
JIT だけが落ちる症状を絞り込んだよ。

| テスト                                              | 期待       | CPS eval / CPS repr eval | JIT       |
| ------------------------------------------------ | -------- | ------------------------ | --------- |
| `debug_undet_list_two_two_one_through_cps_repr`  | `[11, 12]` | OK                       | `[11, 2]` |
| `debug_undet_list_two_one_two_through_cps_repr`  | `[11, 21]` | OK                       | `[11, 20]` |
| `runs_undet_list_nested_each_sum_through_cps_repr` | `[11, 21, 12, 22, 13, 23]` | OK | `[11, 20, 2, 3]` |

つまり「**外側 `each` の二度目以降の resumption で、`+ inner each` の継続が継続として効かず raw 値が `list` の `v -> [v]` 腕に直接戻る**」というパターン。

CPS eval と CPS repr eval は OK なので、JIT layer (Cranelift backend) の差分。

## ハンドラ／フレーム構造の観察

`(each [1, 2] + each [10]).list` を `YULANG_CPS_JIT_TRACE=1` で観察すると、
`yulang_cps_resume_i64` 呼び出しは 6 回（id 重複あり 4 種類）。

```
rid=1, arg=1   ← 外 list の k1(true)
rid=3, arg=1   ← list(k1 true) 内側、内 list の k(true) など
rid=3, arg=0
rid=1, arg=0   ← 外 list の k1(false)  ← ここから症状開始
rid=6, arg=1   ← list(k1 false) 内側
rid=6, arg=0
```

rid=1 の captured `return_frames` (両 resume で共通) は 8 フレーム。
F#3 が `prompt_exit=2` の sub handler boundary、その上下にハンドラ snapshot
`[h1(p=1,ev=0,thr=0), h0(p=2,ev=4,owner_fn=4,thr_owner=10,thr=3)]` を持つ。

つまり外側 `each [1,2]` の `sub::sub { ... }` で install された h0 は
`return_frame_threshold=3` を持っていて、rebase 後の captured slice 上で
F#0..F#2 を「sub install 以前のフレーム」とみなす設定。これは初回 capture 時点では
正しい（最初の outer branch 時の真上 3 フレームが「sub install 以前」だった）。

## どこで `12` が失われるか

`rid=1, arg=0` の resume では:

1. `adjusted_frames`（= rid=1 が抱える 8 フレーム）を thread-local に差し替え。
2. 当該 chunk が iteration 1 を `()` で抜けて fold iteration 2 へ。
3. 二度目の `branch()` が perform される。**今の thread-local handlers は
   `[h1(p=1,ev=0), h1(p=7,ev=99), h0(p=2,ev=4,thr=3)]` で、`h1(p=7)` は
   `list(k1 false)` 用に呼び出し側で install された外側プロンプト。**
4. branch を catch するのは topmost h1 = `h1(p=7,ev=99)`、新しい k2 が capture される。
5. `merge (list (k2 true)) (list (k2 false))` の `list(k2 true)` で h1(p=8) install、
   k2 true を resume。
6. その chunk 内で `sub::return 2` が発火し、active handlers から
   `h0(p=2,ev=4,thr=3)` を引き当てて `return_frames.truncate(3)` する。

ここで「**truncate(3) が落としているフレーム集合に、`+ each [10]` を表す `Primitive(IntAdd)` 後続フレームが含まれていないか**」が中心の疑問。

CPS eval が通って JIT だけが落ちるので、論理的には：

- truncate そのものは sub の exit にきちんと飛ばすために必要、
- ただし JIT のスレッドローカル return frame stack 上では「sub install 時点での
  境界」と「現在 chunk が走っている境界」が同じインデックス座標に混ざっていて、
  thr=3 が現実の境界より深い位置を指してしまい、`+ each [10]` の post-frame まで
  巻き込んで捨ててしまう、というのが今回の本線仮説。

これは prompt-3 の表で言うと "JIT env / replay parity" のカテゴリで、
prompt-3 の指摘どおり Layer 1/2 では `eval_continuations` が完全新規の local state
を作るのに対して JIT は thread-local に追記してから差し替えるので、
threshold の絶対インデックス意味論がずれる、という構造。

## 似ているけど違うところ

`merge_resumption_handlers_native` は handler 列の merge 時に **threshold を rebase していない**。`rebase_native_i64_captured_handlers` は capture 側（`yulang_cps_set_resumption_anchor_from_selected_i64`）でのみ呼ばれていて、resume 側で新しい current handlers が prefix に挿入される際は threshold を補正していない。

ただ resume 側で thr を補正するだけだと意味論を変えてしまうから、見るべきはむしろ
**「resume 中に新しく capture された k2 の return_frames 内の h0 snapshot」** が
正しい threshold を持っているかどうか。

具体的には：

- resume #5（rid=6, arg=1）の captured frames に出てくる h0(p=2,ev=4,thr=3) を、
  k2 capture 時点でその時の thread-local stack の長さに対して **再 rebase していない** 可能性が濃い。
- もし k2 capture 時点で thread-local stack の中の h0 install 境界が実際には
  位置 3 ではなく位置 5 とかにある場合、thr=3 のままだと `+ each [10]` 由来の
  return_frames まで truncate で消してしまう。

## 確認に使ってほしい不変条件

```
ある resumption k の captured return_frames に含まれる handler frame の
return_frame_threshold は、その handler の install_eval_id における
「install 時刻の thread-local stack 上の長さ」ではなく、
**captured slice の中の「sub install 以前」フレーム数**を表すべき。
```

つまり k1 から派生した k2 の中の h0 snapshot の thr は、

```
(k2 capture 時点の thread-local stack 長) - (k2 capture 時点の sub install 以降のフレーム数)
```

であるべきで、これは k1 capture 時の thr=3 と一致するとは限らない。

検証手順：

1. `yulang_cps_set_resumption_anchor_from_selected_i64` で k2 を作るとき、
   captured frames 内の handler 各 snapshot に対して、現在の thread-local stack
   での実際の sub install 境界位置を計算し直す。
2. または、もっと安全策として、k2 の captured frames を作るとき
   handler snapshot の thr を「captured frame index で sub の prompt_exit が
   現れる直前」に再計算する。

## 仕掛けると当たりが見える小実験

```rust
// JIT trace を rid 付きで出す（既に prompt-6 で部分追加してたら戻してね）
eprintln!(
    "[JIT-CPS] resume: rid={} anchor={:?} arg={} captured_frames={} ...",
    resumption.debug_id, anchor, arg, format_return_frames(&resumption.return_frames),
);
```

`debug_undet_list_two_two_one_through_cps_repr` を `YULANG_CPS_JIT_TRACE=1` で
回すと resume が 6 件出る。**resume #5 (rid=6, arg=1)** の captured frames 内
の h0 snapshot を見て、その thr=3 が「captured slice 内で prompt_exit=2 の
直前まで」を指しているか確認する。指していなければ rebase 漏れの証拠。

## 別ルートの保険

もし threshold rebase で直らなかった場合、別の濃いところは：

- `restore_native_i64_return_frames_after_resume` の `debug_id` マッチで
  resume 中に push されたフレームが saved 末尾にぶら下がる挙動。これが起きると
  resume が積み足したフレームが outer caller の view に漏れる。
- `merge_resumption_handlers_native` で current handlers が anchor 前後に
  挿入されることで、captured handler の thr が指していた **handler list 中の
  位置** がずれて、後続の `sub::return` 検索で別の handler に当たる。

両方とも今回の症状（外側 `each` の 2 回目以降で `+` が消える）と整合性ある。
最初に threshold rebase を疑うのは、prompt-3 の "JIT env / replay parity" 仮説と
prompt-5 の "判定のデータ化" 方針の両方に沿っているから。

## 残しておいた regression

`crates/yulang-compile/src/lib.rs` の `tests` モジュールに最小 2 件追加：

- `runs_undet_list_outer_two_inner_one_through_cps_repr`：`(each [1,2] + each [10]).list`
- `runs_undet_list_outer_one_inner_two_through_cps_repr`：`(each [1] + each [10,20]).list`

---

## 解決した内容

仮説通り、原因は **派生 capture（k1 replay 中に生まれた k2）に紛れ込んだ
inherited sub handler の threshold が、k1 capture 時の slice index 意味論を
そのまま k2 slice に持ち越していた** こと。

### 修正

`crates/yulang-native/src/cps_repr_cranelift.rs` の
`yulang_cps_set_resumption_anchor_from_selected_i64` に
`recalibrate_inherited_handler_thresholds` を追加して、

- `install_eval_id < meta.install_eval_id` のハンドラ（= 既存 rebase 対象外の
  inherited handler）について、slice 内に同じ `prompt_exit.prompt` を持つ
  return frame を探し、その index を新しい `return_frame_threshold` として書き戻す。
- マーカーが slice に居なければ「install は slice より外」なので 0 を入れる。
- 同じ補正をトップレベル handlers と各 frame の handler snapshot 両方に適用。

これで sub::return が `route_scope_return.frame_walk` 経由で
truncate するとき、現実の slice 上での sub install 直前位置に揃う。
`+ each [10]` 由来の post-each frame が捨てられなくなる。

### 確認したテスト

| テスト | 結果 |
| --- | --- |
| `runs_undet_list_outer_two_inner_one_through_cps_repr` | ✅ `[11, 12]` |
| `runs_undet_list_outer_one_inner_two_through_cps_repr` | ✅ `[11, 21]` |
| `runs_undet_list_nested_each_sum_through_cps_repr` | ✅ `[11, 21, 12, 22, 13, 23]` |
| `runs_undet_logic_nested_each_sum_through_cps_repr` | ✅ `[11, 12, 21, 13, 22, 23]` |
| 他 `runs_undet_*` 全 11 件 | ✅ |
| `yulang-compile` 63 件 / `yulang-native` 192 件 | ✅ |

CLI でも：

- `cargo run -p yulang -- run --native --print-roots /tmp/x.yu` で
  `(each [1,2] + 3).list` → `[4, 5]`、
  `(each [1,2] + each [10]).list` → `[11, 12]`、
  `(each [1,2] + each [10,20]).list` → `[11, 21, 12, 22]` 復活。

### 既存の他テスト

`yulang-runtime` の VM テスト
`vm_host_handles_console_output_requests` /
`vm_handles_std_read_text_or_throw_not_found` は元から失敗していて、本修正と
無関係（VM/interpreter 側）。
