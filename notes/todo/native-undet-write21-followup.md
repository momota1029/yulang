---
title: native-undet-write21 補足 — CPS lowering は正しかった
date: 2026-05-11
---

# write21 追補：CPS lowering は正しい、問題は別の場所

## 訂正

write21-report.md で「CPS lowering で `guard: n > 1` が消えている」と書いたが、
**これは誤り**。`debugs_std_undet_once_cps_shape` の filter を一時的に広げて
`work__mono0` も dump させた結果、**work body の lowering は完全に正しい**こと
を確認した。

```text
work__mono0 cont 1:
  ListSingleton 1 + ListSingleton 2 + ListSingleton 3 + 2 ListMerge → list
  DirectCall each__mono1(list) → 11 (Thunk)
  ForceThunk(11) → 12 (= n)
  Literal Int 1, dest=13
  DirectCall std::ops::>__mono2(12, 13) → 14
  ForceThunk(14) → 15 (= n > 1)
  DirectCall guard__mono3(15) → 16
  ForceThunk(16) → 17
  Return(12)
```

`guard__mono3` も期待通り：

```text
guard cont 1:
  Branch cond=0 then=cont 3 else=cont 4
guard cont 3:
  Literal Unit, Continue cont 2
guard cont 4:
  Literal Unit, Perform reject(Unit) → cont 5
guard cont 5:
  Continue cont 2
guard cont 2:
  Return
```

つまり `guard(true) = Unit`, `guard(false) = perform reject; Unit`。完全に正しい。

---

## 真の残バグ：私の write21 fix の semantic ギャップ

`debugs_std_undet_once_skip_eval_layers` が `cps:1` で止まる本当の原因は、
**write21 fix の判定が「frame ベース」でなく「function ベース」**であるところ。

### 期待される flow

1. `Perform branch` で k1 capture（H_sub install eval = work_mono0 → DirectCall
   each_mono1 → cont 0 の eval。EffectfulCall fold_impl で eval は terminate 済み、
   ただし F_each_cont_12 frame として **active_handlers ごと保存**されている）
2. once branch arm → recursive once → ForceThunk(k true thunk) → Resume(k1, true)
3. Resume eval は each cont 10 → cont 7 → cont 8 で `Perform sub::return(1)`
4. **本来の意味論**：Resume eval は H_sub の **install eval ではない**ので、
   sub::return prompt=1 は match せず Propagate
5. Propagate しながら frame stack を遡り、**F_each_cont_12 に保存された H_sub** に
   到達してそこで match
6. H_sub arm → each_mono1 Return Plain(Int 1)
7. work_mono0 cont 1 の DirectCall each_mono1 の dest=11 に書かれ、続きの
   `ForceThunk(11) → n>1 check → guard(false) → Perform reject` が走る
8. reject は inner once (prompt=2) に match → reject arm → uncons queue=[k1] →
   k1 false replay → x=2 path → sub::return(2) → just(2)

### 実際の flow（write21 fix 後）

1-3. 同じ
4. **write21 fix**：`frame.escape_owner_function == current_function` (= "each_mono1") が
   true なので、resume eval 内の sub::return が H_sub にいきなり match
5. JumpOrExit → cont 2 → each_mono1 Return Plain(Int 1)
6. consume F_post_fold_impl_cont_10 → fold_impl cont 10 → fold_impl cont 2 → Return
7. Resume eval の最終 return value = Plain(Int 1) → Resume の dest=15 に書かれる
8. once cont 8 (Resume thunk body) Return Plain(Int 1) → once cont 4 → opt::just →
   `just(Int 1)` → outer once Return `just(Int 1)` → cps:1

つまり write21 fix で「同じ function なら resolve」と判定したが、Resume eval は
**元の each_mono1 eval frame** とは別の eval frame。H_sub の install scope は
frame identity で区別されるべきだった。

### なぜ frame ベースでないと駄目か

`each_mono1` 関数を複数の eval frame で並行して実行している状況：

- 元 eval (work_mono0 → DirectCall) … H_sub install 済み、EffectfulCall で
  terminate されたが F_each_cont_12 として保存
- Resume eval (Resume(k1, true)) … 同じ each_mono1 function を target=cont 10 から
  実行

両者は同じ function の continuation を実行しているが、**install scope は別**。
H_sub は元 eval のもの。Resume eval 内で起きた sub::return は元 eval の H_sub
まで届くべき（delimited continuation semantics）。

write21 fix の `escape_owner_function == current_function` 判定では、両者を
区別できない。

---

## write22 で取るべき方向

### 案 1：handler frame に install eval id を持たせる

- `CpsHandlerFrame` に `install_eval_id: u64` を追加
- 各 eval が起動時に fresh id を取得し、自身の InstallHandler で push する frame
  にその id を入れる
- handle_scope_return で `frame.install_eval_id == current_eval_id` ならマッチ
- これで frame identity ベースの判定ができる

### 案 2：resumption.return_frames から H_sub を復元

- Resume eval 起動時、`resumption.return_frames` を走査
- 各 frame の `active_handlers` の中で non-inherited な handler を取り出し、
  Resume eval の active_handlers に inject（**install scope を再構築**）
- これで Resume eval 内で sub::return → installed H_sub に直接 match
- ただし、その H_sub は **resume eval scope に install されたわけではない**ので、
  match して JumpOrExit すると意味論的に正しくない

### 案 3：write21 fix を refine — frame stack を見て decide

- handle_scope_return で frame.escape_owner_function == current_function かつ、
  **return_frames の中に同じ function の F_post がある場合のみ** match させない
- F_post が「自分が中身として実行中の関数の途中」を示すので、その F_post を
  pop して本来の install scope に届ける必要がある
- 複雑だが、現在の data 構造で実装可能

私の感触では **案 3** が一番現実的。frame stack を見て「これは intermediate eval
で本当の install scope はもっと上」を判定できる。

---

## 私の write21 fix を keep する判断

- 167 tests 全 pass、local choice 系 pass、regression なし
- cps:0 → cps:1 は trace frontier の前進（sub::return が H_sub まで届くようになった）
- 案 3 を実装するときに、私の fix を「function 一致 AND no-intermediate-F_post」
  に refine することで完成する

write21 fix を revert すると write20 状態 (cps:0) に戻り、frontier が後退する。
keep しておく方が write22 への足がかりになる。

---

## CPS lowering filter を一時的に拡張した件

`debugs_std_undet_once_cps_shape` test の `if !f.name.contains(...)` filter を
作業中に `"work"` と `"guard"` を含む形に書き換えて確認した。元に戻し済み。

---

## 触ったファイル（write21 全体）

- `crates/yulang-native/src/cps_eval.rs`:
  - `handle_scope_return` の inherited 判定に `escape_owner_function ==
    current_function` exception を追加

write21-report.md, write21-followup.md として記録。
