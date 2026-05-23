# file_handle / monomorphize 引き継ぎ

最終更新: 2026-05-23 (Codex)

## 状況

`str.lines` / `line_view` は前コミット `b926015 Add string line views` で入り、通常の `my $s = ...; for line in &s.lines` は動く。
この後に、ファイルを `ref '[fs] str` として開き、その `str` を `lines` と同じ操作系で編集して、最後に dirty な file handle を flush する方向へ進めていた。

現在の作業ツリーは未コミット。大きく二系統が混ざっている。

- runtime/host 側: `file_handle` を VM 値として持ち、`open_text_raw` / `file_get` / `file_set` / `file_flush` を host effect として処理する変更
- monomorphize 側: `ref '[fs] str` や `line_view` の型引数が閉じない問題への修正途中

現時点で `RUSTC_WRAPPER= cargo check -q -p yulang-runtime` は通る。
ただし、目的の file-backed lines 編集テストはまだ通っていない。

## 未コミット差分

`git status --short` 時点:

```text
M crates/yulang-runtime/src/host.rs
M crates/yulang-runtime/src/monomorphize/pipeline/local_refresh.rs
M crates/yulang-runtime/src/monomorphize/pipeline/normalize.rs
M crates/yulang-runtime/src/monomorphize/pipeline/principal_unify.rs
M crates/yulang-runtime/src/monomorphize/pipeline/principal_unify/type_projection.rs
M crates/yulang-runtime/src/types/substitution.rs
M crates/yulang-runtime/src/vm/control.rs
M crates/yulang-runtime/src/vm/mod.rs
M crates/yulang-runtime/src/vm/model.rs
M crates/yulang-runtime/src/vm/tests.rs
M crates/yulang-sources/std/flow.yu
M crates/yulang-sources/std/fs.yu
M crates/yulang/src/main.rs
M lib/std/flow.yu
M lib/std/fs.yu
```

差分規模は `15 files changed, 735 insertions(+), 177 deletions(-)` 程度。

## runtime / host 側で入っているもの

`crates/yulang-runtime/src/vm/model.rs`

- `VmValue::FileHandle(VmFileHandle)` を追加
- `VmFileHandle` は `Rc<RefCell<VmFileHandleState>>`
- state は `path: Rc<PathBuf>`, `text: StringTree`, `dirty: bool`

`crates/yulang-runtime/src/vm/mod.rs`

- `VmError::HostIo(String)` を追加
- `VmFileHandle` を re-export

`crates/yulang-runtime/src/vm/control.rs`

- `ControlValue::FileHandle(VmFileHandle)` を追加
- basic host profile path で request handling 後に dirty files を flush

`crates/yulang-runtime/src/host.rs`

- `BasicHost` を追加し、stdout と file handles を持つ
- `fs::open_text_raw`: path を読み、handle を作る
- `fs::file_get`: handle 内の現在 text を返す
- `fs::file_set`: handle 内の text を更新し dirty にする
- `fs::file_flush`: dirty な handle をディスクへ書く
- root eval 終了時に `flush_dirty_files`

ここは方向性としてはまだ妥当。ただし `YULANG_DEBUG_HOST_REQUESTS` の env debug が残っているので、コミット前に消す。

## std 側で入っているもの

`lib/std/fs.yu` と `crates/yulang-sources/std/fs.yu`

```yu
type file_handle with:

pub act fs:
    my open_text_raw: path -> (int, file_handle)
    my file_get: file_handle -> str
    my file_set: (file_handle, str) -> unit
    my file_flush: file_handle -> int
```

公開 wrapper は概ね以下。

```yu
pub open_text(path: path): result (ref '[fs] str) fs_err = ...
pub open_text_or_throw(path: path): ref '[fs] str = ...
pub open(path: path): ref '[fs] str = open_text_or_throw path
```

`open_text_raw` を effect op にして、公開 `open_text` は `result (ref '[fs] str) fs_err` を返す。

`lib/std/flow.yu` と `crates/yulang-sources/std/flow.yu`

- `for_in` の callback effect row を `'e` として持ち回る変更が入っている

## 追加されたテスト

`crates/yulang-runtime/src/vm/tests.rs`

- `vm_host_flushes_file_handle_string_edits`
- 期待する動作:

```yu
{
    my path: path = std::path::of_bytes (std::str::to_bytes "...tmp...")
    my text: ref '[fs] str = case open_text path:
        result::ok text -> text
        result::err e -> e.throw
    for line: ref _ str in std::str::line_view text:
        if line.get() == "b\n":
            line[std::range::full()] = "B\n"
        else:
            ()
    text.get()
}
```

期待値は root result とディスク内容がどちらも `a\nB\nc`。

現状は通らない。
直近では runtime に入る前、monomorphize 後 validation で次に落ちる。

```text
ResidualPolymorphicBinding {
  path: std::str::line_view,
  vars: [t2386],
  source: TypeParams
}
```

重要: host debug で見た限り、失敗ケースでは `file_set` まで到達していない。
つまり「ファイルが変わらない」直接原因は、少なくともこの再現では runtime ではなく monomorphize 側で `line_view` の `ref<'e, str>` が `ref<Unknown, str>` へ潰れていること。

## monomorphize 側の現象

観測したログの要点:

```text
principal-unify runtime-required std::fs::open_text vars={t6235,t6282,t6283,t6346,t6347}
principal-unify runtime-slot std::fs::open_text result:
  result<Bounds(... ref<t6282, str> ...), fs_err>
  <= result<ref<Unknown, str>, fs_err>
...
skip std::fs::open_text reason=incomplete-principal-elaboration-plan
local-value text = ref<Unknown, str>

principal-unify runtime-required std::str::line_view vars={t2386}
principal-unify runtime-slot std::str::line_view arg:
  ref<t2386, str> <= ref<Unknown, str>
no-new-substitution
skip std::str::line_view reason=incomplete-principal-elaboration-plan
```

一時的に `open_text` が `ref<Row(fs), str>` まで specialized されるログも出たが、外側の `my text` へ伝播する時点で `ref<Unknown, str>` に戻っていた。

## 既知の危ない実装

ここが一番重要。

### まず消すもの

コミット前に必ず消す。

- `crates/yulang-runtime/src/host.rs`
  - `YULANG_DEBUG_HOST_REQUESTS`
- `crates/yulang-runtime/src/monomorphize/pipeline/principal_unify.rs`
  - `YULANG_DEBUG_LOCAL_VAR_REWRITE`
  - `name.contains("text")` の debug 条件

### path 名分岐

ユーザーから「path名で分岐するな」と明示指摘があった。
この方針に反するものが monomorphize 周辺に残っている。
これらは今回の続きで撤去・置換対象。

見つかっている箇所:

- `crates/yulang-runtime/src/monomorphize/pipeline/principal_unify.rs`
  - `local_var_ref_binding_context` 内の `is_std_var_ref_path`
  - `collect_type_var_effect_usage` 内の `is_std_var_ref_path(path) && index == 0`
  - `runtime_ref_value_args_compatible` / `runtime_ref_value_type_arg_compatible`
  - `named_variant_payload_from_type_args` の `ok` / `err` / `just` / `leaf` / `node` / `list_view`
  - `path_last_segment_is`
- `crates/yulang-runtime/src/monomorphize/pipeline/local_refresh.rs`
  - `named_variant_payload_runtime_type` の `ok` / `err` / `just` / `leaf`

補足:
`host.rs` の effect operation dispatch や `diagnostic.rs` の表示用 operator 名変換は、host/diagnostics の責務なので同じ扱いではない。
問題は monomorphize/type propagation の途中で、型の意味を path 文字列から復元していること。

### いったん入れて撤回したもの

直近で `project_ref_record_type` という形で、`std::var::ref` / `ref_update` の path を直接見て `ref` の effect arg を復元する試みを入れた。
これはユーザー指摘どおり悪い修正なので撤回済み。
現在 `rg "project_ref_record_type|is_std_var_ref_update_path|strip_ref_update_effect"` は何も出ない。

## 正しい直し方の方向

path 文字列ではなく、構造化 metadata を runtime IR / monomorphize へ渡す必要がある。

候補:

1. type definition surface を runtime `Module` か monomorphize pipeline metadata に持たせる
   - named type の type params
   - type param の kind/value/effect 用途
   - struct fields
   - enum variants と payload
2. `ref<'e, 'a>` の「第 1 type arg は effect row、第 2 type arg は value」という情報を path ではなく type declaration 由来の metadata で扱う
3. `result::ok` / `result::err` など variant payload の復元を、tag 名と path の文字列ではなく enum definition の variant index/payload metadata で扱う
4. `PrincipalSlotPathSegment` / `PrincipalSubstitutionCandidate` をもっと使い、annotation/context/variant payload 由来の候補から型引数を閉じる

今の runtime `Module` には type definitions が入っていない。
そのため、monomorphize が named type の構造を知りたいときに path 文字列へ逃げている。
ここが根本原因に近い。

## 直近で見るべき入口

- `crates/yulang-runtime/src/lower/lowerer.rs`
  - infer の principal core から runtime IR へ落とす入口
  - `project_runtime_hir_type_with_vars` / `project_runtime_type_with_vars` が effect row を `Unknown` へ落としていないか見る
- `crates/yulang-runtime/src/types/project.rs`
  - `project_arg` / `project_type_arg_type` / `bounds_type_arg_is_effect_like`
  - `type_is_effect_like` は row 型だけを effect-like と見ている
- `crates/yulang-runtime/src/monomorphize/pipeline/principal_elaborate.rs`
  - `complete_principal_elaboration_plan_from_spine`
  - evidence の `substitution_candidates` を plan に流す場所
- `crates/yulang-runtime/src/monomorphize/pipeline/principal_unify.rs`
  - `complete_plan_from_runtime_effect_slots`
  - `project_principal_result_slot_substitutions`
  - `complete_plan_from_body_return_values`
  - `record_local_value_type_with_expected`
  - `rewrite_refreshed_block_let_initializers`
- `crates/yulang-runtime/src/monomorphize/pipeline/local_refresh.rs`
  - `refresh_expr_local_types`
  - `refresh_pattern_value_local_types`

## ここまで通った確認

通ったもの:

```bash
RUSTC_WRAPPER= cargo check -q -p yulang-runtime
RUSTC_WRAPPER= cargo test -q -p yulang-runtime closed_projection_keeps_partial_type_arg_bounds_when_actual_has_unknown_child
RUSTC_WRAPPER= cargo test -q -p yulang-runtime lower_effect_choice_projection_closes_required_row_var
RUSTC_WRAPPER= cargo test -q -p yulang-runtime vm_runs_source_ref_string_lines_edit_example
```

最後の二つは途中の状態で通したもの。現在の状態でも再実行すること。

失敗しているもの:

```bash
RUSTC_WRAPPER= cargo test -q -p yulang-runtime vm_host_flushes_file_handle_string_edits
```

失敗内容は `std::str::line_view` の residual polymorphic binding。

## 次の作業順

1. `YULANG_DEBUG_HOST_REQUESTS` と `YULANG_DEBUG_LOCAL_VAR_REWRITE` を削除
2. `vm_host_flushes_file_handle_string_edits` を再実行し、失敗が同じか確認
3. monomorphize 内の path 分岐を増やさず、named type / enum / struct の構造情報を渡す設計に切り替える
4. 既存の path 分岐を、可能なものから metadata 参照へ置換
5. `open_text path` の結果が `result<ref<Row(fs), str>, fs_err>` として `case` の `ok` arm に伝わり、外側 `my text` が `ref<Row(fs), str>` になることを確認
6. `line_view text` が `lines<Row(fs)>` に specialized されることを確認
7. その後に host debug で `file_set` が呼ばれるかを見る
8. `file_set` が呼ばれてもディスクが変わらない場合だけ runtime/host 側を疑う

## 注意

この作業では「目の前の fixture を通す」ための名前分岐を入れてはいけない。
`std::var::ref`、`std::result::result`、`std::str::lines` に見えるものも、monomorphize では path 文字列ではなく、宣言・型引数 kind・variant metadata・principal evidence から扱う。

今回の失敗は、runtime file handle そのものよりも、runtime IR へ落ちたあとに named type の構造情報が不足していることが大きい。
このまま path 分岐を増やすと、`result` / `option` / `lines` / 今後の user-defined ref-like type すべてで同じ問題を繰り返す。
