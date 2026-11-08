# record default effect の境界（cycle 2）

旧実機 `d4c8bc8fc`。新spec §3b.3 は default の照合時effectを認め、先行patternがmissなら後続defaultを評価しない。旧文書・前回実機ではpure defaultは左から右に動いた。今回はeffectの保持とhandler到達を切り分けた。

```yulang
act ping:
    our get: () -> int
our pick {a = ping::get()} = a
our handle(action: [ping] _) = catch action:
    ping::get(), k -> k 7
    value -> value
handle(pick {})
```

- check0、dumpのpickは `{a?: 'a} -> 'a | int`（ping行なし）、run1 unhandled ping。
- `pick` の戻りを `[ping] int` と明示してもcheck0、dumpはpingなし、run1。
- 戻りを `[] int` と明示してfield欠如で呼んでもcheck0、run1 unhandled ping。fieldありならcheck0/run0で9。
- defaultのない関数bodyで `ping::get()` を呼ぶ対照はdump `any -> [ping]int`、同じhandleを通して7。
- default式そのものを `handle(ping::get())` にすれば7。
- **直接 `catch (pick {}): ...` は7**。従って「defaultの効果は一切handleできない」とは言わない。明示action境界を通す形で差が出る。
- `case x: {a=ping::get()} -> a` を関数bodyにした形も外側handleではunhandled。
- inline `catch (case {}: ...):` はrun0でもrootが`<thunk>`だった。結果のintをforceした成功とは扱わない。追加force試行は構文エラーで未検証。

旧ソース `lowering/pattern.rs:529–553` はdefaultをlower_exprし、valueをfield値へ接続する。effectは `local_effect: Some` の場合だけ接続。`lowering/expr/lambda.rs` の `connect_lambda_pattern_annotation` は無注釈patternに `local_effect: None` を返す。これは上記表示差と整合するが、runtime adapterまで含む完全な原因証明ではない。

Leanの `CommonAlignedPatternSafeDefaults.typing_matches` は任意effectful defaultの定理ではなく、DefaultSoundという契約を仮定する旨を先頭で明記する。純粋で有限の具体defaultやX22成功から任意effectful defaultのsource統合を完了扱いしない。

新specの意味論を旧失敗に合わせて変更しない。B2/B6で取り込むべき回帰候補として残し、どの表面入口までeffectを保持するかは未確認。この監査はLeanビルドやsource-to-core意味保存を検証していない。

全コマンド・出力と失敗した構文試行も `runtime-cycle-2-effects-patterns.md` に保存。

標準prelude有りの対照でも外側handleはunhandled（0.207秒）、直接catchは7（0.217秒）。no-preludeによる未読込だけが原因とは説明できない。
