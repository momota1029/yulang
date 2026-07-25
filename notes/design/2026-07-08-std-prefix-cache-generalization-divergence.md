# 2026-07-08 std-prefix cache generalization divergence

Found as a side effect of the same-day Yumark Markdown-generalization performance investigation (see notes/design/2026-07-08-shadow-necessity-investigation.md for the earlier, narrower finding in the same overall investigation). Investigated via Codex MCP (gpt-5.6-sol, xhigh), delegated by Claude, read-only.

## The finding

The `std-prefix-hit` compilation path (using a cached, precompiled std) produces a **structurally different, more expensive-to-resolve** poly scheme than a cold (`--no-cache`) compile of the exact same program -- not just slower due to cache-loading overhead, but a genuinely different shape of type/role predicate.

Confirmed with `examples/zz_perf_repro_html.yu` (chosen because it was expected to be the *cheap* case -- its `html_node` intermediate boundary normally keeps the document's `YumarkRender` predicate "open"/variable-rich rather than fully concrete, which is exactly why HTML was fast throughout this investigation while Markdown's direct `repr=str` exposure was the whole problem):

| Path | Release median | Range |
|---|---:|---:|
| `std-prefix-hit` (warm cache) | 15.970s | 14.682-16.888s |
| cold `--no-cache` | 1.318s | 1.298-1.349s |
| `check-poly-std` | 1.016s | 0.995-1.049s |

A **12.1x inversion** -- caching makes this program dramatically *slower* to compile, the opposite of what caching should ever do. Confirmed real and repeatable across 5 alternating rounds (not measurement noise -- for contrast, an earlier apparent "22.213s" figure in this same investigation *was* later shown to be pure measurement noise; this one was specifically checked against that possibility and is not the same kind of artifact). Also confirmed not caused by disk (de)serialization overhead: even a fresh `std-prefix-build` that reuses the just-built std artifact immediately in-memory (no disk round-trip) still shows the same ~14s cost in the user-side resolution phase.

Current-HEAD debug-build medians independently reproduced the same inversion (31.849s warm vs. 6.846s cold), and an exact full-program cache hit (nothing changed since last compile) is fast (155ms) -- confirming the problem is specific to the *partial* std-prefix-only route, not caching in general.

## Mechanism

The `std-prefix-hit` route imports finalized std poly/namespace/lowering/runtime surfaces, then creates a fresh `AnalysisSession` with fresh constraints, role tables, and SCC state. Imported std definitions are seeded as **already quantified**; only the user-side suffix (the HTML repro's own code) joins the new inference graph.

The resulting poly schemes for the exact same program differ:

- **Cold compile**: one variable-rich, still-generic document `YumarkRender` predicate.
- **std-prefix-hit path**: a *fully concrete* document chain, plus an *additional* children-chain `YumarkRender` predicate.

That expanded, fully-concretized role problem triggers the same expensive multi-second role-resolution / dominance / filtering / finalization machinery that this investigation spent the rest of the day optimizing for the Markdown case specifically -- except here it's being triggered by the *caching mechanism itself*, on a program (HTML) that was specifically designed to avoid it.

Release-build phase localization of the std-prefix-hit HTML run: cached suffix body lowering 15ms, cached suffix analysis drain 26ms, "resolve cached suffix remaining selections" 14.301s (of which generalizing the user's `proof` definition alone was 13.906s).

## Why `check-poly-std` didn't show this

`check-poly-std` is **not cache-aware** -- it always collects all source files and calls one-shot `check_loaded_files` directly; `GlobalOptions.use_cache` never reaches that code path. It also stops before specialization/execution, but those phases together total only ~0.12s and cannot explain the gap on their own. This means `check-poly-std` cannot currently be used to validate or reproduce caching-related behavior at all -- a secondary, smaller finding worth remembering when choosing a command for future cache-related investigation.

## Open question -- this is the important part

**It is not yet established whether the warm/cold divergence is merely non-canonical (a different but equally correct representation that happens to be more expensive to resolve) or a genuine semantic/soundness divergence** -- i.e., whether the *type* a program is inferred to have could actually differ depending on whether it was compiled cold or via a cached std-prefix. This investigation established the performance mechanism (over-concretization at the std/user seeding boundary) but explicitly did **not** attempt to prove or disprove equivalence between the two resulting schemes.

If the two schemes are provably equivalent (just differently-shaped), this is "only" a performance regression, if a serious one -- and every program that touches role-polymorphic std types across the cache boundary is potentially affected, not just Yumark documents specifically. If they are *not* equivalent, this could be a real soundness/correctness question about what caching is allowed to change about a program's inferred type, which would need to be resolved before any performance fix is designed, not after.

## Recommendation

Do not attempt a quick fix. This touches the semantics of how cached std definitions get seeded into a fresh inference session at the cache/user boundary -- a more foundational, wider-blast-radius area than the role_solve-local hoists landed earlier the same day (commits 7bbf8291, caac51b1, 526f1258), which were narrowly scoped and independently safety-verified before landing. This deserves its own dedicated investigation session, starting with resolving the open equivalence question above, before any implementation is attempted.

## Files implicated

crates/yulang/src/cache.rs, crates/yulang/src/stdlib.rs, crates/yulang/src/main.rs, crates/infer/src/check.rs, crates/infer/src/analysis/session/lifecycle.rs, crates/infer/src/analysis/session/generalize.rs, crates/infer/src/compiled_runtime.rs, crates/infer/src/compiled_typed.rs.

Investigation: Codex MCP (gpt-5.6-sol, xhigh), read-only, 2026-07-08.

---

# 2026-07-26 追記: 等価性の問いに答えが出た（意味論的な差である）

上記「未解決の等価性の問い」に対し、敵対的な反例探索（Codex MCP gpt-5.6-sol xhigh、read-only）で
**反例が見つかった**。Claude が独立に再現・確認済み。

## 反例

```yu
pub render_one(x) = [x].show
```

```console
$ yulang --std-root lib --no-cache dump <f> --poly
pub render_one: any -> std::text::str::str

$ YULANG_CACHE_DIR=<dir> yulang --std-root lib dump <f> --poly
pub render_one: 'a -> std::text::str::str
                where std::core::fmt::Display('a | std::data::list::list 'a)
```

実行結果は両経路とも `run roots ["[7]"]`、診断も両経路 0 件。差は**公開される推論型だけ**である。

`any` は Yulang の Top 型であり、未知のプレースホルダではない。両者は alpha 変換でも
表示の違いでもない。

## どちらが正しいか

**warm（prefix 経路）が正しく、cold が残余述語を落としている。**

`[x].show` は `list 'a: Display` を要求し、std の
`impl (list 'a): Display where 'a: Display`（`lib/std/core/fmt.yu`）により `'a: Display` が要る。
したがって主型は `'a -> str where Display('a)` 相当であるべきで、`any -> str` は過少である。

cold の `any` が単なる表示上の未解決変数ではないことは、判別実験で確認した。

```yu
pub render_one(x) = [x].show
render_one (\y -> y)
```

```console
両経路とも: error [yulang.unresolved-method]: show: no role implementation satisfies this method call
```

つまり cold は**制約を内部では強制しているが、公開型には出していない**。
同一コンパイル単位の中では使用箇所で捕まるため実害が見えないが、その単位を別々に
コンパイルして消費する状況——prefix cache がまさに再現する状況——では、公開型が嘘になる。

## 位置づけの反転

本ノートも `std_prefix_cache_safety.rs` の保守ゲートも、「キャッシュ経路が疑わしいので
弾く」という前提で組まれている。今回の証拠はその向きを反転させる。差の原因は
**cold 側の generalization が役割述語を失うこと**であり、warm 側は正しい型を出している。

したがって「キャッシュを使うと型が変わるので危険」ではなく、
「**キャッシュ経路を通すと、cold が隠していた本来の型が現れる**」が実態に近い。

## 最初に分岐する場所

- cold: 全ソースを一緒に lower する。suffix から prefix 定義への参照は、対象がまだ live graph に
  いるため `OpenUse` になる。
- prefix 経路: std を finalized artifact として import し、`seed_quantified_def` で全 import 済み
  scheme を量化済みとして扱う（`crates/infer/src/analysis/session/lifecycle.rs`）。
  よって同じ参照が `InstantiateUse` になり、finalized scheme と役割述語を複製する。

この `OpenUse` / `InstantiateUse` の分岐が最初の因果点である
（`crates/infer/src/scc.rs`、`crates/infer/src/analysis/session/selection.rs`）。
canonical boundary artifact は最終的な binder/bound は保存するが、この live topology は保存しない。

## 安全ゲートの述語と、その穴

`crates/yulang/src/std_prefix_cache_safety.rs` は次の時ちょうど warm 再利用を拒否する。

```text
S(suffix) ∧ O(prefix)
```

- `S(suffix)`: suffix の CST の `ImplDecl` 内に `WhereClause` が存在する
- `O(prefix)`: cached runtime surface に open role boundary がある

反例は**この補集合の最大の領域**にある。suffix は `impl` を一つも宣言せず、
std 側の前提条件付き impl を**使っているだけ**なので `S = false` となり、ゲートは通してしまう。

ゲートは presence ベースであり到達可能性を見ない。また `OpenUse` / `InstantiateUse` の
遷移そのものをモデル化していない。

## この結果が意味すること

- **ゲートは緩められない。** 現在の証拠では、緩めると公開型の不一致がそのまま出る。
- ただしゲートを厳しくしても cold 側の過少な公開型は直らない。ゲートは「キャッシュを使わない」
  選択にすぎず、cold が出す型が正しくなるわけではない。
- したがって本件は「キャッシュの安全性」ではなく、**「cold の generalization が役割述語を
  落とすこと」**として扱い直すべきである。

## まだ未確定

- admitted な範囲で、コンパイル成否・診断内容・実行時の値まで変わる例があるか
  （公開型だけでなく）。
- `OpenUse` 分岐の後、role solver / generalizer のどの操作が `any` と残余述語を分けているか。
- 別コンパイル単位からこの食い違う公開インターフェースを消費した時の挙動。
- effects、casts、shadowing、再帰など、反例発見時点で攻撃を止めた他の領域。

調査: Codex MCP (gpt-5.6-sol, xhigh), read-only。反例の再現と判別実験は Claude が独立に実施。
