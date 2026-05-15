# Native Remaining Failure Matrix

このメモは、native backend の「最後の穴」を、実装対象として追える粒度へ分解する。
広い TODO ではなく、observable な失敗・未確認・意図的な prototype 境界だけを並べる。

## Policy

- native の意味論 oracle は引き続き VM。
- source syntax ではなく、型変換後 runtime IR / CPS IR / evidence を基準にする。
- unsupported 判定は IR node / lane / value kind から出す。関数名や module 名の文字列特例にしない。
- 表層で thunk 構文を増やす方向には寄せない。thunk は型変換後の `ExprKind::Thunk` / `ValueToThunk` / boundary evidence として扱う。
- `docs/native-backend.md` は外から見た進捗表、`tasks/current.md` は作業ログ、このファイルは残穴の failure matrix とする。

## Matrix

| ID | Area | Current status | Failure / uncertainty | Next action | Exit condition |
| --- | --- | --- | --- | --- | --- |
| N1 | Type-converted thunk values | CPS-level record/list storage, list index, multi-force, string return, runtime `ExprKind::Thunk` list/index/`BindHere`, and source lazy operator results in tuple/list positions are covered. | Source regression coverage still does not show lazy/thunk-like values through named structural positions such as record or variant payloads; record value-field selection currently mixes in a separate source selection issue. | Add source regressions for lazy operator results in record/variant positions where the type-converted IR produces thunk adapters and source selection is unambiguous. | Source-level forced CPS repr executable tests cover tuple, list, and at least one named-field structural position without leaking visible thunk values. |
| N2 | Thunk boundary hygiene after storage | CPS-level boundary thunk in list/index/force keeps active boundary and skips the blocked inner handler. Direct source callback hygiene is covered without structural storage. | Source-level callback storage still needs a clean type/selection shape before it can become a regression; returned effectful thunks may still miss caller handler / guard re-entry in less direct runtime IR shapes. | Add source-shaped or runtime-IR regression where a stored or returned callback thunk performs under an outer handler after crossing a local handler. | VM, CPS eval, CPS repr eval, and Cranelift JIT agree for stored and returned callback hygiene. |
| N3 | Closure values in structural values | Source closures in records/lists can be selected and called, including scalar and string captures. | Value backend still rejects closure roots embedded in value-lane structural positions; CPS repr covers the intended path. | Keep value backend rejection explicit and route closure-bearing roots to CPS repr via structured unsupported reason. | `yulang native` chooses CPS repr for closure-bearing structural roots and reports the value-backend reason when debugging. |
| N4 | General heap value lane | CPS repr can print tuple/list/record/variant/string prototype heap values. | Runtime still uses boxed `VmValue`-like handles in several paths; compact native layout is not complete. | Treat compact layout as post-mainline optimization; keep current handles documented as prototype heap value lane. | No user-visible native feature is blocked by the prototype lane; docs clearly mark layout as internal/prototype. |
| N5 | Fallback / playground surface | CLI default selection is documented; value backend falls back to CPS repr for explicit unsupported cases. | Playground/deploy native option and failure surfacing may not match CLI selection rules. | Audit web entrypoint and expose the same backend selection/fallback message. | Playground native mode uses the same selection policy as `yulang native` or documents that it is VM-only. |
| N6 | Package / artifact workflow | Native artifacts default to `target/yulang`; object/exe modes exist. | Compiled-unit cache, realm lock, and install/build workflow are still planned. | Keep outside semantic-completion milestone; track under package/cache work. | Native semantic milestone can ship without cache/install; release docs mark cache as future work. |

## Immediate Order

1. Close N2 with one stored callback hygiene regression.
2. Make N3/N5 visible through structured selection diagnostics.
3. Close the named-position tail of N1 once record/variant source selection gives a clean regression shape.
4. Leave N4/N6 as documented prototype / packaging work unless they block release.

## What Counts As Native Complete For This Pass

- `sub` / `return` / shallow handlers / finite nondet agree with VM on the CPS repr executable path.
- Effectful thunks that are introduced by type conversion can be stored, selected, forced, and still carry boundary evidence in covered structural paths.
- Closures/resumptions are callable after flowing through the structural paths used by std nondet and common callbacks.
- Unsupported native roots are rejected or routed by structured reasons, not silent name-based special cases.
