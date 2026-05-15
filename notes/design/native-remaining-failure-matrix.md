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
| N1 | Type-converted thunk values | CPS-level record/list storage, list index, multi-force, string return, runtime `ExprKind::Thunk` list/index/`BindHere`, source lazy operator results in tuple/list/record/variant positions, and record spread expressions are covered. | No immediate source-shaped structural leak is known. | Keep future structural thunk adapter cases on the same forced CPS repr source regression path. | Source-level forced CPS repr executable tests cover tuple, list, record, record-spread, and variant payload positions without leaking visible thunk values. |
| N2 | Thunk boundary hygiene after storage | CPS-level boundary thunk in list/index/force, record/select/force, and variant/payload/force keeps active boundary and skips the blocked inner handler. Direct source callback hygiene and list-stored callback hygiene are covered. | Returned/stored effectful thunks may still need broader real-world std coverage, but the known source-shaped list storage hole is closed. | Add future cases only when they expose a new runtime IR shape rather than duplicating the same list/index path. | VM, CPS eval, CPS repr eval, and Cranelift JIT agree for stored and returned callback hygiene. |
| N3 | Closure values in structural values | Source closures in records/lists can be selected and called, including scalar and string captures; backend selection now routes closure-value roots, record-contained closures, and list-construction primitive payload closures to CPS repr by structured `closure value` reason. | No immediate selection hole is known for closure-bearing structural roots; deeper closure layout work belongs to N4. | Keep future closure structural cases on the same IR-node based `closure value` reason. | `yulang native` chooses CPS repr for closure-bearing structural roots and reports the value-backend reason when debugging. |
| N4 | General heap value lane | CPS repr can print tuple/list/record/variant/string prototype heap values. | Runtime still uses boxed `VmValue`-like handles in several paths; compact native layout is not complete. | Treat compact layout as post-mainline optimization; keep current handles documented as prototype heap value lane. | No user-visible native feature is blocked by the prototype lane; docs clearly mark layout as internal/prototype. |
| N5 | Fallback / playground surface | CLI default selection is documented; value backend falls back to CPS repr for explicit unsupported cases. The web playground is marked as VM-interpreter-only. | If a future playground native mode is added, it must reuse CLI selection policy rather than inventing a separate fallback rule. | Keep native execution on CLI until a wasm/native execution story exists. | Playground native mode uses the same selection policy as `yulang native` or documents that it is VM-only. |
| N6 | Package / artifact workflow | Native artifacts default to `target/yulang`; object/exe modes exist. | Compiled-unit cache, realm lock, and install/build workflow are still planned. | Keep outside semantic-completion milestone; track under package/cache work. | Native semantic milestone can ship without cache/install; release docs mark cache as future work. |
| N7 | Top-level destructuring bindings | Direct `case` structural patterns run through CPS repr for tuple/list/list-spread/record/record-spread/record-default/guarded/variant payload cases. Top-level list and record-spread destructuring now return `42` on the default native CLI by routing to CPS repr with `structural pattern binding`. | Forced value-backend execution still crashes on the nullary binding shape. | Either fix value-backend nullary structural binding lowering or keep it outside the default route until value backend parity work. | `notes/bugs/native_top_level_destructure_binding_recurses.yu` returns `42` on VM, default native, and forced CPS repr; forced value backend is tracked as the remaining value-lane gap. |

## Immediate Order

1. Treat N1/N2 as covered for this semantic pass unless a new source-shaped
   runtime IR form appears.
2. Keep N3/N5 on structured backend selection and CLI fallback behavior.
3. Keep N7's forced value-lane crash out of the default route; fix it before claiming value-backend structural binding parity.
4. Leave N4/N6 as documented prototype / packaging work unless they block release.

## What Counts As Native Complete For This Pass

- `sub` / `return` / shallow handlers / finite nondet agree with VM on the CPS repr executable path.
- Effectful thunks that are introduced by type conversion can be stored, selected, forced, and still carry boundary evidence in covered structural paths.
- Closures/resumptions are callable after flowing through the structural paths used by std nondet and common callbacks.
- Unsupported native roots are rejected or routed by structured reasons, not silent name-based special cases.
