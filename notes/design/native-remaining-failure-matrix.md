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
| N7 | Top-level destructuring bindings | Direct `case` structural patterns run through CPS repr for tuple/list/list-spread/record/record-spread/record-default/guarded/variant payload cases. Top-level list and record-spread destructuring now return `42` on the default native CLI by routing to CPS repr with `structural pattern binding`. | Forced value-backend execution now rejects this shape as unsupported instead of generating a crashing executable. | Keep it outside the value backend until value-lane structural binding parity is intentionally implemented. | `notes/bugs/native_top_level_destructure_binding_recurses.yu` returns `42` on VM, default native, and forced CPS repr; forced value backend reports `top-level structural pattern binding`. |
| N8 | Handler escape through fold / for | Outer `sub` catches a callback `return` thrown inside `for`; CPS repr Cranelift now short-circuits the skipped force/apply chain instead of letting it overwrite the caught result. | Fixed for finite-list `for` return and `examples/04_sub_return.yu`; covered by `runs_for_loop_return_escape_through_cps_repr`. | Keep this as a regression when changing handler-arm return routing. | `notes/bugs/native_for_loop_escape_keeps_running.yu` and `examples/04_sub_return.yu` match VM on forced CPS repr. |
| N9 | Open-range `for` `last` result | Fixed: `examples/03_for_last.yu` and `notes/bugs/native_open_range_for_last_returns_payload.yu` return `5` under forced/default CPS repr. | Scoped abort now keeps local handler-arm values inside the recursive range/fold chain, then consumes the short-circuit at the loop boundary so the following expression runs. | Keep this as a regression when changing `ScopeReturn`, return-frame thresholds, or abort routing. | `runs_open_range_for_loop_last_through_cps_repr` covers the source shape. |
| N10 | Heap values returned from handler/resumption chains | Fixed: recursive handler/resumption flow now returns `(9, "3\n6\n")` on forced CPS repr. | ScopeReturn updates stale thunk payloads after force, duplicate selected handler env entries are read newest-first, and JIT `EffectfulForce` now forces thunk bodies with the pushed post-continuation frame inherited rather than consumable. Root abort payloads are forced after discarding stale prompt-exit frames. | Keep the source regression when changing handler env capture, `force_thunk_i64`, `EffectfulForce` eval context, root abort extraction, or ScopeReturn routing. | `runs_recursive_effect_handler_tuple_result_through_cps_repr` covers the source shape. |
| N11 | Open-range nondet `.once` principal elaboration | Fixed: `examples/06_undet_once.yu` runs on VM and default/forced CPS repr native with `:just (3, 4, 5)`. | Full apply-spine principal plans now win over stale complete single-apply evidence, and open-only `unit` substitutions are not treated as concrete support. | Keep this as a regression when changing principal elaboration plan selection or exported substitution normalization. | `runs_undet_once_open_range_guard_through_cps_repr` covers the source shape. |
| N12 | Nested mutable ref update through indexed refs | Fixed: scalar local refs and indexed list assignment agree with VM. CPS lowering now keeps non-tail `bind_here` continuation frames, handler env capture preserves source/target IDs through shadowing, and the JIT merges `ResumeWithHandler` sibling handlers back into restored return-frame snapshots so mutable-ref state does not roll back. | No known indexed-ref update mismatch remains. | Keep the small indexed-ref source regression around when changing `bind_here`, `ResumeWithHandler`, handler env capture, or native return-frame restoration. | `runs_indexed_ref_update_through_cps_repr` covers `my $xs = [2, 3, 4]; &xs[1] = 6; $xs`, and `examples/showcase.yu` root 1 matches VM as `[2, 6, 4]`. |
| N13 | Combined finite nondet + junction + method result | Fixed: VM, CPS eval, CPS repr eval, and Cranelift JIT agree on the reduced `all/any` + finite `each` + record method + `.once` case. | The mismatch was in the JIT runtime frame protocol. `force_thunk_i64` evaluated thunk bodies through a shared thread-local return-frame stack; when a thunk returned an unresolved `ScopeReturn`, the caller's frame snapshot was not restored, so later finite `each` resumptions missed the post-`each` method continuation and returned `:just 3`. Restoring all snapshots was too broad until scoped abort also stopped treating `frame_len == threshold` as still outside the handler boundary, which produced `:just 1`. | Keep this as a regression when changing `force_thunk_i64`, `ScopeReturn` frame-walk routing, scoped abort thresholds, or return-frame restoration after resumptions. | `runs_junction_method_undet_once_through_cps_repr` is unignored and returns `:just 18` under CPS repr JIT. |

## Immediate Order

1. Treat N1/N2 as covered for this semantic pass unless a new source-shaped
   runtime IR form appears.
2. Keep N3/N5 on structured backend selection and CLI fallback behavior.
3. Keep N7 out of the forced value lane until structural binding parity is implemented there.
4. Keep N9 as a regression when changing scoped abort / return-frame threshold
   routing.
5. Re-run N10 whenever changing selected handler env or ScopeReturn force propagation.
6. Keep N11 around principal elaboration changes; it prevents stale partial
   apply evidence from specializing open operator arguments to `unit`.
7. Keep N12 as a regression for nested mutable reference updates.
8. Keep N13 as a regression for JIT thunk force / scoped abort frame protocol.
9. Leave N4/N6 as documented prototype / packaging work unless they block release.

## What Counts As Native Complete For This Pass

- `sub` / `return` / shallow handlers / finite nondet agree with VM on the CPS repr executable path.
- Effectful thunks that are introduced by type conversion can be stored, selected, forced, and still carry boundary evidence in covered structural paths.
- Closures/resumptions are callable after flowing through the structural paths used by std nondet and common callbacks.
- Unsupported native roots are rejected or routed by structured reasons, not silent name-based special cases.
