# 引き継ぎ: ラベル付き for（`redo 'outer`）の LoopLabel role が discharge されず漏れるバグ（2026-06-04）

## これは Codex への指示書
設計者（ユーザー）と claude で根因を完全局所化し、**fix 方向まで設計決定済み**。残りは「定義側 scheme 構築」の実装。潜って解いてほしい。**当て勘の使う側いじりは2回外しているので絶対に再発させないこと**（後述）。

## TL;DR
`labeled = for 'outer x in [1, 2, 3]: redo 'outer` が `LoopLabel<α> => unit` で漏れる（期待は `unit`）。
- `redo` は prelude の **prefix エイリアス**（`pub prefix(redo) 8.0.0 = label_redo`）。principal body は `Var(label_redo)`。
- `label_redo(label) = label.redo()` は lambda で role 制約 `LoopLabel<param>` を持つ。
- redo は body が `Var(...)` なので **OnDemandLambda（scheme 構築経路）に乗らず、自分の scheme（compact/frozen）が作られない**（`frozen=false, compact=false`）。
- その結果 `label_redo→redo→labeled` の role 制約伝播が**全部 空 subst**になり、role arg（中心 var）が値の適用 param と結ばれず**孤立**。`'outer` の具体 label が role arg に届かず、§決定1（境界に具体型1つで解決）が発火できずに漏れる。

**設計上ありえない＝バグ。** 設計者の見立て「instantiate で揃えるのは正しい。ただし場所は**定義側（redo の scheme 構築）**であって使う側ではない」。

## 最小再現 / 物差し
名指しテスト（全 cargo test はハングするので必ず名指し。`env RUSTC_WRAPPER=` を付けないと sccache がタイムアウトする）:
```
env RUSTC_WRAPPER= cargo test -p yulang-infer display::dump::tests::render_compact_results_lowers_loop_control_operators -- --nocapture
env RUSTC_WRAPPER= cargo test -p yulang-infer display::dump::tests::render_compact_results_lowers_labeled_for_in_stmt -- --nocapture
```
- `loop_control_operators`: `bare = for x: next`（=unit）/ `labeled = for 'outer x: redo 'outer`（=unit）/ `for_in = std::flow::loop::for_in`（=`Fold<α, item = β> => α -> (β -> [std::flow::loop; γ] ⊤) -> [γ] unit`）。
- `labeled_for_in_stmt`: `test`（=unit、`'outer.next()` を含む）/ `nested`（=unit、`redo 'inner` / `next 'outer`）。
- **全体物差し**: `env RUSTC_WRAPPER= cargo test -p yulang-infer display::dump::tests::render` → **現状 48 passed / 8 failed がベースライン**（このバグ修正で labeled/nested/bare が緑になり、回帰0・ハングなしを維持すること）。

## 背景（仕組み）
- prelude.yu:
  - `pub prefix(redo) 8.0.0 = label_redo`（line 16） / `pub prefix(next) = label_next` / `pub prefix(last) = label_last`（同型なので fix は3つ同時に効くはず）
  - `my label_redo(label) = label.redo()`（line 377）。`label.redo` はメソッド選択 → role 制約 `LoopLabel<label>`。
- flow.yu: `pub role LoopLabel 'a:` は `a.last/next/redo : () -> [_] never`。`label` struct と `label_loop::for_in` が `control_label`（label struct 値）を `f` に渡す。
- 使う側 `redo 'outer` の解決: `resolve_bound_def_expr`（`lower/expr/path.rs:364`）で **LetBound alias 経路（525-535）**に落ちる。理由は
  - `principal_body_is_lambda_value(redo)` = false（body が `Var`、lambda でない）→ OnDemandLambda 経路（455-511）を skip
  - `should_defer_unlowered_callable_ref(redo)` = false（principal_bodies に Var body 登録済み）→ defer 経路（512-524）を skip
  - 結果: `instantiate_role_constraints_for_owner(redo, owner, &[])`（**空 subst**）+ `constrain(Pos::Var(def_tv), Neg::Var(tv))`（値の浅いエイリアスのみ）。

## 確定した事実（再調査するな・時間を溶かすな）
`YULANG_DEBUG_ROLE_REF=1` の role 制約 instantiate ログ（`solve/selection/mod.rs:66-92`）で確定済み。DefId/var は実行ごとに変わるので**相対関係**で読むこと（下記は loop_control の一例）。

1. **instantiate の個数は最初から正しい**。labeled（owner=DefId 1341）に来る `LoopLabel` role 制約は**1個**（args=`pos PosId(18502), neg NegId(18523)`）。修正前後で不変。**漏れは「個数」ではなく「その1個が finalize で解決されない」問題**。
2. **空 subst チェーン**: `label_redo(1001)→redo(982)` subst=[]、`redo(982)→labeled(1341)` subst=[]。両方 空。role arg の中心 var が値の適用 param と結ばれず孤立。
3. **redo の def_tv に label_redo の Fun が materialize されない**（過去調査）。`func.tv` に Fun 下界が無いので、`make_app` の `'outer(具体 label) <: param` が role arg に届かず、別 var に行く。
4. **label_redo の body 内の配線は正しい**（過去のプローブ）。`label.redo()` の recv は param の def_tv と完全一致（recv.tv == 実 param == role arg）。問題は body 内ではなく「使う側で値の適用がその param に繋がらない」こと。
5. **frozen_scheme_of は lazy**（`solve/mod.rs:554-570`）。`frozen_schemes` に無ければ `compact_schemes` から freeze して `store_frozen_scheme` で永続登録（568）。**`frozen_scheme_of(def)` を呼ぶこと自体が副作用（scheme 早期生成）になりうる**ので注意。
6. **scheme 構築は OnDemandLambda 経路（path.rs:455-511）が担う**: `finalize_compact_results_for_defs(&{def})`（463）→ `freeze_compact_scheme_with_non_generic_and_extra_vars`（469）等。redo はこの経路に乗らないので scheme が作られない＝これが穴。

## 試して外れた案（**2回外している。再発厳禁**）
**(案A) 使う側 resolve 経路を OnDemandLambda に付け替え** = `principal_body_is_lambda_value` を Var エイリアス透過にして redo を OnDemandLambda 経路に乗せる → **悪化**。loop_control が `LoopLabel<α>`→`<α>,<β>`、labeled が 2→4 個に増えた。Var body を freeze しても **Fun-with-role-param スキームにならない**（body が lambda でないので role arg が値 param と結ばれた Fun を持てない）。

**(案A') 使う側 LetBound alias 経路で target の scheme を instantiate**（2026-06-04、claude が試行・revert 済み） = 525-535 で `alias_target_def(redo)→label_redo` を取り、`frozen_scheme_of(label_redo)` で scheme を得て `instantiate_frozen_scheme_with_subst` + `instantiate_role_constraints_for_owner_with_scheme` で role を subst 付き伝播 → **悪化**（labeled の LoopLabel が 1→2 個）。理由は **順序依存**: redo を使う時点で label_redo の compact がまだ無く `frozen_scheme_of(label_redo)=None` で本来の発火をせず、**`frozen_scheme_of` を呼んだ副作用（scheme 早期生成）だけ**が finalize を狂わせた。

**結論（設計者決定）**: 使う側 resolve 経路いじりは順序依存と副作用で必ず増悪する。**fix は定義側（scheme 構築）にしかない。**

## fix の当て先（設計者決定）
**redo のような「role 持ち lambda への単純エイリアス def（body が `Var(target)`）」を、scheme 構築の対象にする。** redo の scheme を
```
Fun(redo_param, …) with LoopLabel<redo_param>   かつ redo_param == role arg の中心 var
```
の形で作る。具体的には **target（label_redo, lambda）の scheme を redo 用 fresh param で instantiate して継承**する（target の lambda scheme は Fun-with-role を持つので、それを引き継げば role arg == 値 param が構造的に揃う）。こうすれば redo が `frozen_scheme_of(redo)` を持ち、使う側は普通の **Frozen 経路（path.rs:441-454）**に乗って、既存の subst 共有機構（`translate_frozen_subst_to_original_with_scheme`）で自動的に揃う。

- **順序依存の解消**: redo の scheme 構築時に target（label_redo）を先に `finalize_compact_results_for_defs` して compact/frozen scheme を確定させてから継承する。
- **絞り込み**: この継承は **target が role 持ち**のときだけ（`has_role_constraints(target)`）。role を持たない普通のエイリアス（`my a = b`）は従来の軽い `def_tv <: tv` を維持。設計者の「過剰適用で今は十分」は *role 持ちエイリアスに scheme コピーを許す* 意味であって、role 無しまで巻き込む許可ではない。

## 次の一手（推奨・潜る順）
1. **redo の binding lower を追う**: `lower/stmt/binding/decl.rs` の `lower_binding_with_type_scope`。body=`Var(label_redo)` を lower したとき `resolve_bound_def_expr(label_redo)`（owner=redo）が label_redo の Fun を redo の body.tv（→def_tv）に流すか。流していない＝事実3 の発生点。`YULANG_DEBUG_ROLE_REF=1` で `source=label_redo owner=redo` の subst を見る（空のはず）。
2. **redo の scheme が作られないことを確認**: `compact_scheme_of(redo)` / `frozen_scheme_of(redo)`（lazy 前）が None であること。なぜ finalize 対象外かを特定。
3. **scheme 継承を実装**: Var エイリアス body の role 持ち def に対し、target を finalize → target の scheme を redo の fresh param で instantiate → redo の compact/frozen scheme として `store_compact_scheme` / `store_compact_role_constraints`（role arg=redo param）。差し込み候補は OnDemandLambda 経路（path.rs:455-511）の条件拡張、または finalize 段（`role_finalize/finalize.rs`、`finalize_compact_results_for_defs` 周辺）。**使う側の resolve 分岐そのものは触らない**（Frozen 経路に自然に乗せるのが狙い）。
4. **last/next も同時に通す**: `prefix(last)=label_last` / `prefix(next)=label_next` も同型。`labeled_for_in_stmt` の `next 'outer` / nested の `redo 'inner` で検証。

ヘルパー `alias_target_def`（principal body の Coerce/PackForall を剥がして `Var(target)` を返す）は claude が一度書いたが revert 済み。定義側実装で再利用してよい。

## 絶対にやってはいけないこと
- **使う側 `resolve_bound_def_expr` の経路付け替えで直そうとするな。** 案A・案A' で2回外した。順序依存と `frozen_scheme_of` 副作用で必ず増悪する。
- **テスト期待値を改竄するな。** `labeled=unit` / `loop_control labeled=unit` / `nested=unit` は設計者確認済みの正しい値。型が変わって落ちたら、まず実装を疑う。混在ファイルのテスト部だけ `git checkout` で却下し実装は温存するのが正しい却下法。
- **cooccur に「守るべき変数集合 / rigid / non_generic 注入」を足すな。** 論文 §4.3.1（polar removal / indistinguishable unification / sandwich flattening）外の対症療法は過去に剥がした罠。
- **全エイリアスに scheme 継承を無差別適用するな。** role 持ち target のときだけ。`for_in`（Fold）の期待値や他の 460+ テストを回帰させない。

## working tree / デバッグツール
- 現在ツリーはクリーン（案A' は revert 済み）。物差しは 48 passed / 8 failed。
- `YULANG_DEBUG_ROLE_REF=1`: role 制約 instantiate ログ（`solve/selection/mod.rs:66-92`、`instantiate_role_constraints_for_owner source=.. owner=.. constraints=.. subst=..` と compact 版）。
- 物差しは必ず名指し＋`env RUSTC_WRAPPER=`。

## 参照すべき設計ドキュメント / メモ
- `notes/design/2026-06-02-role-system.md` — §簡約3（role 引数は不変＝中心変数は消えない）/ §決定1（簡約直後、通常引数の片側境界に具体型1つだけで解決）/ §決定3。
- `notes/design/2026-06-04-method-selection.md` — method 選択と role 関連型ループ。
- `~/.claude/projects/-home-momota1029-rust-yulang/memory/project-looplabel-role-discharge-bug.md` — 根因地図とプローブ履歴（同一バグ。本 handoff と合わせて読む）。
- `~/.claude/projects/-home-momota1029-rust-yulang/memory/level-polarity-protection.md` — 再帰ハンドラの極性消去（level 保護）。
- `~/.claude/projects/-home-momota1029-rust-yulang/memory/project-infer-residual-regression.md` — cooccur を論文準拠に保つ方針・Codex の悪癖。
- `lib/std/prelude.yu`（prefix エイリアス群） / `lib/std/flow.yu`（LoopLabel role, label struct, label_loop::for_in）。
