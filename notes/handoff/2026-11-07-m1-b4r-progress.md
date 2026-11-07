# B4 redo 進捗（2026-11-07）

## checkpoint 1: 到達した root の拒否を独立判断にする

新規 `CommonRoleReachedRoot` は E2 の反例を表す有限 grammar の独立 semantics。
全 Common 言語の E1 を部分言語へ弱めたものではない。`Description` は有限 int/pair/variant 木、
有限 constructor context、および一 node の正則 graph μ = variant 7 μ を持つ。
root が循環成分にあることを `clockOnly` で定義する。pair の下の循環は root の循環ではない。
head 照合のために内部を見ることと、where の goal を解決することを区別する。
拒否 `Rejects` は実 impl と where index の経路を持つ別 judgment。辞書 constructor は root 非再帰を要求する。

閉じた主張（いずれも追加前提なし）:

- `clock_rejected`: μ は構造的再帰型である。
- `pair_not_recursive`: 任意 first,last : Description について、pair(first,last) の root は再帰的でない。
- `finite_not_recursive`: 任意 value : Ground について有限木 value の root は再帰的でない。
- `recursive_unrolling`: 任意 type : Description について、variant 7 type が再帰的 iff type が再帰的。
- `instantiate_eval`: 任意有限 Pattern と任意 Description 代入について、構文代入後の Common 解釈は
  各代入像を Common で解釈した代入による元 Pattern の解釈と等しい。
- `interpretTerm_encode`: 任意 Pattern と任意 Description 代入について、実 encoded Term の解釈は
  その Pattern の構文代入を some で返す。
- `Dictionary.derives`: 任意 visible,goal とその有限 Dictionary について、同じ visible,goal の Derives。
- `recursive_has_no_dictionary`: 任意 visible,goal について、root 再帰なら有限 Dictionary は存在しない。
- `Dictionary.all_visible`: 任意 visible,goal とその有限 Dictionary、任意消去 plan 中の impl について、
  その impl は同じ visible に属する。

検証: `cd lean && lake build --wfail` exit 0（623 jobs）。
既存 proof の変更なし。prover 登録 `.codex/config.toml` / role file と callable prover role は存在せず、
prover agent は実行していない。主担当が構成し、別 agent が反例の契約を read-only に検討した。

## checkpoint 2: 実宣言を一引数の pair へ包む

新規 `CommonRolePackedRegistry`。全 head/where 引数リスト args を一引数 `pair args` に包む。
二引数の反例 family では、通常の Common pair の固定解釈に一致する。

閉じた主張:

- `packGoal_injective` / `packImpl_injective`: 任意の二つの実 goal / impl について、pack 後が等しければ元も等しい。
- `packImpl_wellFormed`: 任意 impl について、元の実 WellFormed を満たすなら pack 後も満たす。
  head と child の両サイズに 1 を加え、全変数の出現回数を保存するためである。
- `declarations_wellFormed` / `declarations_accepted`: 任意有限 Code について、packed visible は実 WellFormed を満たし、
  実 `CheckedRoles.checkDatabase` が true を返す。追加前提なし。
- `environment_cores` / `environment_checked`: 任意 Code について、実関連型環境の cores は packed visible と等しく、
  既存 `CommonRoleRegularResolutionObstruction.checkEnvironment` が true を返す。
- `head_determines_associated`: 任意 Code について、packed 実環境の全 stored associated RHS は、
  任意二つの Common 代入で head が同値なら同値になる。Description 代入への限定なし。
- `associated_wellFormed`: 任意 Code について、packed 実環境は arity 1 の五つの role signature に対して
  実 `Roles.AssocWellFormed` を満たす。
- `packed_head` / `packed_child` / `terminal_head`: 任意 key,rule,Description 代入に対し、実 pack 後の head / where
  / terminal fields の独立解釈は、元の二引数を pair にした正確な goal になる。
- `matches_compile`: 任意 key,rule,role,first,last,Description 代入について、packed 実 head の独立照合 iff
  元の `HeadMatches` を各代入像の Common 解釈で満たす。
- `matches_to_actual`: 任意 Code、元 visible に属する任意実 impl、任意 role,first,last,Description 代入について、
  packed の照合から元実 fields に対する独立 Common 照合が得られる。
- `unique_of_actual`: 任意 Code,impl,role,first,last について、元 visible で Common 代入全体に対して候補一意なら、
  packed visible の Description 代入についても候補一意。

検証: `cd lean && lake build --wfail` exit 0（624 jobs）。
