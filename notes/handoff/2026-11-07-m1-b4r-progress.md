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

## checkpoint 3: guarded 辞書の存在 iff 停止、および拒否経路の非存在

新規 `CommonRolePackedHalting`。wire に入力木を直接入れる有限 constructor `Description.data` も追加した。
これは有限 Ground pair/int 木の固定略記で、任意の意味的 decoder ではない。

閉じた主張:

- `descriptionAssignment_eval`: 任意有限 rule と任意 Ground 代入について、clock を有限 graph 記述へ置き換えた
  Description 代入の Common 解釈は既存の `clockAssignment` と等しい。
- `finite_step_description`: 任意 rule,source,target について、有限 machine step があれば、有限 Description 代入が存在し、
  実 head が source の Common goal に一致し、実 child は target の Common goal と同値になる。
- `machine_to_dictionary`: 任意 Code、任意有限 configuration とその `MachineHalts (registry Code) 0 configuration`、
  任意 role,first,last に対し、それらの Common 二成分 goal が configuration の goal と同値なら、
  packed visible に対する pair(role,first,last) の guarded 有限 Dictionary が存在する。
  最終 boundary で停止の前提を要求する定理ではなく、停止→辞書の構成方向の帰納補題である。
- `derives_to_old`: 任意 Code,goal と packed visible の guarded Derives、任意 role,first,last について、
  goal がその pairGoal と等しいなら、元の独立 Common Derives が成り立つ。
- `dictionary_iff_machine`: 任意 Code,configuration に対し、canonical packed finite description の
  guarded 有限辞書が存在 iff 同 configuration の有限 machine が停止する。追加前提なし。
- `dictionary_exact`: 任意有限 Code,Tree input に対し、実 packed registry の初期有限 goal description の
  guarded 有限 Dictionary が存在 iff `∃ output, CommonRoleComputation.Eval Code input output`。追加前提なし。
- `no_rejection`: 任意有限 Code,role,first,last,任意実 impl/index 経路について、packed visible で
  その pairGoal から再帰型拒否 `Rejects` に至ることはない。すべての where child の root が pair なのである。
  有限実行だけでなく、任意の Description 代入と任意の有限拒否経路を量化している。
- `actual_plan_exact`: 任意有限 Code,Tree input について、初期 goal の guarded 有限辞書で、
  その消去 plan 内の全実 impl が同じ packed visible に属するものが存在 iff 上記 Eval が停止する。
  full where 子を保持する既存 `RoleDictionaries.Plan` を返す。旧 unpacked Plan と等しいとは主張しない。

検証: `cd lean && lake build --wfail` exit 0（625 jobs）。

## checkpoint 4: 全域実 resolver の非存在（E2 主定理）

新規 `CommonRoleReachedRootObstruction`。入力は任意の意味的 Common 値ではなく、実 packed registry の全 fields、
定数 int の associated bodies、一引数の五つの有限 role signatures、一 node clock と有限 data の goal description を
具体的な有限 Tree に符号化したもの。実 finite binary-tape machine の停止 bit だけを要求する。

閉じた主張:

- `eval_queryCode`: 任意有限 Code,input について、固定有限 Code `queryCode` は
  node(descriptor Code,input) から正確な実 queryWire を有限に計算する。
- `queryCode_exact`: 任意 Code,input,output について、その評価が成り立つ iff output=queryWire(Code,input)。
- `signature_actual`: 任意 role<5 について、serialized signature の arity は実 roles の arity=1 と一致し、
  associated 宣言リストは [(0,none)] である。
- `no_total_reached_root_resolver`: 追加前提なしで、次の有限 tape machine は存在しない。
  任意有限 Code,input に対し、実 queryWire を初期入力として有限に停止し、その最終 current bit が true iff
  packed visible と初期 goal に対する guarded 有限 Dictionary が存在する、という machine である。
- `reached_root_registry_undecidable`: 追加前提なしで、以下の連言。
  (1) 任意有限 Code について実 checkEnvironment=true、実 WellFormed、任意 Common 代入に対する
  HeadDeterminesAssociated、実一引数 signature に対する AssocWellFormed。
  (2) 任意 Code,input,実 impl/index 経路について、初期 goal から構造的再帰型の拒否経路は存在しない。
  (3) 直前の全域 finite tape resolver は存在しない。

検証: `cd lean && lake build --wfail` exit 0（626 jobs）。
この時点で主定理は閉じた。最終記録・最小例・設計 note・独立レビュー・trust=0 Audit を続ける。

## checkpoint 5: 照合代入を任意 Common 型へ広げても反例は変わらない

新規 `CommonRolePackedSemanticReflection`。root 拒否と候補一意性を取り除き、代入像を任意の Common 型・行とした
より大きい独立 unary evidence を、実 packed head/where fields から定義した。

閉じた主張:

- `packed_head` / `packed_child` / `terminal_head`: 任意実 key,rule と任意 Common 代入に対し、
  実 packed fields の固定解釈は、元の Common head/child/terminal goal を pair にしたものと正確に一致する。
- `matches_compile`: 任意 key,rule,元 SemanticGoal,任意 Common 代入について、
  packed head の独立一致 iff 元の `HeadMatches`。
- `reflect`: 任意 Code,unary goal とその実 packed visible の独立 Derives、任意元 SemanticGoal について、
  unary goal が元 goal の pair 表現なら、元の独立 Common Derives が成り立つ。
- `of_old`: 任意 Code,元 SemanticGoal とその元の独立 Derives について、packed 実 fields の
  pair 表現の独立 Derives が成り立つ。
- `arbitrary_common_exact`: 任意有限 Code,input について、任意 Common 代入を許し、拒否も候補一意性も要求しない
  上記の大きい独立 Derives が存在 iff `∃ output, Eval Code input output`。追加前提なし。
- `guarded_iff_arbitrary_common`: 任意有限 Code,input について、guarded 有限 description 辞書の存在 iff
  上記の任意 Common 代入の独立 Derives。追加前提なし。

したがって、反例の成功判定が Description で表せない代入を捨てたために難しくなったのではない。
検証: `cd lean && lake build --wfail` exit 0（627 jobs）。

## checkpoint 6: 一 role・一 impl の目視用最小構成

新規 `CommonRoleReachedRootExamples`。head は `:box (:tick 'a)`、where は `R (:box 'a)`。
clock μ は `μ≈:tick μ`、初期 goal は `R (:box μ)`。box は tick と異なる tag の構造的 variant。
role、impl、型変数、正則 graph node がそれぞれ一つの最小構成である（全構文に対するサイズ最小性の定理ではない）。

閉じた主張（入力前提なし、最後の主張だけ任意 path を量化）:

- `declaration_sizes`: head/child の実構文サイズは 3/2。
- `declaration_accepted`: 実 CheckedRoles.checkImpl は true。
- `root_not_recursive`: 初期 goal の box root は構造的再帰型ではない。
- `root_matches`: 任意変数を μ に写す固定有限記述代入で、実 head は初期 goal に Common 同値で一致する。
- `child_returns_to_goal`: 同じ代入で、実 child の有限記述解釈は初期 goal に等しい。
- `unique_head`: singleton visible で head 候補は一意。
- `no_rejection`: 任意実 impl/index 経路について、singleton visible から初期 goal の再帰型拒否へ到達しない。

この例だけから全域算法不可能とは言わない。既訪問 cache が扱える同一 goal の循環であり、
算法不可能性の E2 は checkpoint 4 の任意有限 program の還元による。
検証: `cd lean && lake build --wfail` exit 0（628 jobs）。

## checkpoint 7: 独立レビューが求めた境界の明文化

二つの独立 read-only review は E2 に blocking defect を認めなかった。
一方から任意 Common 照合の一意性を公開する named lemma、もう一方から where signature の完全な閉鎖性を提案された。
それらを新規 module 内に追加した。

- `CommonRolePackedRegistry.constraints_declared`: 任意有限 Code、任意 packed visible 所属 impl、
  任意その実 where child に対し、child.role<5 かつ child.args.length=(roles child.role).arity=1。
  これで head/associated fields だけでなく全実 where の宣言済み arity も個別に確認した。
- `CommonRolePackedSemanticReflection.matches_to_actual`: 任意 Code、元 visible 所属実 impl、元 SemanticGoal、
  任意 Common 代入に対し、実 packed unary head の一致から元実二引数 head の一致を得る。
- `arbitrary_unique`: 任意 Code,実 impl,元 SemanticGoal について、元の実 head 候補が任意 Common 代入に対して
  一意なら、packed 実 unary head 候補も任意 Common 代入に対して一意。
- `unique_at_configuration`: 任意有限 Code,有限 configuration,packed visible 所属実 impl について、
  任意 Common 代入の head 一致 witness が一つでもあれば、その impl は同じ packed visible で、
  任意 Common 代入を許しても唯一の一致候補である。

検証: `cd lean && lake build --wfail` exit 0（628 jobs）。
Audit の登録を全56 theorem に拡張した。再検証と最終報告を続ける。
