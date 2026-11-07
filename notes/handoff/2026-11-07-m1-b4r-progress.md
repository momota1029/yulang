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

## 最終 gate と終了

E2: `CommonRoleReachedRootObstruction.reached_root_registry_undecidable`。
任意有限 Code に対する実 checker/WF/HDA/AssocWF を満たし、任意有限 Code,input,path で新 K2 拒否は起きず、
それでも全 query で有限停止し true iff 実 guarded 有限辞書の存在を返す finite tape machine は存在しない。

最終 `cd lean && lake build --wfail` exit 0、628 jobs。
最終 `cd lean && lake env lean --trust=0 Audit.lean` exit 0、allowlist 52454 declarations。
主定理の依存公理は propext / Quot.sound のみ。新規全56 theorem を Audit に登録した。
二つの独立レビューは E2 を支持し、最後の named arity/任意 Common 一意性の追加も再レビューを通った。

質問 note の Yulang 宣言例を `:{box :{tick 'a}}` の構文へ修正して、offline parser probe は
ok 1 / recovery 0。最初の省略表記は recovery だったので、source 到達可能性の証明として扱わない。

全 statement、build/Audit 末尾、正確な未証明項目を `2026-11-07-m1-b4r-results.md` に記録した。
README の未証明欄も追記済み。既存 Lean は許可された import/Audit の追記のみ。
RoleRank・fuel・無限辞書・公開入口の変更なし。commit / push なし。

# B4 redo 第2継続（head constructor 検査拒否の承認後）

旧 E2 の module・結果は保存する。開始時 HEAD は 2c75ac510143e14a4f32674c707ef0e1f9d02789。
承認済み spec K2 と completion contract を読み、初期 build は exit 0（628 jobs）。
prover の登録/config/呼出 role は引き続き無い。主担当が構成し、独立 read-only agent に反例を検討させる。

## B4r2 checkpoint 1: constructor 検査拒否を含む独立 semantics

新規 `CommonRoleInspectedSemantics`。int/pair/variant、単一 field 名0の record、有限 data tree、
一 node variant clock の有限 countergrammar。head/where の固定実 Term 解釈を置く。
`blocked` は非変数 pattern が循環 root の constructor を検査する場合と、pattern が必要とする子で検査する場合。
明示的に隠れた同名 field は検査対象から除く。変数による捕捉は検査しない。
`Ready` は root 非再帰かつ全 visible same-role head に禁止検査なし。
`HeadOutcome` は拒否を曖昧性より先にする作業上の選択を明示し、成功辞書も Ready を要求する。
priority は別の一問として記録する。この有限木反例には priority の選択は影響しない。

閉じた主張:

- `lift_eval`: 任意旧有限 data Pattern、任意 Common 代入について、新固定 grammar へ埋めた解釈は元と等しい。
- `decode_encode`: 任意新 Pattern について実 Term の decode(encode p)=some p。
- `interpret_encode`: 任意新 Pattern、任意 Common 代入について、実 Term 解釈はその Pattern の解釈を返す。
- `finite_root`: 任意 Description について、finite=true なら recursiveRoot=false。
- `finite_view`: 任意 Description について、finite=true なら実 view の全直接 child も finite=true、clock view はない。
- `finite_not_blocked_raw` / `finite_not_blocked`: 任意 Pattern,Description について、Description が有限木なら
  その head pattern の禁止再帰 constructor 検査は起きない。
- `variable_capture_allowed`: 任意変数名と任意 Description について変数で捕まえるだけなら blocked=false。
- `constructor_on_clock_rejected`: variant 7 の非変数 head を clock に当てると blocked=true。
- `finite_ready`: 任意有限 visible、任意 goal について、その引数が有限木なら Ready。
- `instantiate_eval`: 任意 Pattern と任意 Description 代入について、有限構文代入後の Common 解釈と
  代入像の Common 解釈で元 Pattern を解釈することは等しい。
- `interpretDescription_encode`: 任意 Pattern と任意 Description 代入について、実 Term の有限記述解釈は
  その Pattern の構文代入を some で返す。

検証: `cd lean && lake build --wfail` exit 0（629 jobs）。

## B4r2 checkpoint 2: 同名 field で実宣言サイズを padding する

新規 `CommonRoleFiniteShadowRegistry`。実 head は `{x:left,x:G^k int}`、実 where は `{x:right}`。
全変数は可視 left/right にしか現れず、padding は閉じた有限木。既存 checker を強化せず使う。

閉じた主張:

- `lift_size` / `lift_occurrences`: 任意旧有限 data Pattern、任意変数名について、固定新 grammar の実 encode は
  元 encode と同じ size / 変数出現回数を持つ。
- `compile_wellFormed` / `compile_accepted`: 任意 key,有限線形 rule について、その実 padded impl は
  WellFormed を満たし、実 CheckedRoles.checkImpl=true。前提は元 rule の全変数の線形性だけ。
- `declarations_wellFormed` / `declarations_accepted`: 任意有限 Code について、生成した有限 visible は
  実 WellFormed と実 checkDatabase=true を満たす。追加前提なし。
- `environment_cores` / `environment_checked`: 任意 Code について、実関連型環境の cores は visible と等しく、
  既存 CommonRoleRegularResolutionObstruction.checkEnvironment=true。新規 size gate はない。
- `head_determines_associated`: 任意 Code について、実 stored head/RHS を固定新 grammar で解釈した
  HeadDeterminesAssociated が、任意二つの Common 代入に対して成り立つ。RHS は定数 int。
- `visible_declared`: 任意 Code,visible 所属 impl について role<5 かつ head.length=1。
- `constraints_declared`: 任意 Code,visible 所属 impl,その where child について child.role<5、
  child.args.length=(roles child.role).arity=1。
- `associated_wellFormed`: 任意 Code について、実環境は既存 Roles.AssocWellFormed を満たす。
- `head_equivalent`: 任意 rule,任意 Common 代入について、実 head の解釈は required x (leftの解釈) と同値。
- `matches_compile`: 任意 key,rule,role,value Description,任意 Common 代入について、実 head の独立照合 iff
  source role が一致し、可視 left が value と Common 同値。
- `matches_terminal`: 任意 role,value Description,任意 Common 代入について、実 terminal head の独立照合 iff
  role=0 かつ代入0が value と Common 同値。
- `child_interpreted`: 任意 rule,任意 Description 代入について、実 child の独立解釈は
  right の構文代入を payload に持つ実 target role の required record goal。

検証: `cd lean && lake build --wfail` exit 0（630 jobs）。

## B4r2 checkpoint 3: 有限木の guarded 辞書 iff program の停止

新規 `CommonRoleFiniteShadowHalting`。旧有限線形 interpreter の実 rule.Step と MachineHalts に接続した。

閉じた主張:

- `matched_step`: 任意線形 rule、任意有限 configuration、任意 Common 代入について、source role が一致し
  left が source.value と要求同値なら、有限 target と実 rule.Step が存在し、right は target.value と同値。
- `unique_terminal`: 任意 Code,source,role,value Description について、role/source.role が一致し、value が
  source.value と Common 同値で role=0 なら、terminal impl が任意 Common 代入の head 照合で一意。
- `unique_compile`: 任意 Code,source,target,registry 所属 entry、その実 rule.Step、role,value Description に対し、
  role/source.role と value/source.value が一致すれば、その compiled impl は任意 Common 代入の head 照合で一意。
  no-overlap を外部前提として渡さず、実 compiler の既存独立 no_overlap から導く。
- `instantiate_lift_finite`: 任意旧有限 data Pattern と全代入像が finite=true の Description 代入について、
  埋め込み Pattern の構文代入も finite=true。
- `machine_to_dictionary`: 任意 Code,有限 source,その MachineHalts 証拠、任意 role,value Description に対し、
  value が有限木で role/source.role と value/source.value が一致すれば、amended semantics の有限辞書が存在。
  構成は全代入像を ground Description とし、全 child で有限性と Ready を証明する。
- `dictionary_to_machine`: 任意 Code,goal,独立 amended Dictionary、任意有限 source,role,value Description について、
  goal=dataGoal(role,value)、role=source.role、value が source.value と Common 同値なら MachineHalts。
  反映方向では value の有限性を追加前提にしていない。
- `dictionary_iff_machine`: 任意 Code,有限 configuration について、実 canonical finite goal の独立 guarded 辞書 iff
  その configuration の MachineHalts。追加前提なし。
- `start_finite`: 任意 Code,input について初期実有限 goal description は有限木。
- `dictionary_exact`: 任意有限 Code,input について、実 visible と初期有限 goal の独立 amended 辞書が存在 iff
  `∃ output, CommonRoleComputation.Eval Code input output`。追加前提なし。

検証: `cd lean && lake build --wfail` exit 0（631 jobs）。

## B4r2 checkpoint 4: 有限木だけでも全域成功判定は不可能（E2）

新規 `CommonRoleFiniteShadowObstruction`。実 registry の全 head/where/key/associated fields、一引数 signature、
初期有限木 goal を有限 Tree に wire 化し、既存の実 finite binary-tape machine と結ぶ。

閉じた主張:

- `eval_queryCode`: 任意有限 Code,input について固定有限 queryCode は node(descriptor Code,input) から
  実 queryWire(Code,input) を有限に計算する。
- `queryCode_exact`: 任意 Code,input,output について、その評価 iff output=queryWire(Code,input)。
- `signature_actual`: 任意 role<5 について serialized signature の arity は実 role の arity=1 と等しく、
  associated 宣言は [(0,none)]。
- `configuration_ready`: 任意 Code,任意有限 configuration について、canonical goal は有限木かつ Ready。
  したがって root 拒否も head の再帰 constructor 検査拒否も、どの有限 machine configuration にも作用しない。
- `no_total_finite_shadow_resolver`: 追加前提なしで、任意有限 Code,input の実 queryWire に対し必ず有限停止し、
  終了 bit が true iff その実 visible と初期 goal の独立 amended 有限 Dictionary が存在する、という
  finite transition-table binary-tape machine は存在しない。
- `finite_tree_registry_undecidable`: 追加前提なしで、(1) 任意 Code について実既存 checker=true、
  実 WellFormed、任意 Common 代入に対する HeadDeterminesAssociated、実 AssocWellFormed、
  (2) 任意 Code,input について初期 goal は有限木かつ Ready、
  (3) 上の全域 machine は存在しない、の連言。

検証: `cd lean && lake build --wfail` exit 0（632 jobs）。
主定理は閉じた。任意 Common 代入の上位 evidence、最小例、独立レビュー、Audit、最終 note を続ける。

## B4r2 checkpoint 5: 任意 Common 代入、実 plan、拒否の優先順位

新規 `CommonRoleFiniteShadowSemantic`。任意 Common 型・行を代入像とし、両拒否 gate と候補一意性を
取り除いた大きい独立 Derives を実 head/where fields から定義する。

閉じた主張:

- `CommonRoleInspectedSemantics.not_ready_no_dictionary`: 任意 visible,goal に対し Ready が成り立たなければ辞書は存在しない。
  root 拒否または禁止検査がある場合、成功を優先しないことを明示する。
- `Dictionary.all_visible`: 任意 visible,goal と独立 amended 辞書について、全消去 plan 内の任意 impl は同じ visible に属する。
- `CommonRoleFiniteShadowHalting.actual_plan_exact`: 任意有限 Code,input について、独立 amended 辞書で全実 plan 宣言が
  同じ visible に属するものが存在 iff `∃ output, Eval Code input output`。追加前提なし。
- `CommonRoleFiniteShadowSemantic.child_interpreted`: 任意有限 rule と任意 Common 代入について、実 where field の
  解釈は、target role と required x (rightの解釈) を正確に返す。
- `reflect`: 任意 Code,semantic goal,その大きい Derives、任意有限 source について、role が source と等しく
  goal.argument が required x source.value と Common 同値なら MachineHalts。
- `of_machine`: 任意 Code,有限 source とその MachineHalts について、実 visible の canonical semantic goal の
  大きい独立 Derives が成り立つ。
- `arbitrary_common_exact`: 任意有限 Code,input に対し、任意 Common 代入を許す大きい独立 Derives iff
  `∃ output, Eval Code input output`。追加前提なし。
- `guarded_iff_arbitrary_common`: 任意有限 Code,input に対し、有限 Description 代入の guarded 実辞書の存在 iff
  上の任意 Common 代入を許す大きい独立 Derives。Description の表現可能性を制約したための障害ではない。

検証: `cd lean && lake build --wfail` exit 0（633 jobs）。
独立レビューは初期4 module を E2 と判定し、trust=0 / 全体 build / Audit を通した。
新定理は Common record の既存 lemma を使うため Classical.choice にも依存する。許可された公理の範囲内。

## B4r2 checkpoint 6: 最小の有限例と cache を超える有限 growing chain

新規 `CommonRoleFiniteShadowExamples`。同名 field に隠れる ground int だけで size を稼ぐ。

閉じた主張:

- `loop_sizes`: 一 role・一 impl・型変数なしの `{x:int,x:int}` requires `{x:int}` の実サイズは5/3。
- `loop_accepted`: その実 impl は既存 checker を通る。
- `loop_ready`: singleton visible の初期有限木 goal は Ready。
- `loop_matches`: 任意 Common 代入に対し、その実 head は `{x:int}` に独立に一致する。
- `loop_child`: 任意 Description 代入に対し、実 where の解釈は同じ初期 goal を返す。
- `growing_sizes` / `growing_accepted`: 一変数の `{x:'a,x:int}` requires `{x::g 'a}` の実サイズは5/4、既存 checker は受理する。
- `normalized_examples_rejected`: 明示的 hidden field を除いてから既存 checker を呼ぶと、上の二例はともに拒否される。
  未承認修正案の probe であり、実 checker は変更していない。
- `payload_finite`: 任意 n に対し G^n int の有限記述は finite=true。
- `chain_ready`: 任意 n に対し `{x:G^n int}` は同じ singleton visible で Ready。
- `growing_step`: 任意 n に対し、全変数を G^n int に写す有限記述代入で実 head が chain(n) に一致し、
  実 where 解釈は正確に chain(n+1) を返す。
- `payload_eval`: 任意 n に対し、その有限 payload の Common 解釈は既存 growing(n) と等しい。
- `chain_equivalent_iff`: 任意 m,n に対し chain(m),chain(n) の引数が Common 同値 iff m=n。
- `no_natural_descent_measure`: 任意 n で chain(n+1) の値が chain(n) より小さくなる Goal→Nat 関数は存在しない。

検証: `cd lean && lake build --wfail` exit 0（634 jobs）。
上の最小ループや growing chain だけを算法不可能性と呼ばず、主 E2 は任意 program の停止問題還元に置く。

## B4r2 最終 gate と終了

E2: `CommonRoleFiniteShadowObstruction.finite_tree_registry_undecidable`。
任意有限 Code の実既存 checker/WF/HDA/AssocWF を満たし、初期 goal と全 canonical machine goal は有限木で Ready。
それでも任意有限 Code,input の実 query で必ず停止して true iff 実 guarded 有限辞書の存在を返す finite tape machine はない。

最終 `cd lean && lake build --wfail` exit 0、634 jobs。
最終 `cd lean && lake env lean --trust=0 Audit.lean` exit 0、allowlist 53240 declarations。
主 theorem の公理は propext / Classical.choice / Quot.sound、全65 theorem を Audit に登録。
二つの独立最終レビューも全6 module と同じ build/Audit を確認し、E2 と判定した。

全 statement、build/Audit 末尾、正確な残りを `2026-11-07-m1-b4r2-results.md` に記録した。
新設計 note に priority の作業上の選択と qualified の正確な未証明 lemma を置いた。
priority と宣言 checker 正規化の提案はそれぞれ questions に記録し、いずれも仕様へ黙って採用していない。
全3 Yulang block の offline parser probe は ok 3 / recovery 0。
既存 Lean は import6行/Audit65行の追記のみ。旧 E2 と旧結果、公開入口、既存 checker の変更なし。
commit / push なし。

# B4r3: duplicate-field 正規化承認後の継続（2026-11-07）

開始 HEAD f0f5ecd1d4d79757531f8035c68b0f90d34c6379。spec 6.3 の新しい大きさの数え方と K2 を読んだ。
初期全体 build は exit 0（669 jobs）。旧 E2 とその source は変更しない。

## B4r3 checkpoint 1: 正規化の意味保存と decidable checker

新規 `CommonRoleNormalizedDeclarations`。既存固定 countergrammar（int/pair/variant、field名0の record、変数）で、
N=Pattern.visible false を用いて payload 内も含め隠れた同名 field を除く。未知の tail は変数のまま残す。

閉じた主張:

- `tail_of_equivalent`: 任意 Common 型の同値から、label0を隠した双方向 RecordTailLe が成り立つ。
- `tail_trans`: 任意三 Common 型について、その双方向 tail 関係は推移的。
- `hidden_tail`: 任意 Common payload,rest について、rest と record0 payload rest は label0を隠した tail 関係で同値。
- `record_congr`: 任意 payload の Common 同値と任意 rest の双方向 masked-tail 関係から、全 record の Common 同値。
- `normalize_meaning`: 任意 Pattern、任意 Common 代入について Nfalseの解釈は元と Common 同値、
  Ntrueの解釈は元と label0を隠した tail 関係で同値。
- `normalizeTerm_encode`: 任意 Pattern について、実 Term の正規化は normalized Pattern の encode と等しい。
- `normalizeTerm_meaning`: 任意実Term、任意Common代入について、固定grammarでdecode可能なら、
  N前後の両実解釈が存在して Common 同値。
- `normalized_head_match_exact`: 同じ任意Term/代入/decode前提と任意Common goalについて、
  N後の実head解釈がgoalに要求同値 iff N前の実head解釈がgoalに要求同値。
- `checkImpl_sound`: 任意実implについて新decidable checker=trueなら、N(impl)の実 WellFormed。
- `checkEnvironment_sound`: 任意実有限関連型環境について新checker=trueなら、N(cores)はWellFormedかつ
  元の実stored head/RHS に対する HeadDeterminesAssociated。HDAは任意二Common代入を量化し、RHS=intの十分検査を使う。
- `another_size_erasure`: Common の union(int,int) は int と同値だが、その固定raw構文サイズは大きい。
  一般union注釈はsurfaceで禁止されるため、この lemma 単独を source-valid impl 反例とは扱わない。

検証: `cd lean && lake build --wfail` exit 0（670 jobs）。
これらはE2のcountergrammarの結果であり、全Common grammarのNを完成したとは主張しない。

## B4r3 checkpoint 2: 明示的duplicateを持たない有限 tail clock

新規 `CommonRoleFiniteTailClock`。一つの atom C={x:int} と、pair で独立に並べた有限個の C を clock にする。
head の各 slot は {x:int,..fresh}、child の各 slot は fresh。同じspineで同名fieldを二度書かない。
実 substitution fresh:=C 後だけ first-field-wins の重複が生じ、{x:int,..C}≈C となる。
これで prefix の異なるlabelやrecord順序の同値を追加せず、任意個のslotによって任意の構文サイズ差を稼げる。

閉じた主張:

- `fork_size` / `fork_occurrences`: 任意slot数 n,Pattern,変数名について、fork のsize=n*(size(pattern)+1)+1、occ=n*occ(pattern)。
- `lift_normal`: 任意旧data Patternの新grammar埋め込みはNで変わらない。
- `clock_normal`: 任意n,freshについてhead/child clock PatternはNで変わらない。
- `fork_instantiate`: 任意n,Pattern,Description代入でforkの構文代入は各slotを代入したforkDescriptionと等しい。
- `fork_equivalent`: 任意n,Pattern,Common代入,Descriptionについて、slotの解釈が同値ならfork全体も同値。
- `atom_absorbs`: Cは有限木であり、Common.record0 int CはCと同値。
- `head_clock_matches`: 任意n,fresh,Description代入でfreshをCへ写すならhead clockは固定有限clock(n)にCommon一致。
- `clock_finite`: 任意nについてclock(n)は有限木。
- `capacity_positive` / `member_below_capacity`: 任意有限rule列のcapacityは正、任意所属ruleのright raw sizeはcapacity未満。
- `compile_normal`: 任意n,key,ruleの実compiled implはNで変わらない。
- `compile_wellFormed` / `compiled_checked`: 任意n,key,線形ruleについてright.size<nなら、実WellFormedかつ新normalized checker=true。
- `assignment_fresh` / `assignment_finite`: 任意rule,有限Ground代入について、生成したDescription代入はfreshをCへ写し、全像が有限木。
- `assignment_data`: 任意rule,旧data Pattern,有限Ground代入について、Pattern.bound≤freshなら、
  上の代入によるPatternのCommon解釈は元Ground代入による構文代入の解釈とCommon同値。

検証: `cd lean && lake build --wfail` exit 0（671 jobs）。
独立調査は、型注釈にspreadを直接書けないsurface grammarとの境界を指摘した。
本反例は既存Roles.Term/WellFormed/AssocWellFormedが許すcore registryへの反例であり、source到達可能性は主張しない。
元の普遍量化にsource生成可能性の前提はない。その前提を追加する場合は別のamended statementとして扱う。

## B4r3 checkpoint 3: normalized checker を通る実registry

新規 `CommonRoleFiniteTailRegistry`。任意有限Codeの全ruleに同じ有限slot数capacityを使う。
閉じた主張:

- `declarations_wellFormed` / `declarations_accepted`: 任意Codeについて、実visibleはraw WellFormedと既存raw checkerを満たす。
- `environment_cores`: 任意Codeについて実関連型環境のcoresはvisibleに等しい。
- `environment_checked`: 任意Codeについて、Nでサイズ/出現回数を数える新checkerは実環境を受理する。
- `head_determines_associated`: 任意Codeについて、元実stored head/RHSに対するHDAが任意二Common代入について成り立つ。
- `normalized_wellFormed`: 任意CodeについてN(cores)は実WellFormed。checker soundnessから追加前提なしで導く。
- `visible_declared`: 任意Code,visible所属implについてrole<5、head.length=1。
- `constraints_declared`: 任意Code,visible所属impl,実where childについてchild.role<5、arity=1。
- `associated_wellFormed`: 任意Codeについて実関連型signature/scope/completenessが既存AssocWellFormedを満たす。
- `declarations_normal`: 任意Code,visible所属実implについてN(impl)=impl。
- `matches_compile`: 任意slot,key,rule,role,clock Description,data Description,任意Common代入について、
  実head一致 iff source role一致、head clockのCommon一致、left dataのCommon一致。
- `matches_terminal`: 任意role,clock/data Description,任意Common代入について、実terminal head一致 iff
  role=0、代入0とclockのCommon一致、代入1とdataのCommon一致。
- `child_interpreted`: 任意slot,rule,Description代入について、実where fieldは、freshの代入像をslot数だけ並べた
  clockとrightの構文代入をdataに持つ実target roleのpair goalを返す。

検証: `cd lean && lake build --wfail` exit 0（672 jobs）。
最初の試行にlocal名clockのlinter warningが出たためclockTypeへ直し、wfailで再検証した。

## B4r3 checkpoint 4: N-stableな有限tail clockの辞書 iff 停止

新規 `CommonRoleFiniteTailHalting`。既存independent Dictionaryの両K2 gate、全実where、任意Common候補一意性を使う。

閉じた主張:

- `unique_terminal`: 任意Code,有限source,role,clock/data Descriptionについて、role=source.role、data≈source.value、
  role=0なら、同じvisibleのterminalは任意Common代入のhead照合で一意。
- `unique_compile`: 任意Code,source,target,registry所属entryと実Step、role,clock/data Descriptionについて、
  role/source.roleとdata/source.valueが一致すれば、そのcompiled implは任意Common代入のhead照合で一意。
- `machine_to_dictionary`: 任意Code,sourceとMachineHalts証拠、任意role,有限data Descriptionについて、
  role/source.roleとdata/source.valueが一致すれば、固定有限clockとdataの独立amended辞書が存在する。
  全代入像・全子の有限性とReadyを証明し、freshを有限Cへ捕まえる。
- `dictionary_to_machine`: 任意Code,goal,その実Dictionary、任意有限source,role,clock/data Descriptionについて、
  goal=pairGoal(role,clock,data)、role=source.role、data≈source.valueならMachineHalts。
  clockの有限性・同値・成功を反映方向の追加前提にしていない。
- `dictionary_iff_machine`: 任意Code,有限configurationについて、固定有限clockのcanonical goalの辞書 iff MachineHalts。
- `start_finite`: 任意Code,inputについて初期descriptionは有限木。
- `dictionary_exact`: 任意有限Code,inputについて、実N-stable registryの独立amended有限辞書の存在 iff ∃output,Eval Code input output。
- `actual_plan_exact`: 任意Code,inputについて、全消去Plan内実implが同じvisibleに属する独立辞書が存在 iff 上記停止。

検証: `cd lean && lake build --wfail` exit 0（673 jobs）。
capacityの定義展開でproof elaboratorが既定heartbeatに達したため、このmodule内でcountをlocal irreducibleにした。
これは証明探索の展開制御であり、resolverのfuel・意味的深さ制限ではない。

## B4r3 checkpoint 5: normalized core registryの全域resolver非存在（E2）

新規 `CommonRoleFiniteTailObstruction`。実declaration fields、associated RHS、unary signature、有限clock description、
有限data goalをwireへ保存する。clock wireは有限descriptorから実queryCodeがコピーする。

閉じた主張:

- `eval_queryCode`: 任意有限Code,inputについて、固定有限queryCodeは実queryWireを有限計算する。
- `queryCode_exact`: 任意Code,input,outputについて、その評価 iff output=queryWire(Code,input)。
- `configuration_ready`: 任意Code,有限configurationについて、実canonical goalは有限木かつReady。
- `no_total_normalized_resolver`: 追加前提なしで、任意Code,inputの実有限queryで必ず停止し、終了bit=true iff
  実normalized-checked registryの独立amended有限Dictionaryが存在するfinite tape machineは存在しない。
- `normalized_registry_undecidable`: 追加前提なしで、(1) 任意Codeについて新checker=true、N(cores)の実WellFormed、
  任意Common代入の実HDA、実AssocWF、全visible実implのN固定性、(2) 任意Code,inputについて初期goalは有限木かつReady、
  (3) 上の全域machine非存在、を示す。

検証: `cd lean && lake build --wfail` exit 0（674 jobs）。
このE2はlisted core premisesに対するもの。source-generated閉spineに限定した別定理を反証したとは言わない。
独立reviewはこの量化境界でE2を支持し、build674/Audit55745の初期gateと主定理公理を確認した。

## B4r3 checkpoint 6: 任意Common代入と、既存VerifiedDeclarationの最小反例

新規 `CommonRoleFiniteTailSemantic` と `CommonRoleFiniteTailExamples`。

閉じた主張:

- `NormalizedDeclarations.union_padding_scope`: 任意Common代入について、既存の別union grammarでunion(unit,unit)を
  表す有限Termは同じunitに解釈され、raw sizeが増え、record用Nでは変わらない一方、今回のcheckPatternsには拒否される。
  実decoderを越えた別grammarの意味を混ぜた反例にしないよう、scopeを明示した。
- `interpretGoal_commutes`: 任意実where goalとDescription代入について、有限記述解釈後のCommon意味と、
  代入像をCommonへ写して実fieldを直接解釈することは等しい。
- `forget`: 任意visible,goal,独立amended辞書について、両gate/一意性を除いた既存上位semantic Derivesが成り立つ。
- `child_interpreted`: 任意slot,rule,任意Common代入について、実child fieldはclockChildとrightをpairにした意味を返す。
- `reflect`: 任意Code,semantic goalと上位Derives、任意有限source,任意Common clockTypeについて、
  role一致かつgoal.argument≈pair(clockType,source.value)ならMachineHalts。
- `arbitrary_common_exact`: 任意Code,inputについて、任意Common代入の上位Derives iff ∃output,Eval Code input output。
- `guarded_iff_arbitrary_common`: 任意Code,inputについて、有限Description代入のguarded辞書存在 iff 上位Derives。
- `old_verified_api_accepts`: 最小DeclarationのtoImplは実反例implと等しく、既存verify.isSome=true。
- `normalized_checked` / `declaration_fixed` / `declaration_sizes`: 最小実implは新checkerを通り、N固定、N前後head size3、child size1。
- `goal_ready` / `head_matches` / `child_returns`: 最小有限goalはReady、有限C捕捉で実head一致し、実childは同じgoalへ戻る。
- `normalization_does_not_commute_with_capture`: このheadをNしてからCを捕捉する構文と、捕捉してからNした構文は等しくない。
- `post_capture_sizes`: 捕捉後raw head size5、N後size3、childの捕捉後size3。
- `finite_children_differ`: 有限CとemptyRecordはCommon同値でない。
- `requirements_not_determined`: 最小implは、headのCommon意味からwhere引数のCommon意味が決まる条件を満たさない。
  σtail=Cとτtail=emptyでheadは同値、childは非同値になる。

検証: `cd lean && lake build --wfail` exit 0（676 jobs）。
これで全72新規theoremをAuditに登録した。source到達可能性は主張しないが、既存のnamed VerifiedDeclaration APIまで
明示的に受理するため、listed core前提の外に暗黙のclosed-spine条件があるとは扱わない。

## B4r3 最終 gate と終了

E2: `CommonRoleFiniteTailObstruction.normalized_registry_undecidable`。
任意有限Codeの実core registryは新normalized checker/WF/HDA/AssocWF、全declのN固定性を満たす。
全canonical goalは有限木でReady。それでも全実finite queryで必ず停止してtrue iff実有限Dictionaryを返すmachineはない。

最終 `cd lean && lake build --wfail` exit0、676 jobs。
最終 `cd lean && lake env lean --trust=0 Audit.lean` exit0、allowlist55785 declarations。
主定理の公理はpropext/Classical.choice/Quot.sound。全72新規theoremを登録した。
二つの独立最終reviewも同じbuild/Auditとfocused trust0 warning-as-errorを通し、E2と判定した。
source ..tail不可、closed-spine/source bridge未証明という境界も独立reviewした。

全statement、build/Audit末尾、残りを新 `2026-11-07-m1-b4r3-results.md` に記録した。
設計noteにNと代入の非可換性、別union encodingの範囲、qualifiedの正確な未証明lemmaを記録。
source量化/closed-spine bridgeまたはtail意味の変更は一問へ置き、仕様へ採用していない。
実source比較例のparser probeはok1/recovery0。core反例を直接書けるsource例にしていない。
既存Leanはimport7行/Audit72行の追記のみ。既存proof、旧E2、spec、公開入口の変更なし。commit/pushなし。
