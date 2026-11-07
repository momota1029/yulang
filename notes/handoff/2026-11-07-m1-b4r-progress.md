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

# B4r4: canonical residual 捕捉の承認後（2026-11-07）

開始HEAD ab93202a61ad091aae567127dd97a14a507dedf4。spec6.3の新しいtail引き算規則を読んだ。
旧tail-clock E2は任意Common代入という旧解釈に対する定理であり、承認後のsemanticsには適用しない。
record tailはcanonical residual以外へ捕まえず、未解決goalを解決しない。

## B4r4 checkpoint 1: 任意labelのcanonical row subtraction

新規 `CommonRoleCanonicalRows`。payload型を任意に保ち、first-field-wins正規化とcanonical residualを実関数で定義。
閉じた主張（Payload型は任意）:

- `mem_residual` / `mem_selected`: 任意label列,row,entryについて、残る/選ばれる iff 元row所属かつlabelが未選択/選択。
- `residual_excludes`: 任意所属entryのlabelは取り除いたlabel列にない。
- `residual_commute` / `residual_idempotent`: 任意二label列とrowで引き算が可換、同じ引き算は冪等。
- `residual_map`: 任意payload写像について、引き算はpayloadの写像と可換。自由Common代入の成功性を前提にしない。
- `lookup_residual`: 任意row,labelについて、引き算後lookupは取り除いたlabelならnone、それ以外は元lookup。
- `lookup_normalize`: 任意row,labelについてfirst-field-wins正規化はlookupを保存。
- `normalize_unique`: 任意rowについて正規化後のtag/field名はNodup。
- `normalize_of_unique` / `normalize_idempotent`: もとがNodupなら正規化は恒等、一般rowで正規化は冪等。
- `capture_unique`: 任意label列,row,二tailについて、両方canonical captureなら等しい。
- `capture_no_hidden`: 任意canonical capture所属entryのlabelは引いたlabelにない。
- `capture_normalize`: 任意label列,rowについて事前row正規化でcaptureは変わらない。
- `former_clock_removed`: 任意payloadについてcapture [0] [(0,payload)]=[]。旧Cへの再捕捉は認めない。
- `mass_partition`: 任意payload重み,row,label列について、selected質量+residual質量=元質量。
- `residual_mass_le`: 任意payload重みと引き算で質量は増えない。
- `selected_positive` / `residual_mass_lt`: 元rowに引かれるentryがあればselected質量は正、residual質量は真に小さい。

検証: `cd lean && lake build --wfail` exit0（677 jobs）。これはglobal E1の完了ではない。

## B4r4 checkpoint 2: 実variant tag mergeが残すpayload union

新規 `CommonRoleMergedPayload`。surfaceに一般unionを書くのではなく、同じtagと同じdata Patternを繰り返し、
実 `Variants.Merged.normalize joinTerm` を呼ぶ。tagは一意になるがpayloadは右結合unionのまま。

閉じた主張:

- `merged_entries`: 任意コピー数とdata Patternについて実normalize後entriesは一要素(0,padded payload)に正確に等しい。
- `merged_tag_unique`: 同じ任意入力について実merged rowのtag列はNodup。
- `interpret_data` / `interpret_padded` / `interpret_head`: 任意data Pattern,コピー数,任意Common代入に対し、
  固定codecの実解釈は元data、反復payload union、single-tag variantの意味を正確に返す。
- `padded_equivalent` / `head_meaning`: 任意Common型,任意コピー数について反復unionは元と同値、single-tag headも同値。
- `unlift_lift` / `decode_data` / `contract_data` / `contract_padded` / `decode_head`: 任意data Patternとコピー数について、
  実encodeのdata decodingと同一branchだけのcanonical contractionは元Patternを返す。
- `data_size` / `data_occurrences`: 任意data Pattern,変数名について実codecは既存data grammarとsize/出現回数が等しい。
- `padded_size` / `padded_occurrences`: 任意Term,コピー数n,変数名についてraw size=(n+1)*元size+n、occ=(n+1)*元occ。

検証: `cd lean && lake build --wfail` exit0（678 jobs）。
独立調査はspec10の実mergeにpayload冪等則の前提がなく、sourceの重複tag例もparserが読むことを確認した。
row区切りをproducer unionと取り違えず、実mergeが作ったpayload内部のunionだけを扱う。

## B4r4 checkpoint 3: 実merged-row declarationとnormalized checker

新規 `CommonRoleMergedRegistry`。任意有限Codeを既存linear machine registryから実Roles.Implへcompileする。
閉じた主張:

- `normalize_head` / `compile_normal`: 任意コピー数,Pattern / 任意key,Ruleについてrecord用Nはhead/implを変えない。
- `compile_wellFormed` / `compile_checked`: 任意key,RuleについてLinear Ruleなら実whereのsize/occ条件と実checker成功。
- `declarations_wellFormed` / `declarations_normal`: 任意Codeの全実visible implはWellFormedかつN固定。
- `checkImpl_sound`: 任意implについて新decoderと既存checkImplの合成がtrueならN implはWellFormed。
- `environment_cores`: 任意Codeについて実AssocEnvのcoresはvisible Codeと等しい。
- `checkEnvironment_sound`: 任意AssocEnvについて実checker=trueなら全N coresのWellFormedと任意Common代入のHDA。
- `environment_checked`: 任意Codeの実AssocEnvはchecker=true。
- `visible_declared` / `constraints_declared`: 任意Code,visible実impl,実whereについてrole<5、実arity=1。
- `associated_wellFormed`: 任意Codeについて既存Roles.AssocWellFormed。associated RHSは常にint。

検証: `cd lean && lake build --wfail` exit0（679 jobs）。
旧limited checkPatternsにunion構文を紛れ込ませていない。新decoderは実mergeが作る同一payload反復を明示的に扱う。

## B4r4 checkpoint 4: canonical payload captureと独立finite dictionary

新規 `CommonRoleCanonicalMergedEvidence`。
閉じた主張:

- `goal_finite` / `goal_ready`: 任意有限Ground goal,任意visibleについてdescriptionはfiniteかつ両K2 gateを通る。
- `capture_reconstructs`: 任意Pattern,Ground,有限代入でinstantiate=goalならcanonical captureも同じgoalを再構成。
- `capture_agrees` / `captures_unique_on_used`: 同じ任意premiseにおいてheadに現れる任意変数の捕捉はcanonical値と等しく一意。
- `head_matches_exact`: 任意実impl,有限goalについて実Bool headMatches=true iff 独立structural Matchesの有限代入が存在。
- `requirements_determined`: 任意Linear Rule,Ground,二有限代入でhead instantiateが共にgoalならright instantiateも等しい。
- `matches_compile` / `matches_terminal`: 任意実compiled/terminal impl,goal,代入について独立Matchesは元rigid data一致とrole一致に正確に等しい。
- `child_interpreted`: 任意Rule,有限代入について実where fieldの解釈はright instantiateを正確に返す。
- `Dictionary.all_visible`: 任意visible,goal,独立finite Dictionaryについて実Plan中の全implはvisible所属。

検証: `cd lean && lake build --wfail` exit0（680 jobs）。record tailは存在せず、任意Common同値代入を選ぶ定義ではない。

## B4r4 checkpoint 5: 実normalized rowからのbridgeとHalts iff

新規 `CommonRoleMergedHalting`。Registryへ実row/head bridgeを追加した。
閉じた主張:

- `merged_head`: 任意コピー数,Patternについて実Variants.Merged.normalize後のRowから実headTermが得られる。
- `all_heads_from_merge`: 任意Code,visible実implについて、そのheadが実normalized rowから得られるコピー数,Patternが存在。
- `unique_terminal` / `unique_compile`: 任意Code,有限sourceについて終了role=0 / 実registry所属entryによるsource→target stepなら実候補は一意。
- `machine_to_dictionary` / `dictionary_to_machine`: 任意Code,有限configuration / goalについてMachineHaltsから実全where Dictionary存在、逆も成り立つ。
- `dictionary_iff_machine`: 任意Code,有限configurationについて実Dictionary存在 iff MachineHalts。
- `dictionary_exact` / `actual_plan_exact`: 任意Code,inputについて実Dictionary存在（全実Plan宣言がvisibleという性質を含めても）iff ∃output,Eval Code input output。

検証: `cd lean && lake build --wfail` exit0（681 jobs）。有限Dictionaryだけを使い、coinductive evidenceやfuelは導入しない。

## B4r4 checkpoint 6: 全有限resolver非存在

新規 `CommonRoleMergedObstruction`。
閉じた主張:

- `start_description`: 任意Code,inputについて有限wire用記述の解釈は実startGoalに等しい。
- `eval_queryCode` / `queryCode_exact`: 任意Code,input,outputについて固定有限programの評価は実queryWireを返し、その出力だけ。
- `no_total_canonical_merged_resolver`: 追加前提なしで、全Code,inputの実有限queryで停止し終了bit=true iff実canonical有限Dictionary存在を返す有限tape machineは存在しない。
- `canonical_merged_registry_undecidable`: 追加前提なしで、任意Codeの実registryは新checker、NWF、raw WF、任意Common代入のHDA、AssocWF、全implのN固定性と実normalized variant row由来を満たし、任意Ground goalはfiniteかつ両K2 gateを通る。それでも上の全域machineは存在しない。

検証: `cd lean && lake build --wfail` exit0（682 jobs）。成功bitだけで既存Halts非決定性に還元した。
これは現在の任意core registry量化へのE2であり、source全elaborationの正確性を新たに証明したとは言わない。

## B4r4 checkpoint 7: 任意Common代入との独立比較

新規 `CommonRoleMergedSemantic` 初版。
閉じた主張:

- `generated_match_exact`: 任意コピー数,Pattern,Groundについて、構造的有限捕捉存在 iff 実head解釈をgoalのsingle-tag variantとCommon同値にする任意Common代入と型が存在。
- `requirements_determined_common`: 任意Linear Rule,Ground,二Common代入について、両left解釈がGroundと同値ならright解釈も同値。
- `child_interpreted`: 任意Rule,任意Common代入について実where field解釈はvariant tick(right.eval)を返す。
- `reflect`: 任意Code,上位Derives,有限sourceについてrole一致とvariant payloadの要求同値からMachineHalts。
- `of_machine`: 任意Code,有限sourceについてMachineHaltsから上位Derives。
- `arbitrary_common_exact` / `canonical_iff_arbitrary_common`: 任意Code,inputについて上位任意Common evidence iff Halts、またcanonical有限Dictionary存在 iff同上位evidence。

検証: `cd lean && lake build --wfail` exit0（683 jobs）。上位比較はcanonical record tailを任意代入へ戻す定義ではない。

## B4r4 checkpoint 8: 小例と提案の局所検査

新規 `CommonRoleMergedExamples`。
閉じた主張:

- `minimal_checked` / `growing_checked`: 固定self-loop / growing implは新checker=true。
- `minimal_sizes`: 固定self-loopの実head size4、実child size2。
- `growing_sizes_occurrences`: 固定growingの実head/child size4/3、変数0の出現2/1。
- `minimal_normal` / `minimal_from_merge`: 固定self-loopはN固定、実duplicate-tag mergeから実headが得られる。
- `minimal_matches`: 固定finite selfGoalに実headMatches=true。
- `minimal_child`: 任意有限代入について固定実childはselfGoalへ戻る。
- `no_finite_self_dictionary`: 任意finite Goalについてsingleton selfImpl環境の有限Dictionaryは存在しない。
- `no_self_descent_measure`: measure selfGoal < measure selfGoalとなるGoal→Natは存在しない。
- `proposed_rejects_minimal` / `proposed_rejects_growing`: 固定各小例のheadを提案縮約してから実checkerへ渡すとfalse。

検証: `cd lean && lake build --wfail` exit0（684 jobs）。小例だけを全域アルゴリズム非存在の代用にしない。

## B4r4 checkpoint 9: 全Commonでのrequirements決定性と候補一致

Semanticを追加強化した。
閉じた主張:

- `pattern_determines_used`: 任意rigid Pattern,二Common代入,変数について、両pattern解釈同値かつ当該変数出現なら変数像も同値。
- `requirements_determined_all_common`: 任意Linear Rule,二Common代入について、両left解釈同値ならright解釈も同値。有限target前提なし。
- `generated_candidate_exact`: 任意role,key,コピー数,Pattern,実child列,有限goalについて、canonical Matches代入存在 iff実格納headの任意Common Matches代入存在。
- `visible_candidate_exact`: 任意Code,visible実impl,有限goalについて同candidate iff。
- `unique_common`: 任意Code,実impl,有限goalについてcanonical Uniqueなら全任意Common一致候補も同じimpl。
- `head_determines_requirements`: 任意Codeの全実visible implについて、任意二Common代入の全実head同値から全実whereのrole一致と引数同値。定義されることも含む。

検証: `cd lean && lake build --wfail` exit0（684 jobs）。追加のHeadDeterminesRequirementsだけでも今回のfamilyは除外できない。
全98新規theoremをAuditへ登録した。独立reviewもglobal量化を確認し、trust0 Audit exit0/56333 declarations。

## B4r4 最終gateと終了

E2: `CommonRoleMergedObstruction.canonical_merged_registry_undecidable`。
canonical residualを守るtail-free実registryで、実variant merge後の同一payload unionがPaterson sizeを膨らませる。
任意CodeについてN固定/WF/実checker/HDA/AssocWF、全finite goalでReady、実全where辞書存在iff停止、全域有限machine非存在を証明。
任意Common代入での強いHeadDeterminesRequirementsも全registryについて証明したため、その追加だけでは除外できない。

最終 `cd lean && lake build --wfail` exit0（684 jobs）。
最終 `cd lean && lake env lean --trust=0 Audit.lean` exit0、allowlist56333 declarations。
全98新規theoremを登録。主定理とglobal HDRはpropext/Quot.soundのみ。
独立fresh reviewもfocused trust0/warning-as-error、full build/Audit、最終4文書のscopeを確認し阻害事項なし。
parserの重複variant tag例はok1/recovery0。実merge→実head bridgeは証明済み、full source elaboratorは未証明。

結果は新 `2026-11-07-m1-b4r4-results.md`。全定理名/全日本語量化/前提、build/Audit末尾、正確な残りを記載。
新設計noteにcanonical record subtraction、Common候補iff、K2/priorityの範囲、qualifiedの正確な未証明lemmaを記載。
新question一問へpayload冪等縮約後のsize/occ checker案を置いた。未承認のまま、specへ採用していない。
旧tail E2は旧意味の定理として保存し、現在の意味の証拠にしていない。

既存Leanの差分は許可されたYulang.lean import8行/Audit追記/README節追記だけ。
開始HEADからのappend-onlyと既存proof無変更を機械検査した。公開入口/spec/旧結果の変更、commit/push/networkなし。
全E1、全Common N/regular matcher、一般finite-tree/nominal agreement、qualified実生成と全family、source/B6統合は残る。
これらを前提へ移して同名E1を閉じていない。元全称core-registry契約へのE2として終了する。

# B4r5 開始（2026-11-07）

開始HEAD 0579a6caccb212ecc8934e6e20d3e1c930e6db10。
承認済みのvariant payload合流後size/occurrenceと、existential substitution addendumを読んだ。
旧B4r4 E2は旧size ruleへの定理として保存し、現規則のE2として使わない。
独立grammar auditはaliasesの事前展開、rigid pair/arrow/variantのCommon injectivity、
nominal opaque/invariant、effect rowのextensional表現、associated projection禁止、
record first-wins/orderとvariant tag合流を点検した。
optional-anyのsemantic vacuityは既存定理にあるが、optional表示をsource head構文と勝手に読み替えない。

新しい局所候補は、直接role引数で'a=intを捕捉した後に、以前は異なった二variant payloadが一致する場合。
これは恣意的なexistential substitutionでないが、宣言時checkと遅延merge後checkの接続がspecで未指定。
E2とは扱わず、質問を一つ `2026-11-07-b4r5-capture-before-size.md` に置いた。
その間、symbolic check / instance再check / capture-safe declaration checkの各場合を分けて形式化する。
prover role設定とcallable schemaは今回も不在。primaryが構成し、別agentへ独立auditを依頼した。

## B4r5 checkpoint 1: 直接捕捉後の新しい合流を局所形式化

新規 `CommonRoleCaptureNormalization`。E1/E2の終了ではない。
閉じた主張:

- `subst_encode` / `subst_eval`: 任意Form,任意Form代入（後者は任意Common解釈も）で実Term substitutionとencode、および意味解釈が可換。
- `join_congr`: 任意四Common型でa≈bかつc≈dならunion(a,c)≈union(b,d)。
- `normalize_meaning`: 任意Form,任意Common解釈について局所idempotence stageの前後は要求同値。
- `capture_zero_actual`: 固定実impl/goalについて既存Roles.matchingSubstの変数0像は固定capture0=intのencodeと等しい。存在代入の選択ではない。
- `symbolic_checked` / `symbolic_sizes` / `symbolic_occurrences`: 固定symbolic implは実checker=true、実head/child size9/5、変数0occ3/3。
- `captured_head` / `captured_child` / `captured_sizes`: 固定実capture後Nのhead/childは共に実goal.args、sizeは共に5。
- `normalization_capture_noncommute`: 固定headについてN後captureのencode列とcapture後Nのencode列は異なる。
- `symbolic_check_does_not_imply_captured_descent`: 固定symbolic implの実checker=trueかつcapture後の真下降は成立しない。
- `late_check_rejects`: 固定capture後実implは実checker=false。
- `capture_safe_rejects`: 提案条件CaptureSafe（任意Form割当てでN後child size<head size）は固定宣言では偽。現checkerだとは扱わず、decidabilityも主張しない。
- `actual_merge_entries` / `actual_merge_unique`: 固定二payload rowの実Variants.Merged.normalize結果は指定singleton joinと等しく、tag列Nodup。

検証: `cd lean && lake build --wfail` exit0（685 jobs）。局所counterlemmaを現承認規則へのE2と呼ばない。

## B4r5 checkpoint 2: pair成分合流による別分解

同moduleへ追加。
閉じた主張:

- `coalesced_meaning`: 任意Common解釈について、固定元head payloadのunion of pairsとpair of unionsのsingle-tag variantは要求同値。
- `coalesced_checked` / `coalesced_size`: 固定coalesced実implも実checker=true、実head size9。
- `coalesced_captured`: 固定coalesced headも直接capture後Nで実goal.argsに等しい。
- `coalesced_late_check_rejects`: 固定coalesced headと実childをcapture後にcheckするとfalse。

検証: `cd lean && lake build --wfail` exit0（685 jobs）。
独立reviewもtrust0/warning-as-error exit0。source質問例の実parser probeはok1/recovery0、role/where引数順を確認。
全22新規theoremをAuditへ登録した。任意Common代入のlemmaはcongruence/意味保存であり、実captureを任意解にしていない。

## B4r5 現在のgateと設計判断境界

`cd lean && lake build --wfail` exit0（685 jobs）。
`cd lean && lake env lean --trust=0 Audit.lean` exit0、allowlist56505 declarations。
全22新規theorem登録、追加公理/sorry/native_decideなし。
独立reviewはfocused trust0/warning-as-errorと全22日本語量化、question/design/results/READMEのscopeを確認。
optional表示についてのsource意味を断定しないよう、一箇所の表現を修正した。
開始HEADに対して既存Leanの許可外変更なし、Yulang.lean/Audit/READMEはappend-onlyを機械確認。

新results `2026-11-07-m1-b4r5-results.md` はE1/E2未到達と明記。
N全grammar完全性、全regular resolver/exact dictionary、finite-tree/nominal agreement、qualified実生成と全familyは残る。
一問 `2026-11-07-b4r5-capture-before-size.md` のtiming決定なしに、capture-safe宣言条件や新use-site拒否を採用しない。
実captureは既存extractorにより決定しているが、宣言checkがcapture後mergeをどう保証するかが未指定であり、
この点を勝手に決めたE2や追加hypothesis付き同名E1は出していない。

# B4r6 開始（2026-11-07）

開始HEAD d39ff4c8abd1db80af0e7e5de3095f56211140e8。第五回の作業treeの追記を保存したまま開始。
ユーザーがcapture後mergeにも安全な宣言条件（利用時の新規拒否なし）を承認したspec6.3を読んだ。
前回の局所9/5→5/5例は宣言時拒否として扱い、現規則へのE2としない。
有限十分checkerとしてheadの安定rigid位置のlower envelopeとchildのupper envelopeを比較する分解を進める。
merge下のhead variableはlower係数に使わず、canonical record residualのlabel不在はmatcherから得る。
prover roleは今回も不在。primaryが構成し、別agentの独立design auditを得た。

独立auditは新しい強い条件を通るrobust E2を見つけていない。
残る実matching policyとして、terminal implの非同一payload内にだけ現れる変数の決め方がspec未指定。
一問に記録し、勝手な存在Common代入を置いたE2は出さない。checkerの局所soundness構成は並行して継続する。

## B4r6 checkpoint 1: substitution-stable lower/upper envelope checker

新規 `CommonRoleStablePaterson`。現在の形式化範囲はrecursive idempotence stageの有限Form grammarであり、full Common/source checkerの完成ではない。
閉じた主張:

- `normalize_idempotent`: 任意FormでN(Nf)=Nf。
- `normalize_subst` / `normalize_before_subst`: 任意Form,任意Form代入について、代入像の事前N、およびtemplateの事前Nは、最後のN結果を変えない。
- `normalize_size_le` / `normalize_occurrences_le`: 任意Form（後者は任意name）で、N後の実size/occは元以下。
- `lower_size` / `lower_occurrences`: 任意Form,任意代入（後者は任意name）で安定rigid lower boundへN済代入像を入れたsize/occは実capture後N以下。
- `upper_size` / `upper_occurrences`: 同任意入力で実capture後Nのsize/occはraw upper templateへN済代入像を入れた値以下。
- `term_subst_occurrences` / `args_subst_occurrences`: 任意実Term/引数列,実代入,変数bound,nameで、元boundが指定bound以下なら代入後occは全元変数occ×代入像occの有限sumBelowに等しい。
- `occurrence_mono`: 任意実head/child引数列で全変数occ(child)≤occ(head)なら、任意実代入とnameで代入後もocc(child)≤occ(head)。
- `head_size_bound` / `child_size_bound` / `head_occurrences_bound` / `child_occurrences_bound`: 任意Form列,任意代入（occは任意name）に対してN済lower/upper list boundsが実capture後Nを挟む。
- `check_comparison_exact`: 任意有限Declarationで実Boolcheck=true iff有限comparison Roles.Impl.WellFormed。
- `check_sound`: 任意Declaration,check=true,任意実requirements所属child,任意Form代入で、実N後child size<head sizeかつ任意nameの実N後child occ≤head occ。late拒否や成功前提なし。
- `subst_identity` / `instantiated_identity`: 任意Form/列についてidentity代入は構文を保ち、N後引数列はchildBoundに等しい。
- `accepted_wellFormed`: 任意Declarationでcheck=trueなら実toImpl.WellFormed。
- `unary_accepted` / `rebuilding_accepted` / `repeated_accepted` / `constant_accepted`: 固定通常unary下降、pair再構築、同一payload重複、merged headから定数childの各実check=true。
- `previous_rejected`: 固定第五回例の実check=false。
- `terminal_accepted`: 任意role,key,任意Form headについてwhereなし宣言の実check=true。terminalを形制限で除外していない。

検証: `cd lean && lake build --wfail` exit0（686 jobs）。追加strengtheningは次checkpointの687 jobsにも含まれる。
独立reviewは全Form代入のsandwich証明とactual toImpl WFを確認、focused trust0/warning-as-error exit0。

## B4r6 checkpoint 2: terminal merged headの未決capture boundary

新規 `CommonRoleMergedCaptureBoundary`。運用上のcaptureやfull E2を定義していない。
閉じた主張:

- `stable_checked` / `wellFormed`: 固定二terminal declarationは実stable checker=true、実visible impl列はWF。
- `environment_cores`: 固定実AssocEnvのcoresは同visible列。
- `associated_determined`: 固定実AssocEnvは任意二Common代入の実HeadDeterminesAssociated。
- `merged_head_interpreted` / `concrete_head_interpreted`: 任意Common解釈で実stored headはtick(union(σ0,σ1)) / tick intの意味を正確に返す。
- `full_payload_head` / `separated_payload_head`: 固定二つの数学的completion（int,intとnever,int）はいずれも同tick intとCommon同値。
- `bottom_not_int` / `completions_differ`: bottomとintは非同値、二completionの変数0像も非同値。
- `distinct_declarations`: 固定二actual toImplは異なる。

検証: `cd lean && lake build --wfail` exit0（687 jobs）。独立focused trust0/warning-as-error exit0。
これはcanonical solverがどちらのcompletionを選ぶかを仮定した定理ではない。question一問に記録した未指定の運用判断を勝手に埋めていない。

## B4r6 checkpoint 3: canonical record residualのstable branch

新規 `CommonRoleStableRecordResidual`。payload型と重みは任意。
閉じた主張:

- `lookup_member`: 任意label,row,payloadで実lookup=some payloadならentryはrow所属。
- `matching_explicit_entry`: 任意labels,具体goalで宣言check=trueかつ実label headMatches=trueなら、normalize goal所属かつlabels内labelのentryが存在。
- `capture_is_normal`: 任意labels,goalで実canonical captureはfirst-wins N固定。
- `residual_count_le`: 任意payload occurrence重み,labels,rowで実residual filterはcount非増加。
- `checked_residual_decreases`: 任意labels,具体goal,check=true,実label headMatches=true、任意size重み/任意name別occurrence重みで、実canonical captureのsizeは元goalより真に小さく、全nameのoccurrenceは非増加。
- `repeated_label_allowed` / `empty_head_rejected`: 任意labelの重複label列はbranch check=true、空label列はfalse。

検証: `cd lean && lake build --wfail` exit0（688 jobs）。fresh independent auditはtrust0/warning-as-error exit0。
これはpayload照合全体やfull source checkerではなく、実残余計算のdescent component。tailを任意のmasked Common代入としていない。

## B4r6 gateと未指定capture境界

`cd lean && lake build --wfail` exit0（688 jobs）。
`cd lean && lake env lean --trust=0 Audit.lean` exit0、allowlist56666 declarations。
全45新規theoremを登録、追加公理/sorry/native_decideなし。
二つの独立reviewはchecker sandwich proof、全Form代入の量化、実WF、実record lookup/capture、固定completionと運用captureの区別を確認。
terminal例のparser probeはok1/recovery0。

新results `2026-11-07-m1-b4r6-results.md`、設計note、README追記はcomponent/full目標の境界とE1/E2未到達を明記。
新questionは一問のみ。二択を曖昧性（推奨canonical共有捕捉）と全体保留に分け、ユーザー判断が一回答で定まる形にした。
未指定のhead captureを任意Common存在代入で埋めず、現語へのE2を出していない。
fullCommon/source checker、全regular matcher/resolver/exact dictionary、finite-tree/nominal agreement、qualified実生成/全familyは残る。
prover role不在、primary構成/別agent監査。既存proof/spec/公開入口/旧結果は変更せず、許可追記と新moduleのみ。

B4r6最終文書reviewも通過。全45定理の名前/日本語量化/前提とAudit登録、688jobs/56666allowlistの記録を独立確認。
componentをfull E1にせず、固定completionを運用上の存在captureにせず、未決一問を勝手に採用しない境界に阻害事項なし。
第六回もE1/E2には未到達。元contractのexistential-substitution addendumに従い、操作的capture規則のユーザー判断が必要。

# B4r7 開始（2026-11-08、成果物名は原契約の2026-11-07を維持）

開始HEAD 0216852d96a3fc88f29a0a615ab74baf587b0802、clean tree。
spec6.3のplain variable branchは両方へ合流payloadをそのまま捕捉する承認を読んだ。
旧数学的completionの存在をruntime選択とせず、有限で計算する共有captureと承認済み曖昧性を新moduleで形式化する。
prover設定/live roleは不在のためprimary構成、別agentへnonvariable branchの独立auditを依頼した。

tupleの共有component projectionとwhole再構築チェックはCommon意味の完全性に必要だが、
より強い未指定点として、invariant nominalの複数alternativeは引数合流で一つにまとめられない。
保持されたnominal alternativeへの有限coverをhead matcherが許すかを一問候補として点検する。
任意Common splitやE2は仮定しない。

## B4r7 checkpoint 1: opaque payloadのcanonical共有捕捉

新規 `CommonRoleSharedPayloadCapture`。任意Payload型をopaqueのまま扱い、実有限binding表を計算する。
閉じた主張:

- `lookup_repeated_payload` / `assignment_exact`: 任意names,payload,nameで、raw/実normalized binding表lookupは名前所属ならsome同payload、それ以外none。
- `captured_as_is` / `unmentioned`: 任意同入力で所属/不在から上のlookup結果。
- `bindings_unique`: 任意names,payloadで実binding表のlabel列はNodup。
- `capture_sound` / `capture_complete` / `capture_exact` / `capture_unique`: 任意names,payload,任意Option像について、独立Capturesは計算済assignmentとiff、指定された像は一意。
- `both_same` / `duplicate_unchanged`: 任意二所属nameの像は同じ、任意nameの重複追加はassignmentを変えない。
- `total_captured_as_is`: 任意fallbackを用いてtotal化しても、所属名の像は同payload。
- `actual_merge`: 任意tag,first,restについて実Variants.Merged.normalizeはsingle tagの右結合variablePayloadを返す。
- `interpret_payload`: 任意first,rest,Common像,payloadで全所属像=payloadなら、実格納payload解釈は反復union(payload)に等しい。
- `approved_head_meaning`: 任意tag,first,rest,任意Common payload/fallbackについて実計算captureで格納headを解釈すると反復unionのvariantを返し、それはvariant tag payloadとCommon同値。
- `approved_two`: 任意payloadで固定名0/1は共に同payloadを捕捉。
- `no_bottom_split`: 固定int payloadの実capture0はbottomと要求同値でない。

検証: `cd lean && lake build --wfail` exit0（689 jobs）。任意Common意味への比較であり、任意payload goalのK2 Readyを主張しない。

## B4r7 checkpoint 2: actual candidate / ambiguity / terminal Plan

新規 `CommonRoleCanonicalPayloadCandidates`。readableなvariable/int head componentで実Roles.Impl fieldsを読む。
閉じた主張:

- `finite_ready`: 任意visible,有限Ground Goalでdescriptionは両K2のReady。
- `payload_capture_exact` / `head_capture_exact`: 任意実Term/Impl,有限Ground goal,Option像について、このcomponentの計算済capture table存在 iff独立に指定されたCaptures。headではrole/tag照合を含む。
- `head_matches_exact` / `mem_candidates`: 任意同入力で実Bool候補iff独立prescribed capture像存在、任意visibleでcandidate membership iff visible所属と同capture存在。
- `merged_capture` / `concrete_capture`: 任意Ground payloadで承認例の実第一implは両名へ同payload、第二implはpayload=intの場合だけ空capture。
- `actual_candidate_list`: 任意Ground payloadで実候補列はintなら第一/第二、他なら第一のみ。
- `approved_ambiguous` / `other_payload_selected`: 固定intでは実head分類=ambiguous、任意payload≠intでは第一selected。
- `actual_two_images` / `approved_independent_overlap`: 任意payloadの両lookup同値と、固定intの独立二候補（実impl相異）を証明。
- `TerminalEvidence.all_visible`: 任意同componentの独立terminal evidence,任意実Plan宣言所属からvisible所属。全実where=[]を必須とする。
- `approved_no_dictionary`: 固定intの独立terminal辞書は存在しない。
- `other_payload_dictionary` / `example_dictionary_exact`: 任意payloadについて独立terminal辞書存在 iff payload≠int。
- `approved_no_plan` / `other_payload_plan` / `example_plan_exact`: 固定intでは実Planなし、任意payload≠intでは実第一impl leaf、任意payloadで実Plan存在 iff独立terminal辞書存在。

検証: `cd lean && lake build --wfail` exit0（690 jobs）。unsupported compound headsをfull languageのnoImplとしない。

## B4r7 checkpoint 3: invariant nominal coverの判断境界

新規 `CommonRoleNominalCoverBoundary`。運用上のcover/captureを採用していない有限case analysis。
閉じた主張:

- `argument_equivalent_exact`: 任意二ArgumentCode（int/bool/int|boolの三code）でCommon意味同値 iff code等号。
- `box_invariant`: 任意二Common引数で実nominal box subtype iff引数Common同値。
- `coded_box_exact`: 任意二codeの実box subtype iff code等号。
- `boxes_distinct` / `joined_not_integer` / `joined_not_boolean`: 固定int/boolのboxは別で、box(int|bool)はbox int/boolのいずれへのsubtypeでもない。
- `no_single_box_upper`: 任意Common引数Aでbox intとbox boolの両方をbox A以下にはできない。
- `cover_exact`: 任意有限code列source/targetで実有限cover Bool=true iff提案した有限support関係Covers。
- `covers_enumerated`: 固定三code空間での実有限探索結果は(int,bool),(bool,int)の二つだけ。
- `forward_cover` / `reverse_cover` / `joined_fails`: 固定二coverは提案関係を満たし、両方joinedにするものは満たさない。
- `covers_change_child`: 固定二coverが変数0へ与えるint/boolはCommon非同値。
- `private_child_decreases` / `all_term_substitutions_decrease`: 任意unary nominal constructor番号,任意有限実引数Term（後者は任意実代入0/1像）で、同一alternativeのみを縮約したsize frameは第一引数より真に大きく、全occは第一引数以上。size-only componentでfull nominal loweringとはしない。
- `allow_cover_two_candidates` / `forbid_cover_one_candidate`: 固定提案kernelはcover許可ならkeys[0,1]、不許可なら[1]。

検証: `cd lean && lake build --wfail` exit0（691 jobs）。三code探索を全Common matchingのsmall-model theoremとは呼ばない。

## B4r7 checkpoint 4: 旧独立Common head/Planとの有限family一致

新規 `CommonRoleSharedPayloadAgreement`。
閉じた主張:

- `previous_merged_matches`: 任意Ground payloadで、計算済canonical共有captureをCommonへ写した明示像が、旧実head解釈のmerged一致を与える。
- `previous_concrete_exact` / `canonical_concrete_exact`: 任意Ground payloadで旧任意Common一致存在 / 新canonical capture存在は共にpayload=intとiff。
- `finite_head_agreement`: 任意Ground payload,任意承認例visible実implについて、新canonical候補存在 iff旧独立Common一致存在。
- `previous_no_unique_at_int`: 任意実implについて固定intで旧候補一意性は成り立たない。
- `previous_unique_other`: 任意payload≠intで旧候補は第一implに一意。
- `previous_selected_plan`: 任意payloadで旧第一impl一致存在かつ一意 iff payload≠int。
- `actual_plan_agrees_previous`: 任意payloadで実terminal Plan存在 iff旧第一impl一致存在かつ一意。

検証: `cd lean && lake build --wfail` exit0（692 jobs）。旧側の任意Common代入は比較定理だけに現れ、実captureを定義しない。

## B4r7 checkpoint 5: stable checkerと実shared captureのgoal下降を接続

新規 `CommonRoleSharedCaptureDescent`。finite Form/idempotence stageのglueでありfullCommon Nとはしない。
閉じた主張:

- `encode_variables`: 任意first,restについて再帰的variableForm.encode=実variablePayload。
- `normalized_variables`: 任意first,rest,任意Form像,payloadで全所属像=payloadならN(variableForm[像])=N payload。
- `actual_head_is_goal`: 任意first,rest,任意Form payload/fallbackで、計算済total shared capture後の実N head引数列はN済single-tag goal引数列に等しい。
- `canonical_capture_strictly_decreases`: 任意role,key,first,rest,実where列、同宣言の実stable check=true、任意所属child、任意Form payload/fallbackについて、計算済shared capture後のN child sizeはN済goal sizeより真に小さく、任意nameのoccはN済goal以下。

検証: `cd lean && lake build --wfail` exit0（693 jobs）。全67新規theoremをAuditへ登録。
追加の `unsupported_explicit` / `example_supported` も全visible/goalでcomponent範囲外ならunsupported、承認例visibleは範囲内を証明した。
unsupported compoundを言語のnoImplへ読み替えない。

## B4r7 最終gateと未決non-variable branch

`cd lean && lake build --wfail` exit0（693 jobs）。
`cd lean && lake env lean --trust=0 Audit.lean` exit0、allowlist56986 declarations。
全67新規theoremを登録。追加公理/sorry/native_decideなし。
独立fresh reviewは全五moduleのtrust0/warning-as-error、全67日本語statement/Audit登録、最終文書scopeを確認。
独立最終Auditもexit0/56986 declarations。
開始HEADから既存Leanの許可外変更なし、Yulang.lean/Audit/READMEのappend-onlyを機械確認。
questionのsource blockは独立parser probeと完全一致、ok1/recovery0。型をbox int/box boolへ先に確定させた経路を使う。

新results `2026-11-07-m1-b4r7-results.md` と設計note/README追記に全量化、build/Audit末尾、正確な不足を記録。
新questionは `2026-11-07-b4r7-nominal-alternative-capture.md` 一問のみ。
推奨finite cover/where決定性は未承認で、現在のtheoremへ採用しない。
三codeのcover実験やsize-only nominalFrameを全Common carrier/全matchingの証明としない。
component classifierのunsupportedを言語のnoImpl/新拒否にしない。

E1/E2には未到達。今回の明示指示とcontract addendumに従い、未指定のnon-variable nominal captureを一問へ置いた。
full stable checker/N、全regular matcher/resolver/exact nested dictionary、一般finite-tree/nominal agreement、qualified実生成/全familyは残る。
これらを外部support/fuel/success仮定へ移した同名E1や、任意Common splitを仮定したE2は出していない。
prover role不在、primary構成/別agent監査。公開入口/spec/旧結果を変更せず、commit/push/networkなし。

## B4r8 開始（2026-11-08）

開始HEAD `3f9adabdce5f5152c0c85c1eb8757dc64b9ccb3c`、開始時tree clean。
第七回の問いの選択肢3（non-variable payloadをsplit/coverしない）がspec6.3の確定本文へ入ったことを確認。
既存のE2、component証明、旧resultsを保持する。拒否先行は未決のworking choiceのまま。
prover roleの登録・callable surfaceは今回も無く、primaryによる構成と独立read-only監査を使う。

全regular型を単なるgraph IDの等号で比較する置換は採用しない。
同じplain変数が複数箇所に現れると、捕捉値の要求同値を検査する必要があるためである。
また、同tag payload内のNはsyntactic idempotenceだけでは足りず、any/neverのunion則、
tuple/arrow等の既存Common coalescingを保つ必要がある。
これらは追加E2ではなく、全matcherとfinite-view下降への証明義務として扱う。

## B4r9 interval訂正: 証明再開前の設計監査（2026-11-08）

ユーザー訂正を受け、点capture matcherの構成を停止。未コンパイル草案CommonRoleCaptureMachineを削除し、既存証明は変更しない。
非空のreference二ファイル（role124行/sandwich168行）と現spec6.5を全文再読。
`notes/design/2026-11-08-b4r8-interval-model.md` を新規作成してから証明再開へ移る。
中心なしendpoint、mergeと交差制約、主型＋全rolesのreadiness/sandwich、variance/level、全where/associated再投入を記した。
全CommonRole 65moduleの明示theorem733件を索引し、元statementの真理と新intervalモデルへの移送を区別した。
旧五E2はいずれも現在のinterval/Yulang障害として未証明。特にfinite-tailの任意像は実subtractionと食い違う。
既存CommonBoundCoalescing/CanonicalIntervals/BoundRef*/DemandBoundPropagation/CommonDemand*のAPIと前提を調査。
候補の区間整合とlower anchor固定の未確定点は `2026-11-08-b4r9-interval-candidate-anchor.md` 一問に限定。
その回答に依存しない区間代数/通常制約生成を先に閉じる。新しいE1/E2はまだ主張しない。

## B4r9 checkpoint 1: 中心なし区間と実交差制約（16定理）

新規 `CommonRoleIntervals`。carrierは既存Boundのpairのみ、endpointの意味は既存Common。
全ての以下の任意入力は全称量化し、明記していない成功・有限木・support前提はない。

- `fits_merge`: 任意二Common endpoint区間A,Bと任意実型Tで、merge(A,B)がTを挟む iff AとBがともにTを挟む。
- `valid_iff_nonempty`: 任意Common区間Iでlo≤up iff ある実型TをIが挟む。証人は数学上のみで、中心fieldやruntime選択は作らない。
- `valid_merge_exact`: 任意二Common区間で、mergeのlo≤up iff 元二区間の整合かつ両交差loA≤upB・loB≤upA。
- `fits_pin`: 任意二Common型T,Uでpin(T)がUを挟む iff U≈T。
- `valid_pin`: 任意Common型Tでpin(T)は整合。
- `fits_congr`: 任意二区間のlower同士・upper同士がそれぞれCommon同値、任意実型Tなら、両区間がTを挟むことはiff。
- `merge_pin_valid`: 任意二Common型A,Bでpin(A)/pin(B)のmergeが整合 iff A≈B。
- `two_sided_equality`: 任意Common型A,B,Tでpin(A)/pin(B)のmergeがTを挟むならA≈B。他の主型位置から変数を削除する操作ではない。
- `fits_coalesce`: 任意有限Common区間列Is,任意Tでjoin lowers/meet uppersのcoalesceがTを挟む iff 全所属区間がTを挟む。
- `valid_coalesce`: 任意同列でcoalesce整合 iff 任意二所属I,JのloI≤upJ。
- `mem_checks`: 任意Bound型、有限区間列Is、有限slot数n、既存Constraint cで、実checks所属 iff ある所属I,Jでc=check(loI,upJ)。
- `checks_exact`: 任意Bound型/eval:Bound→Common.Ty/有限区間列/有限slot数n/任意slot割当てvaluesで、実checksの既存Models iff 全所属I,Jでeval(loI)≤eval(upJ)。
- `checks_valid_exact`: 任意同入力で実checksの既存Models iff eval済coalesceの整合。
- `checks_real_argument_exact`: 任意同入力で実checksの既存Models iff ある実型Tがeval済全所属区間に挟まれる。これは独立意味の全model族の存在であり、head捕捉の任意点選択ではない。
- `checks_length`: 任意Bound型/有限区間列/有限slot数nで、生成checks長=区間数の二乗。
- `append_checks_exact`: 任意同Bound/eval/Is/n/valuesと任意既存problemで、problem++checksのModels iff 元problemのModelsかつeval済coalesce整合。

検証: `cd lean && lake build --wfail` exit0（694 jobs）。全16定理をAuditへ追記登録。
候補確定・readiness・interval全resolver/全辞書のE1ではない。設計note完成後に構成した最初の新component。

## B4r9 checkpoint 2: 既存ordinary atom/shared graphへの実生成（8定理）

新規 `CommonRoleIntervalGeneration`。endpointは既存Presence TyTerm、出力は既存tyLe atom列。
全ての任意入力は全称量化する。

- `atom_exact`: 任意名前型α、任意Common computation割当てρ、任意既存Constraint 0 (TyTerm α) cで、実atom変換後のHolds iff 元既存templateのHolds。slotは0で中心を作らない。
- `generate_exact`: 任意α/ρ/有限endpoint区間列Isで、実生成atom列のAll iff eval済coalesce区間のlo≤up。
- `generate_real_argument_exact`: 任意同入力で実All iff ある実Common型Tがeval済全所属区間に挟まれる。独立意味の存在でありruntime捕捉の選択ではない。
- `generate_length`: 任意α/Isで実生成atom数=区間数の二乗。
- `append_exact`: 任意α/ρ/Is/既存finite atom列Aで、A++generate IsのAll iff AのAllかつeval済coalesce整合。
- `compile_exact`: 任意有限slot数m/既存TyTerm(Fin m) endpoint区間列Is/任意Common computation割当てρで、eval済coalesce整合 iff 既存compile(generate Is)のある全node割当てがModelsを満たし、既存readbackがρと**等しい**。成功solver・grammar/support前提なし。元graphの未解消edgeは残す。
- `compile_append_exact`: 任意m/Is/ρ/既存atom列Aで、AのAllかつcoalesce整合 iff 既存compile(A++generate Is)にModelsとρの同一readbackを持つ全node割当てが存在。
- `compiled_reflects`: 任意m/A/Is/独立row割当て/全compiled node割当てについて、実compiled Modelsなら、その実readbackでAのAllとeval済coalesce整合が成立。arbitrary regular realizerを含む。

検証: `cd lean && lake build --wfail` exit0（695 jobs）。全8定理をAuditへ追記登録。
checkpoint1の独立reviewもtrust0/warningAsError exit0、全16量化と中心なし/既存生成を確認済み。
これらはinterval整合・交差の実生成とgraph反映。candidate確定/readiness/全branch matcher/resolverの完成ではない。

## B4r9 checkpoint 3: interval由来の変数等式を全ordinary構文へ運ぶ（16定理）

新規 `CommonRoleIntervalCongruence`。全入力の任意は全称量化する。
Relatedは同じ名前でtypeがCommon同値、rowがliteral等号という関係。型は任意Common regular値を含む。

- `related_refl` / `related_symm`: 任意名前型とCommon computation割当てでRelatedの反射・対称性。
- `related_extend`: 任意Related二割当て・同じfresh computationでextend後もRelated。ambient共有を保つ。
- `row_eval_equal`: 任意Related二割当て・任意既存RowTermでevalはliteral等号。
- `type_eval_equivalent`: 任意Related二割当て・任意既存TyTermでevalはCommon同値。全既存branch（union/inter/pair/arrow/record/default/variant等）、負arrow子も含む。nested nominalは既存TyTermに無いため別。
- `subtype_congr`: 任意四Common型A,B,C,D、A≈BとC≈DならA≤C iff B≤D。
- `atom_holds_congr` / `all_holds_congr`: 任意Related二割当て・任意既存atom/有限atom列でHolds/Allがiff。
- `formula_holds_congr`: 任意Related二割当て・任意既存Formula（全existsSlotを含む）でHoldsがiff。同じfresh computationを共有して量化する。
- `identify_related`: 任意DecidableEq付き名前型、任意代表名r/除去名d/割当てρ、pin(ρr.ty)とpin(ρd.ty)のmerge整合なら、dのtypeだけをρr.tyへ更新し全rowを保持する実identify後とρはRelated。
- `identified_equal`: 任意同名前/ρで実identify後のr/dのtypeはliteral等号。整合前提不要で、更新の定義の事実。
- `global_formula_identification` / `global_atoms_identification`: 任意同名前/ρ・任意Formula/atom列、上のmerge整合なら、全体でidentify前後のHolds/Allがiff。
- `interval_checks_identification`: 任意同名前/ρ・任意既存TyTerm endpoint区間列、上のmerge整合なら全区間coalesceの整合がidentify前後でiff。
- `generated_variables_equal`: 任意名前r,d/ρで、実generate[(var r,var r),(var d,var d)]のAllが成立すればρr.ty≈ρd.ty。等式発見を外部から仮定せず、生成交差制約から導く。
- `global_formula_from_generated`: 任意DecidableEq付き名前型/同r,d,ρ/任意Formulaで、同実生成Allが成立すれば全体のidentify前後でHoldsがiff。

検証: `cd lean && lake build --wfail` exit0（696 jobs）。全16定理をAuditへ登録。
interval由来の変数-変数等式の全ordinary contextへの保存であり、具体構造liftの全体sandwichやlevel実装を証明したとはしない。
checkpoint2の独立reviewもtrust0/warningAsError exit0。Fin0で排除するのは新template slotだけで、endpointのambient変数は保持していることを確認済み。

## B4r9 追加訂正: nominal variance（2026-11-08）

spec6.5の更新を再読し、設計noteを同日ユーザー訂正へ合わせた。
boxは共変でbox(int|bool)へ合流。不変区間は無限に入れ子になりうるlist/木等の引数に使い、varianceは型宣言時metadata。
旧一律nominal不変APIやbox_invariantを現source boxへ移送しないと明記。
全head branchの方向表を追加し、non-variable no-split決定を要確認へ戻した。
未確認のnon-variable規則を新しい証明へ採用しない。plain-variable承認は維持する。
既存40新規定理はCommon区間・既存ordinary構文だけの事実であり、nominal全引数不変やno-splitを前提にしていない。
checkpoint3独立reviewもtrust0/warningAsError exit0。全型/row共有、同fresh量化、type-only identifyを確認済み。

## B4r9 方向付け: interval制約＋lower-head deferral（2026-11-08）

最新ユーザー指示に従い、設計note§3/6/7/8を再記述。
独立意味はinterval制約・伝播・遅延とし、候補を存在代入探索で定義しない。
lower head未確定はpending、既知なら伝播後の残存候補一/多/零をselected/ambiguous/rejectedへ分類する。
whereはhead選択後だけ新しいinterval制約として投入、全child完成時だけ実有限辞書を返す。
Mark/int/anyの旧anchor質問は取り下げ。sourceの具体分類は実伝播から導くので、新たなpoint前提へ戻らない。
Patersonは選択後の無限where生成を防ぐため引き続き必要。pendingを残すだけでは、全lower head既知のgrowing chainは止まらない。
全旧E2は各旧モデルでは真だが、deferred interval/Yulangへの移送は未証明。最新全承認に対するE2として数えない。
