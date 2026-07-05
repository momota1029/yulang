# Evidence Slot 静的化 計画（2026-07-05、Claude 署名・ES-0/ES-1 着手承認済み）

状態: ユーザ承認済み（2026-07-05、「いいよ！」）——**Stage ES-0（計測）と ES-1（共有メモ化）から着手**。ES-2/ES-3 は ES-0/ES-1 の結果を見てから改めて判断。実装は Stage ごとに段階承認を要する大規模プロジェクト。

## 背景・動機

2026-07-05 夜、`lib/std/text` の文字列スキャナ高速化（43f83284、後に 2242c69b で revert）が思わぬ副作用を出した: 実行時に一度も通らない「大きい入力向け」分岐がプログラムの specialized IR に存在するだけで、`evidence_vm::build_plan`（`crates/evidence-vm/src/lib.rs:554`）の実行時間が約3倍に増えた。実測: runtime IR バイト数は +17〜21% なのに、evidence_plan_build 時間は 25.4ms→73-76ms（約3倍）。バイト数を物差しにすると不釣り合いに見えるが、プランナーが実際に見ている量（runtime tasks +65%、runtime nodes +76%、delayed boundaries +89%、generic fallbacks +56%）で見ればもっと大きい——それでも 3 倍という結果の全部は説明しきれず、残りは **`collect_value_env_plans`／`attach_evidence_call_plans`／`LexicalHandlerIndex`など複数の独立したパスが、同じ関数本体を共有メモ化なしにそれぞれ歩いていること**に由来する（Codex 調査で確認済み）。

これは「未使用コードでも全プログラムが課税される」グローバルな話ではない——実際にその stdlib 関数を呼ぶ specialized プログラムだけが、その関数本体（使わない分岐も含め全部）の解析コストを毎回の起動時に払う。プログラムを実行するたび、実行しない分岐の構造解析コストまで律儀に払っている状態。

ユーザ判断（2026-07-05）: 応急処置（ホストプリミティブへの退避、閾値調整）ではなく、かねてから温めていた**根本方針＝evidence slot の静的化**（証明発行を mono/specialize 時へ前倒し）に今から着手する。機能が安定している今のうちに。共有メモ化はこの静的化に組み込む前提で進める（単体パッチにしない）。

## 位置づけ: 既存計画との関係（重要）

`notes/design/2026-07-02-speedup-proof-system.md` が最初に提案した5項目のうち、これは**提案2そのもの**:
1. 静的 route 昇格（`notes/design/2026-07-02-static-route-promotion-plan.md` として着手済み・現在 Stage M1 で停滞中——static-tail hit が全ワークロードでゼロ）
2. **evidence slot 静的インデックス化**（本ノートの主題）
3. scope-delta 正規化（native close cert 簡素化、別途）
4. known-handler 代数カタログ化（State の次、特に Fold）
5. 三層 check 配置（mono-time / handler-entry-time / signal-time）

**静的 route 昇格と evidence slot 静的化は同一軸の関係にあり、後者は前者を土台に一般化する**。共有機構はすでに存在する: specialize が `RuntimeEvidenceSurface`（`static_routes`、`known_state_handlers` 等）を計算し、evidence-vm がそれを消費する、という「specialize が計算・evidence-vm が消費」というパターンは、`known_state_handlers`（2026-06-30 known-state-handler-plan）と `static_routes`（2026-07-02/03 static-route-promotion）ですでに実証済み。evidence slot 静的化は、このパターンを**もっと多くの plan artifact に広げる**話。

**しかし決定的に重要な発見**: 今日の退行の直接原因（build_plan の重複構造解析）は、静的 route 昇格が「解決できるか（static-tail hit > 0）」に依存しない。**共有メモ化（同じ本体を複数パスで二度と歩かない）だけでも、静的 route 昇格が停滞したままでも独立に効く**。したがって本計画は静的 route 昇格の成否を待たずに着手できる、別の切り口を持つ。

## 現状の build_plan アーキテクチャ（確定事実）

`evidence_vm::build_plan`（lib.rs:554）は起動のたびに、到達可能な specialized プログラム全体を構造的に歩く:
- `ControlEvidenceProgram::from_program` で control evidence 再構築
- `collect_value_env_plans`（lib.rs:1496）— Lambda/MakeThunk/FunctionAdapter を再帰的に独立スキャン
- `attach_evidence_call_plans`（lib.rs:1268）— 関数 plan ごとに個別に本体を歩く
- `LexicalHandlerIndex`/`build_lexical_handler_envs`（lib.rs:4281/2475）— root/instance/分岐本体をグローバルメモなしに歩く
- provider index、static-route summary、known-handler plan の組み立て

これらは互いに独立したパスであり、同一の本体（特に closure/thunk が密な箇所）が複数回解析される。

## Per-artifact 静的化可能性（Codex 調査、確定）

| artifact | 静的化可否 | 残る動的部分 |
|---|---|---|
| Control evidence | ほぼ可 | 意図的に Unhandled/blocked な route のみ |
| Lexical handler indexes | ほぼ可 | delayed/callback boundary は保守的に動的のまま |
| Handler plans | 可 | arm class（abortive/tail-resumptive/one-shot/multi-shot/escape/fallback）は構造的に静的。multi-shot の意味論は実行に影響するが分類自体は静的 |
| Operation plans | 部分的 | identity/path/kind/lowering shape は静的、provider-env/open-row/host/delayed の実ターゲットは動的 |
| Function plans | ほぼ可 | 必要 evidence の集合は静的、実際の evidence 値は runtime 引数 |
| Value plans | 部分的 | 捕獲 evidence 要求の形は静的、捕獲される provider 値自体は動的 |
| Call plans | ほぼ可 | 既知 instance 呼び出しの必要 slot は静的、first-class/動的呼び出しは残余 |
| Object plans | ほぼ可 | slot・オブジェクト組み立ては静的、active frame/provider env/state frame/continuation snapshot は当然 runtime 保持 |
| Provider indexes | 部分的 | slot→handler 候補写像は静的、どの provider env が非遮蔽で active かは動的（静的 routing/slotting で証明できない限り） |
| Static-route summaries | 可 | すでに specialize が計算・evidence-vm が join。runtime hit はプロファイリング専用 |
| Known-handler plans | 部分的 | 証明は静的起源、runtime state frame 内容・snapshot/fork 挙動は動的 |

**要点**: ほとんどの artifact が「形は静的、内容の一部が動的」という構造を持つ。全部を静的化する必要はなく、**静的な形（shape）を specialize/mono 時に確定し、動的な残余だけを軽い実行時テーブル構築に落とす**のが正しい境界。

## 既存の配管（そのまま使える先例）

- `SpecializeOutput`（specialize2/runtime_evidence.rs:13）はすでに `mono::Program` と `RuntimeEvidenceSurface` を束ねている。
- `Specializer2::specialize_with_runtime_evidence`（emit.rs:12）が mono program 構築後に known-state handler と static-route profile を付与する、という「後付け attach」の実績パターンがある。
- `RuntimeEvidenceRunContext::from_plan`（runtime/plan.rs:128/221）はすでに「plan artifact から expr-indexed テーブルを組み立てるだけ」という軽い消費側の実装例——動的残余の処理はこの形に寄せればよい。

## 難所（Codex 調査で確認、実装前に必ず踏まえること）

1. **slot key は family だけでは足りない**——`family + visibility/blocker route + projection boundary` が必要（2026-06-27 evidence-passing-paper-notes:291）。
2. **handler 定義文脈の保持**——handler evidence は「どの evidence vector/env の下で定義されたか」を運ぶ必要があり、単なる handler pointer では足りない（同 notes:81）。
3. **SCC/相互再帰**——静的解析には SCC 縮約＋一回の伝播が要るが、[[feedback-no-heavy-fixpoint]] の既存ルール（重い不動点反復を足さない）に従うこと。静的 route Stage M0 がすでにこの骨格（task 内字句解決＋SCC 縮約＋一回伝播、不動点反復なし）で実装済み——**これを再利用・一般化するのが最有力**。
4. **付与タイミング**——specialized instance identity・closed runtime signature は `ensure_def_instance` 後にしか存在せず、control IR の expr id はさらに後まで存在しない。早く付けすぎると evidence-vm が必要とする正確な id を失う。
5. **known-state directness は route 証明だけでは足りない**——型/evidence routing だけでは handler の意味を証明できない（2026-06-30 known-state-handler-plan:39 の既存知見）。
6. **continuation 意味論（snapshot/fork、multi-shot、state frame）は本質的に動的**——これは失敗ではなく正しい境界。Koka 系 evidence passing 自体も一部の evidence は値として動的に運ぶことを認めている。

## 共有メモ化の位置づけ（ユーザ指定: 静的化に組み込む）

自然な設置点は「specialize/control レベルの task/body/expr id をキーにした body evidence summary」——today の build_plan が control evidence／lexical handler index／handler-arm 分類／function call evidence／value env 要求／lexical handler env／object 組み立てを別々に歩いている部分を、**一度だけ計算して共有する**。この構造解析そのものを static slot 計算パスに寄せれば、動的残余は「すでに付与された plan artifact からのテーブル構築」（`RuntimeEvidenceRunContext::from_plan` 相当）だけになり、重複構造解析コストがほぼ消える。

## 段階案（Stage ES-0 〜 ES-3、既存の Stage T/F/S・static-route Stage 0/1/2 と名前衝突しないよう ES= Evidence Slot と命名）

### Stage ES-0（計測のみ、挙動変更なし）
build_plan の各パス（collect_value_env_plans / attach_evidence_call_plans / LexicalHandlerIndex 系 / provider index / static-route join / known-handler join）ごとに実測タイミングと重複解析率（同一本体が何回歩かれているか）を計測する counter/instrumentation を追加。これにより「共有メモ化だけでどれだけ回収できるか」を静的 route 昇格の成否と切り離して定量化する。今日の regression 再現ケース（String Match 相当）を canonical ベンチとして使う。

### Stage ES-1（共有メモ化、静的化なし・挙動変更なし）
build_plan 内で、task/body/expr id をキーにした一回限りの構造解析結果をキャッシュし、複数パスから再利用する。**まだ mono/specialize 時への前倒しはしない**——あくまで「同じ実行時パス内での重複を減らす」だけなので、静的化より遥かにリスクが低い。ES-0 の計測で見積もった回収量と実測を照合。ここで regression ケースがどこまで戻るか確認。

### Stage ES-2（表として静的化・shape のみ）
「ほぼ可」「可」評価の artifact（control evidence、lexical handler indexes、handler plans、function plans、call plans、object plan の shape、static-route summaries）を specialize/mono 時に計算し `RuntimeEvidenceSurface` に付与、evidence-vm 側は consume のみに変える。既存の known_state_handlers/static_routes の attach パターンを一般化。SCC 条件・付与タイミングの難所は静的 route Stage M0 の骨格を再利用。

### Stage ES-3（部分静的化・動的残余の切り出し）
「部分的」評価の artifact（operation plans、value plans、provider indexes、known-handler plans）を「静的な形」と「動的な残余」に分割し、残余だけを軽量な実行時テーブル構築に落とす。

### 継続的な動的残余（今後も変わらない）
provider env の実内容（closure/thunk/callback を跨ぐ場合）、open row・effect subtraction 残余、host escape、continuation snapshot/fork・multi-shot・state frame——これらは静的化の失敗ではなく正しい境界として動的なまま残す。

## 追記（2026-07-05 夜、Claude 署名）: ES-0 計測結果——当初仮説の訂正

Stage ES-0（build_plan の各サブパス計測＋重複歩行検出、commit `dd214b2f`、zero behavior change 確認済み・plan output byte-identical）の実測結果、**「複数パスにまたがる重複構造解析」という当初仮説は今回の regression の主因ではなかった**。

- redundancy ratio は baseline 2.65 → bloated 2.67 でほぼ不変。
- `lexical_handler_index`/`handler_plans`/`call_plans`/`value_env_plans`/`object_plan` など build_plan の後続サブパスは、bloated ケースでも絶対時間がほぼ動かない（例: lex_idx 0.070ms→0.132ms）。
- **退行 551.8ms のほぼ全部（551.6ms）が単一のフェーズ `control_evidence`（`ControlEvidenceProgram::from_program`、crates/control-vm/src/evidence_ir.rs）に集中**している。String Match: 21.8ms→573.4ms（約26倍）。

つまり ES-1 として当初計画していた「build_plan の複数サブパス間の共有メモ化」は、この具体的な regression にはほぼ効かない。ES-0 を計測専用の段階として先に独立させておいたおかげで、効かない実装に進む前に気づけた。

**次の一手**: `ControlEvidenceProgram::from_program` 単体を対象にした集中調査（ES-0b）——この関数がなぜ IR サイズ+17〜21%に対して約26倍もコストが増えるのかを specific に調べる。redundancy ratio が変わらないことから、build_plan 外側の重複ではなく、**この関数内部**に別の増幅機構（内部での重複歩行、closure/branch 密度に対する非線形コストなど）がある可能性が高い。ES-1（共有メモ化の実装）は、この内部機構が判明してから、対象を絞って再設計する。

## 追記2（2026-07-05 夜、Claude 署名）: ES-0b で真因確定——メモ化ゼロの callgraph 展開

`ControlEvidenceProgram::from_program`（crates/control-vm/src/evidence_ir.rs:31）は、handler-passing backend 向けの static evidence（instance entry・stack/type evidence・catch-handler arm shape・effect operation route・function-adapter hygiene・delayed lambda/thunk boundary・fallback site）を構築する。アルゴリズムは単純な一回歩行ではなく、**既知の呼び出し/instance 参照に出会うたびに callee 本体を再帰的に展開する**形。`active_exprs`/`active_instances` は**サイクル検出のガードのみで、結果のメモ化ではない**。

**確定した機構**: `Expr::Apply` の callee が `InstanceRef` のとき、(1) `visit_expr_id(callee) → InstanceRef → visit_instance_entry` で本体を歩き、(2) 別途 `visit_known_call_site → visit_known_instance_call_site → visit_known_callee_entry` で**同じ本体をもう一度**歩く（evidence_ir.rs:476/524/641/675/702/791）。呼び出し文脈をキーにした再利用が一切ないため、小さいヘルパー関数が連鎖して呼び合う構造（今回のスキャナ書き直しがまさにこれ: `word_prefix_at → word_prefix_ascii_or_slow_end → word_prefix_ascii_chunk →（fold内）→ word_prefix_ascii_step`、さらに slow path 側も同型の連鎖）では、呼び出し経路の掛け算でコストが指数的に近い形で膨張する。

**実測（String Match）**: expr 訪問回数 355,442（baseline）→12,276,082（bloated）、ユニーク式は1,460→2,271（1.55倍）。**再訪問倍率が 243倍→5,405倍**（22倍化）——IR サイズの伸び（+20.7%）から大きく乖離。片方の展開経路だけ無効化する ablation で 39.7ms→9.5ms/14.1ms、両方無効化で 436μs（フロア）まで落ちる、という切り分けで機構は確定と言ってよい。

**重要な副次発見**: `ControlEvidenceProgram::from_program` は `ControlEvidenceIndex::new`（runtime.rs:8793）からも呼ばれており、**同じ高コストな計算が runtime 経路でも別途発生しうる**——build_plan 時点の一回だけではない可能性。要追加確認。

**base line ですら 243 倍の重複がある**——現状「安く見える」のは今のコードベースの呼び出し連鎖がまだ浅いからにすぎず、今後スタイルとしてヘルパー関数を増やす stdlib 変更は同種の爆発を踏みうる時限爆弾。これは speedup-proof-system.md が指摘する「Koka なら静的に証明する内容を動的に再生している」構造そのものであり（build_plan の最初のサブパスとして呼ばれる: lib.rs:786）、evidence slot 静的化の射程内。

**未解決の難所（実装前に必ず解く）**: 素朴に「同じ ExprId なら結果を使い回す」というメモ化は**不健全**な可能性が高い。route classification は現在の `EvidenceContext`（handler stack の形＋callback/delayed boundary の深さ）に依存するため、同じ式でも呼ばれる文脈が違えば正しい分類結果も変わりうる。ES-1 実装前に、**どこまでを cache key に含めれば健全か**（handler stack 全体か、その一部の shape か、boundary depth か）を精査する専用の調査が必要——ここを雑にやると「静かに間違った evidence が使われる」という、今日一日通して警戒してきた種類のバグになる。

## 追記3（2026-07-05 夜、Claude 署名）: 健全な cache key 設計確定——ES-1 実装へ

### Part A（同一呼び出しの二経路）: 完全重複ではないと確定、一本化は不健全

`Expr::Apply` の callee が `InstanceRef` の場合の二経路（(i) `visit_instance_entry` 経由の「値としての」歩行、(ii) `visit_known_callee_entry` 経由の「今すぐ呼ばれる」歩行）は、**意図的に異なる文脈で同じ lambda 本体を解析している**。(i) は delayed boundary を追加してから歩く、(ii) は追加しない——同じ本体内の effect operation が、(i) では `Blocked{delayed_boundary:true}`、(ii) では `Direct` になりうる、という**正当な使い分け**。単純に一本化するのは不健全と確定。この経路は今回のメモ化設計の対象にしない。

### Part B（cross-call-site メモ化）: 健全な粗視化を発見

`EvidenceContext`（evidence_ir.rs:1033）は `handlers: Vec<EvidenceHandlerFrame>` / `callback_boundary_depth` / `delayed_boundary_depth` を持つ。結果に影響する読み出しは実質2箇所のみ:
- `record_effect → classify_route(path, context)`——`context.handlers` を内側から走査
- `record_fallback`——`context.has_handler()`（`!handlers.is_empty()`）のみ参照

callback/delayed の深さそのものは、**handler stack が空である限り出力に一切影響しない**（`classify_route` は走査対象がなく、`has_handler()` も自明に false）。

今回のスキャナのホットケース（`word_prefix_ascii_or_slow_end → word_prefix_ascii_chunk →(fold内)→ word_prefix_ascii_step` 等）を実測したところ、**観測された「複数の文脈」は全て `handlers=0`（空）で、differ していたのは callback/delayed depth のカウンタ値だけ**だった。

**確定した健全な cache key 設計**:
- `handlers` が空のときは、callback/delayed depth の値に関わらず単一の `NoHandlers` キーとして扱ってよい（証明済み、ヒューリスティックではない: 上記の依存解析により、この場合これらの値は出力に一切影響しないため）。
- `handlers` が非空のときは、保守的にフルコンテキスト（handler stack 全体＋各フレームの handled path／resumptive flag／entry 時の depth＋現在の depth）をキーにする。
- **cycle guard との整合**: `active_exprs`/`active_instances` はキャッシュキーではなく、現在進行中の再帰スタックガード。ターゲットが現在 active（=完了前）なら、たとえキャッシュに完了済み結果があっても cycle fallback を優先しなければならない——キャッシュは「完了済みの結果」のみを保持・返却し、active な対象への参照は従来どおり cycle guard 経路を通すこと。

「更に広い粗視化（body ごとの effect-path summary で handler ありのケースも圧縮する等）」は今回のアルゴリズム解析だけでは健全性を証明できておらず、別の設計課題として保留する。今回実装するのは上記の「NoHandlers 粗視化＋非空時はフルコンテキスト」のみ。

### 次の一手: ES-1 実装

上記のキー設計で `ControlEvidenceProgram::from_program` に完了済み結果のメモ化を追加する。検証は「evidence 出力がバイト単位で完全一致すること」を主軸に、対象は今回の scanner ケースだけでなく既存の contract suite 全体・named canary 全て。

## 未決の設計論点（着手前にユーザ確認したい点）

1. Stage ES-0/ES-1（計測＋共有メモ化）から始めることに同意するか。静的 route 昇格の成否を待たずに独立着手できる点が利点。
2. slot key の最終形（`family + visibility/blocker route + projection boundary`）は ES-2 着手前に別途詳細設計が要る——これは大きめの下位設計課題になる見込み。
3. `EvidenceVmPlan` 自体を静的（シリアライズ）artifact にするか、`RuntimeEvidenceSurface` に静的 slot を足して evidence-vm が薄い plan を組み立て続けるかは、まだ確定していない（Codex 調査でも medium confidence）。

## 関連

- [[perf-findings-2026-07-05]]
- notes/design/2026-07-02-speedup-proof-system.md（本計画の親提案、提案2）
- notes/design/2026-07-02-static-route-promotion-plan.md／2026-07-03-static-route-mono-resolution-plan.md（同一軸の先行効果、Stage M0 の骨格を再利用予定）
- notes/design/2026-06-30-known-state-handler-plan.md（specialize→evidence-vm attach パターンの先例）
- notes/design/2026-06-27-evidence-passing-paper-notes.md（slot key・handler 定義文脈の理論的根拠）
- [[feedback-no-heavy-fixpoint]]（SCC 解析で不動点反復を避ける既存ルール）
