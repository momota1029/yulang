# 宣言索引による recursive formation の構成と固定 guard の残余

独立査読後の注記: R1–R3 の構造構成、R4 の条件付き assembly、R5 の参照 transport を記載範囲で受理。完全 J_rec/J_pub は未導出。[固定版と判定](../../tasks/agent-loop/sprints/extrusion-intrusion-scc-20261024-outcome.md)に記録する。以下の未査読・凍結表記は producer r1 の提出時点の記述である。この注記だけを停止後に primary が追加した。

Assignment EXTRUSION-INTRUSION-SCC-20261024/OM-REC/r1。Author `/root/astra_scoped_join`、descendants なし。
Status: 新しい source-owned データ構成と保存補題、条件付き hereditary 構成、固定 original predicate の正確な残余。完全 CompleteMem/KV、元の反例、production authority は未成立。
Contract `tasks/agent-loop/sprints/extrusion-intrusion-scc-20261024.md` SHA-256 `f0506f59f8baca172a9f4f68278cff3068bf2d6f61474c99d421251d0b04c435`。
Baseline `3ca3a9867a9fdc20841b983d047192ca7de9b672`。Requested Astra/medium、observed model/effort/duration UNKNOWN。

## 1. 固定 source と構成の境界

```
let rec f = lambda x.
  let g = lambda y. (lambda z.y)(f y)
  in {a=succ(g 0), b=g true}
in f
```

U=Int∨Bool、V={a:Int,b:Bool} を目標 endpoint とする。f は一つの monomorphic root、g の二 use は同じ actual g closure と f を使う。元の source/history/world/challenge/response/future、CompleteMem/KV、F1/FK1 と Simple-sub A/B・主型性・停止性を保存する。native G/F qualification と shared C は既知であり再計算しない。候補核 CH1–CH5 は操作 skeleton の確認に使い、original membership の結論に置換しない。

前稿の「registry/formation object がない」という部分を今回は実際の有限構成で取り除く。合法的に欠けた source-owned record を定義する権限を使う。ただし既に固定された `Phi` の independent guards、D、ActualAdm、P、CompleteMem の意味を変更する権限とは区別する。

## 2. 有限 declaration registry を作る

source tree の各 binder/Name/Lambda/Call/Bind/field/literal occurrence に、その構文位置の有限 path を key として割り当てる。これは source の lexical identity の表示であり、同じ字面を key にしない。主要 declaration を f,x,g,y,z、Lambda site を ℓf,ℓg,ℓw、Call site を q_fy,q_wrapper,q_g0,q_succ,q_gtrue とする。

有限 registry R の一行は

`(decl, enclosing_scope, code_site, role, formal, capture_slots, body_plan, source_result_port)`

である。Name 行は `(use_site,resolved_decl,lexical_path)`。body_plan は元の Return/Delay/Call/Bind/Record の有限 DAG と登録再帰参照であり、実行を展開しない。

生成手続は次の通り。

1. rec f の declaration と r_f の allocation slot を一度登録し、そのスコープを f RHS の Name resolution に開く。まだ ValueMem/InstalledWorld を登録しない。
2. ℓf の formal x をその body scope に登録する。g の initializer を外側 f が見える環境で走査し、ℓg の formal y、ℓw の formal z を各 child scope に登録する。
3. 非再帰 g は initializer の走査を終えてから record body の lexical environment に公開する。g の initializer から g 自身へ辺を作らない。
4. 各 Lambda の capture_slots は body の free resolved declarations から formal/local binder を除いた集合。f の自己参照は実 closure knot の capture reference として残す。各 Name は元の resolved_decl にだけ接続する。
5. 各 Call は callee plan と **全** argument plan を保持し、Value entry の receipt/Force/actual rebind/body/invocation-return port を別々に登録する。q_wrapper の引数は q_fy 全体であり削除しない。Record は元の field order を保持する。

直接得られる capture 表は以下である。succ は既存外部 primitive binding とし、Int/Bool/literal は元の declaration を参照する。

| site | actual closure capture |
|---|---|
| ℓf | f の同じ自己 root r_f と外部 succ binding |
| ℓg | f の同じ r_f。x と y は capture しない |
| ℓw | その g invocation で実際に受け取った y/root。z は capture しない |

「body から再帰的に利用する値」まで capture_slots に推移閉包して別環境を作らない。例えば g が f を持つことと g が succ を直接 capture することは違う。f の完全 capture/world の義務は f の証明参照を通じて保持する。

### 実 allocation と有限 schema

registry は closure **site** の有限表である。f の初期 allocation に r_f を一つ与え、f の actual invocation h において ℓg が評価された時だけ r_g(h) を作る。g の actual invocation k において ℓw が評価された時だけ r_w(h,k) を作る。keys は fresh allocation の証明用索引であり、歴史を runtime ID に置き換える規則ではない。原 allocator の actual fresh ID を index から指す。

```
env(r_f)      = { f ↦ r_f, succ ↦ r_succ }
env(r_g(h))   = { f ↦ r_f }
env(r_w(h,k)) = { y ↦ actual_returned_y(h,k) }
```

同じ h の q_g0,q_gtrue は同じ r_g(h) を指す。k は異なる。recursive f call は常に r_f。W の拡張では actual Return より前に parameter 値を置かず、初期 f closure を allocation するだけで g/world を事前実行しない。

**補題 R1（構成と scope/identity）。** 上の手続は有限時間で終了し、各 Name は元の binder、各 closure は正確な free capture、全 recursive f は同じ root を持つ。独立 g uses は f や既存世界を再初期化しない。

証明。source tree の構造帰納。rec は binder を RHS 前に一度挿入、通常 let は RHS 後に挿入する。Lambda の child scope は formal を覆い、終了時に元環境へ戻る。Name lookup はその環境で一意。free-declaration の帰納は上表を与える。再帰辺では既登録 root key を返して走査を止めるので有限。allocation は実評価 event ごとに元 allocator を使い、Name は allocation しない。□

**補題 R2（guarded code graph）。** f の唯一の source recursion cycle は ℓf の body と q_fy を通る。alias/証明名だけの cycle はない。g と wrapper の creation は inert lambda construction であり、g の先行 scheme を仮定しない。

証明。上の Name 表で r_f へ戻る use は ℓg 内 q_fy の callee。ℓg は ℓf body 内で形成される。いずれも Lambda body を跨ぐ。g initializer に自己辺はなく wrapper は y だけを読む。□

R2 は operational guard の構文的事実であり、元の independently specified profile/license guard を真にする定理ではない。

## 3. declaration-indexed evidence と既存 case への埋込み

各 source edge に次の有限証拠 constructor を付ける。

* `DeclAt(d,σ)` と `Resolve(u,d,path)` — 上の走査が供給する登録と lexical lookup derivation。
* `CaptureAt(ℓ,env,free_rows)` — free-declaration 計算と actual root tuple。捕捉値の **membership evidence** は別の依存参照として保持する。
* `EntryPlan(q,receipt,Force,rebind,body,return)` — 元の全 operand/port の同一性。
* `PendingAt(q,phase,suffix)` — 元 plan のその phase 以後の順序付き suffix。typed response、current world、原 raw handle は元 transition の引数。
* `ProofRef(d,root,contract,telescope)` — 登録 member の同時証明への参照。これは ValueMem の証明でも Installed/Established certificate でもない。参照先の full obligation と original telescope を保持する。

これらは新しい guard truth を返す axiom ではなく、明示された有限データと導出 tree である。source-owned constructor 部分の missing representation として採用可能な定義を与えた。unknown fixed predicate をこのデータの存在と定義し直さない。

**補題 R3（旧二 case との compatibility）。** 同じ手続を旧 `my f x=g; my g y=f` の既登録二 declaration に適用すると、相互 capture と二 actual root、Value entry と opposite-root Return が得られる。旧 `my apply f={my step x=f x;step}` では step の capture は outer Return から得た同じ actual f となる。追加した declaration key/ProofRef wrapper を忘れると、選択済み K/Strict の同じ raw graph、ports、captures になる。

証明。前者は両登録を先に行う選択済み simultaneous declaration constructor の実 slot を入力し、Name をその二 root に解決する。後者は元の sequential Bind と actual outer formal binding を入力する。手続は raw provider/operation/root/world を新しく解釈せず、各入力への有限 path を付けるだけなので、forget は全 typed operand に恒等。capture/port 表を直接比較すれば等しい。逆に元表の source occurrence から keys を一意に復元できる。□

これは既存 exact case を拡張データが壊さない証明である。full domain/opaque guard の新しい meaning の conservative extension を主張しない。そこには次節の独立適合証拠が必要である。

## 4. joint hereditary relation を実際に組む

complete descriptors は既存 Strict を使う。f の I_U entry と R_body、g の I_A entry と wrapper body、wrapper の I_V entry と captured-y Return を、同じ registry の original IF ports で接続する。F* の entry/return を pure body と同一視しない。

H は **actual f value tuple のみ**を、その元の compatible event/telescope で並べた declared hypothesis family とする。H に world、carrier、continuation、guard、g、wrapper の validity を入れない。元の positive clauses を使う相対数学構成 `B_H=νY.(Phi(Y) with V additionally containing H)` に対する background-lift の証明は、旧稿の二要素性を使わずそのまま成立する。H の要素ごとの replacement が必要な点は変わらない。ただし実 original background certificate を B_H の意味と同一視する対応は、固定 original domain ごとに必要である。

S を次の同時族と定義する。

1. 元の r_f と F* の全 compatible-event tuples。
2. actual source constructor が作った r_g(h)、r_w(h,k) とその complete descriptors、literal/record/result values。
3. actual source-prefix worlds、全 complete entry prefixes、全 pending/Return observations、未完了 suffix とその independently admitted developments。
4. 全 B_H の V/W/T/Car components。外部値、argument carrier、response とその future fields を省かない。

S は存在する raw source observations と元の全 domain 上の proof-indexed family であり、成功済み source trace だけへ challenge domain を狭めない。g の family tuple には A と同じ full checking proofを持ち、別々の f certificate を選ばない。

### postfixedness の constructive 部分

`S⊆Phi(S)` の各 case を次のように展開できる。

| case | 今回構成した証拠 | なお必要な固定 semantic input |
|---|---|---|
| f provider/capture | R1–R3 の actual r_f/self/succ と全 slot incidence | 元の Act identification、formation/profile/license guard、succ の full original relation |
| g capture | actual h の同じ r_f を ProofRef で参照。f tuple は S.V にある | 元の capture predicate と record の identification、g publication の full checking family |
| wrapper capture/Return | actual y/root、z を actual V Return 後に束縛し同じ y を返す | y の hereditary background と current world、元の Return/guard laws |
| entry Force | 元 I と Strict の実 receipt/Force/Return-rebind phase | 元 D の全 challengeに対する I-admission→ActualAdm、全 typed background embedding |
| recursive f call | q_fy は同じ r_f、A≤U の original whole-carrier check | complete domain/observation inclusion action（scalar inclusionだけではない） |
| pending request/resume | PendingAt が f、wrapper、g の未完了 suffix を順に保持 | 元の full response/future/authority clauses と current world transition law |
| world | actual registry/aliases、actual Return 後の bindings、同じ roots | 元の independent joint authority/license/profile fields |
| background | relative-coinduction の unfolding/monotonicity | 実 background 全域の B_H interpretation/embedding |

**補題 R4（証拠付き局所 assembly）。** 右列の actual original evidence が同じ tuples/telescopes で供給されれば、左二列は全 constructor case の postfixed derivation を与える。H は f case により discharge され、νPhi に f/g/wrapper/world を同時に入れる。

証明。R1 により captured f は S の同じ tuple、captured y は actual input の B_H tuple。Strict の phase 分解で zero/admin/Force-return/body/pending/final-return を全て扱う。q_fy の recursive membership occurrence は S.V に戻るが、independent guard は右列の証拠を使い、S から導かない。pending suffix は同じ actual request/response/world に Bind を順次適用する。world は同じ registry と全 binding の S 証拠を結合する。background は非 H case の unfolding と monotonicity、H は今構成した f caseで置換する。これで全部の S sorts が Phi(S) に入り coinduction を適用できる。□

R4 は新しい complete witness ではないが、前稿の J_rec 全体を未分解の前提にする定理ではない。有限 registry、source-owned closure/capture/alias/port incidences、exact pending plan、再帰的 value/world circularity は明示構成で消え、右列の **非再帰・固定 original inputs** にだけ残余を移した。guard/domain を弱めた演算子の安全性を証明したのではなく、固定 Phi の proof tree の未埋め leaf を列挙した。

有限深さごとの別 witness を一つに貼り合わせる compactness は使わない。S は最初から同じ scoped strategy を含む joint family とし、右列の証拠もその telescope に要求する。発散は一つの case を消す理由にならない。

### 4.1 選択済み native signature formation の適用

ここは generic な opaque formation 前提として残さない。直接の governing authority `notes/design/2026-10-08-native-signature-formation-definition.md` §§2–4 は、`source-signature-incidence-construction` §§2–6 の native `PortProv/DeclContribution/S/L/A` grammar と unannotated owning introduction の full-protection/no-concrete-removal policy を既に選択している。

R の各 typed port schema にこの構成を適用する。ℓf/ℓg/ℓw の Lambda は entry/body/capture/future の operand injection、各 Name は同じ registered root の Ref、q_fy と q_wrapper は別々の全 FrameCall、Bind は一つの actual result/current-world tuple、Record は元 field の ordered constructor image を保持する。再帰 Ref は preallocated port schema を指し、実行の無限展開を要求しない。従って **与えられた original typed port/local operator schemas に対し** 全 catalogue、PortProv、S-Declared と source/reference attachment の構造部分を実際に生成できる。二 Call の provenance partition は別 origin/receiver と全 inherited fields を保持する。

unannotated な f/g/wrapper の genuinely local introduction には選択済み full-protection/no-removal を適用する。受け継いだ f/argument/primitive の contribution へ新しい blanket policy を塗らない。この policy 自体の選択や generic native Lic/Attach grammar は未解決項ではない。

ただし DeclContribution の Op case は `typing_q` と `original_license_fields` を明示入力に持ち、Call の場合は actual independent complete C0/phase/world law を保持する。S-Declared は支持 schema を作るがその license witness の inhabitance を証明しない。本 source で **次に残る具体的な native leaf** は、active r_f を使う q_fy の complete local Call law と whole-carrier compatibility/admission action、およびそれを使う simultaneous hereditary background である。succ/literal/record も actual primitive/operator law を使い、存在しない foreign profile atom を足さない。

この適用で前表の「formation/profile/license」は三つに分かれる。(i) lexical/source-owned catalogue/provenance と native unannotated policy は上で構成、(ii) genuine native primitive/complete-operator evidence はその実 original local owner で残る、(iii) separately fixed foreign model へ同定する場合だけ foreign bridge が必要。本 packet の native witness に全 foreign model の guard を要求しない。

## 5. active-f capture の記録と Generalize の実適用

g の capture を、次の **deferred relation reference** として具体的に登録する。

`ActiveCapture(p_g(h), use_f, K_f, r_f, FullRelation(K_f), original_scope_map)`。

r_f の operational field は固定、FullRelation は original f の全未完了 constraints/guard obligations/descriptor dependencies を参照する。g を K_f の member に追加せず、f を completed external Mono と偽らず、証明後の discharge を約束するだけの certificate ともしない。この参照は source-owned data の定義であり、元の Generalize walk に新しい挙動を自動追加しない。

**補題 R5（同根・全依存 transport）。** capture の Name/alias restriction と g の二 actual use は、同じ r_f と同じ FullRelation を参照する。closure ごとの scope map を合成しても元の free fields と original binder dependencies は変わらない。

証明。R1 の resolve key を capture row に格納し、use は行の参照を共有する。FullRelation は root の既存 relation key であり frame ごとにコピーしない。scope map は lexical binder inclusion、composition は path concatenation なので同じ original free field を同定する。□

Generalize §5.1 をこの explicit data に適用するには、その未定義 field action を決定する bridge が残る。具体的には

`WalkActive(ActiveCapture(...), retain/fix) = original typed dependency traversal`

の証拠である。R5 が提供するのは traversal の対象 **全関係と元 scope** であり、どの field が Established/Shared/Description/EventProof かを勝手に選ばない。既存 fix edges が A を固定すればその mark を消さない。閉じた表示 F:U→V に A が見えないことと、full relation の自由 A がないことは異なる。

二 use への実適用として、Parameter の Desc_A、q_fy の full Call、wrapper の actual-y Return、g publication p_g(h)、new i_Int/i_Bool の原 scope と actual operands を一つの有限 proof schema に並べた。Int≤U と Bool≤U は structural injection の同じ値証明、f/root/world は共有、g の A-result correlation は wrapper により保持される。Generalize の SRC-J/GC を適用するため未埋めなのは、R4 右列と WalkActive によりこの schema が **独立 original joint derivation** になること。その前提を J_pub 自身で置き換えない。

従って今回の J_pub の残余は「active capture object が存在しない」ではなく、構成済み ActiveCapture row の **complete typed field classification/action** である。native shared C を C_i に変えず、この row から actual C の original interpretation への proof を要求する。資格 G/F と arbitrary C source binder の有無はこの結論に使わない。

## 6. 本当に opaque な入力が残る理由

選択済み native formation を §4.1 で適用した後、最初の具体的な未埋め leaf は **q_fy の actual active-root complete Call operator law/whole-carrier action** とその original background incidence である。native catalogue、Lic/Attach grammar、unannotated policy は既定かつ適用済みであり、追加の opaque foreign formation をこの native witness の前提にはしない。R1 の syntactic role/capture correctness も構成済みなので同じ registry を再調査する必要はない。

以下の independent-field discriminator は separately fixed opaque package への拡張の限界だけを示す。選択済み native grammar に任意の L を付け足す理由にはならず、native witness の阻害理由も §4.1 の実 operator leaf に限定する。frozen original-interface embedding §8 は `OriginalIndependentFields` を freely chosen property ではなく元の exhaustive inventory と明記し、その inventory と全 fixed-parameter laws は未供給としている。§9 の independent-field witness を今回の固定 tuple に適用すると、次の論理的境界が得られる。

全 raw graph/registry、selected hereditary sorts、challenge domain、Strict constructor と old pair/step の証拠を等しく保ち、未指定 CompleteMem field の profile atom L の値だけが新しい actual declaration incidence で違う二つの parameter interpretation を考える。R1–R5 のデータ事実と source prefix は等しいが、L を要求する完全 package の truth は異なる。従って supplied construction/旧限定定理だけから当該 L の真理は導けない。

これは二つの言語政策の提案でも、実際の fixed guard を変更する操作でもない。提供された premises の非含意を示す metatheoretic discriminator である。実際の原意味には一つの固定 L があり、その actual rule/evidence を必要とする。新しい source-owned registry を定義する権限は、この L を source registry 存在へ置換する権限ではない。R4 の全右列を true と定義することも行わない。

## 7. 親適用と次の owner packet

得られた meaningful delta は、元の J_rec/J_pub に必要な actual registry/capture/prefix operand を有限 source から構成し、旧 selected cases に戻る忘却を証明し、joint postfixed derivation の全 recursive dependency を同じ S に配線したことである。残余は operand 不在から **固定 original atoms の意味/証拠と、既に構成した active row の typed field action** に狭まった。

* **OM-LOCAL-CALL**: original complete Call/constructor owner は q_fy の `typing_q`、元 `original_license_fields`、active r_f/whole argument の complete C0/admission action をこの実 source tuple で構成する。選択済み native signature grammar の再定義は不要。source support から license inhabitance を推論すること、callee membership を前提と結論で循環使用することが falsifier。
* **OM-ADMISSION**: original contextual Function/Strict owner は I_A→I_U の full carrier action、D/ActualAdm、全 background future の元 interpretation を渡す。A≤U だけで arbitrary carrier/license を成立させたり、pending development を落とすことが falsifier。
* **OM-ACTIVE-WALK**: original Generalize/active capture owner は §5 の row の全 field を元の retained/fixed/event scopes に対応付ける。native C の sharing を変更したり hidden dependency を省略することが falsifier。

これらは新しい語で同じ registry inventory を要求する packet ではない。R1–R5 を input として、特定の semantic leaf/action を解決する packet である。全 inputs が揃えば R4 と SRC-J/GC に適用し、二 lawful g uses と native failure を同じ original witness で比較できる。現時点では完全 witness がないので intrusion required coverage の source-qualified 反例も成立しない。親は OPEN。

## 8. 依存、帰属、チェックと凍結

contract の20項目を actual bytes の SHA-256 と照合し全て一致した。primary が明示した linked governing authority とその selected proof も §4.1 のため直接読解した。厳密な manifest は冒頭の frozen contract/hash にあり、本稿はその20項目を再定義しない。直接数学依存の主要 hash:

| input | SHA-256 |
|---|---|
| `notes/design/2026-10-08-native-signature-formation-definition.md` | `e6c6cf995a3618172e45b4f8cdf4578313c057c6ec1e3e118c4dc11b6f162ab9` |
| `notes/theory/2026-10-08-source-signature-incidence-construction.md` | `7367ce8eb69376583386c6d675d067712ec6fa173e96f458ee34ce390dc8901a` |
| original recursive authority | `a9f833556a7e7c361c5b602c982de96b78663a77099999206bdb7bda6da67903` |
| contextual membership authority | `0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0` |
| captured closure authority | `6292b778e804988b32d48df663061d01e1593340ccb584fb6a8c0565bd817cfd` |
| simultaneous immutable root | `a5efa7056b12f931892548ecf3366d66156627ec44577c99d20ca48596438ae6` |
| original interface embedding | `29a643b5823a2732129c2e9a4924e3459648e315d9c916be9493e4218a2af680` |
| captured Call closure | `0f8adcf70a72d1f46bd4ca95f3984554d8cf2ff6af6434b679e991e346ffd50f` |
| Generalize | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| preceding original attempt | `4cfa7794b5f2e4e964511a1824a96309bb77a29a3ea5f75b9b0888cae4d9efbf` |
| primary candidate-core derivation | `18e971fef7a67bd2febea26ba399429e2bbbf795394b9430d6d02796d0b62b7e` |

旧 original attempt は本 worker、candidate-core 稿は primary。その他の依存作者・既存 review は各 frozen file の帰属を保持する。新構成の author は本 worker のみ、未独立査読。旧二 closure の actual premise と generic Strict composition を再利用し、未知 CompleteMem の exhaustive inventory、R35 provisional placement、candidate safety→original validity の飛躍は再利用しない。

三段階: finite declaration/capture construction、joint postfixed proof skeleton、Generalize/opaque boundary/parent application。上限190秒、全予約 charge。observed runtime UNKNOWN。静的読解、dependency hash、数学的 case inspection、artifact whitespace/fence inspection のみ。tests/build/compiler/network/Git、descendants はゼロ。新規/scratch path は本稿一つ、final message が唯一の handoff。

r1 を凍結、全書込み終了、worker STOPPED。次は Luna intake と fresh independent review、上記 exact leaf owners への適用。元の親と production は OPEN。
