# monomorphize type graph pipeline plan

作成日: 2026-05-23

## 背景

現在の principal monomorphize 系は、型の全代入、local type refresh、specialization
emit、既存 specialization への参照書き換え、cast 補正、hole default を同じ周辺で扱っている。
その結果、ある段階の暫定型が別段階の入力として再利用され、`unit` default や古い
specialization が後続の単一化を汚染する。

`ref '[fs] str` と `str.lines` / `line_view` のケースでは、`fold_lines` の effect row が
閉じきる前に既存 specialization の形へ引き寄せられ、さらに local の古い `unit` 注釈が
使用文脈として拾われることで、修正が局所分岐の連鎖になっている。

この文書は、infer より後、runtime VM より前の monomorphize / runtime type finalization を
再設計するための計画である。

## 目標

- 型を全代入・全単一化する pass と、矛盾処理、hole default、specialization を分ける。
- type inference / monomorphize の途中で path 文字列に基づく型決定をしない。
- original binding を fixpoint 中に破壊的 alias 化しない。
- `Expr.ty` に残る古い暫定型を、制約の根拠として無条件に採用しない。
- 後続の diagnostics に渡せる structured conflict を残す。

## 下界仮説

仮説:

> monomorphize が実行に必要な runtime type を閉じるとき、型変数・effect 変数・role
> associated slot の最終候補は、正規化された「下界 evidence」だけから決められる。
> 上界は候補生成には使わず、候補が許容範囲に入っているかを検査するためにだけ使う。

ここでいう下界は、型構文上の生の `lower` field そのものではない。関数引数、handler、
role receiver、effect row のように極性を持つ場所では、`type_graph` が occurrence を slot
の役割に沿って正規化し、次のどちらかへ分類した後の evidence を指す。

- observed lower: 実際に生成・渡され・返され・実行された runtime shape。
- required upper: その runtime shape が満たすべき期待型、許容 effect、role requirement。

また、この仮説で扱う「下界」は、実行時 shape を持つ inhabited evidence に限る。
`mzero` のように、任意の型へ入れる bottom / empty / impossible value だけを根拠にする例は
検証対象から除く。これらは「下界から型が決まるか」ではなく「型が決まっていない値を
期待文脈へ合わせられるか」の問題であり、候補生成ではなく expected-context check /
hole default / ambiguity diagnostic の責務に置く。

この仮説が正しければ、solver は次の構造にできる。

1. `type_graph` が equality / observed lower / required upper を分けて保存する。
2. `total_substitute` は observed lower の join と equality closure だけから各 slot の候補を作る。
3. required upper は候補決定後の audit で使い、失敗したものを `TypeGraphConflict` にする。
4. upper しか根拠がない slot は runtime type を合成せず、hole として残すか
   `UpperOnlyDependency` として記録する。
5. `insert_conflict_casts` は audit 後の conflict にだけ反応し、候補そのものを書き換えない。

重要なのは、上界を捨てることではない。上界を「型を作る根拠」から「型を検査する根拠」へ
移す。これにより、古い annotation、未閉鎖の scheme、expected edge、role requirement が
実行時の型 shape を勝手に合成する経路を断つ。

### 検証方法

導入中は solver に `LowerOnly` と `UpperAwareAudit` の二つの観測を持たせる。
既存 pipeline の挙動はすぐ変えず、preview / debug report で次を数える。

- lower evidence だけで closed runtime type まで決まった slot 数。
- equality closure 後にも lower evidence がない slot 数。
- upper を使わないと候補が作れない slot 数。
- lower 候補はあるが upper audit に失敗した conflict 数。
- lower 候補と既存 upper-aware projection の結果が違う slot 数。
- role associated / receiver / effect row で upper-only になった箇所。

下界仮説を「そのケースでは成立」とみなす条件:

- lower-only solution と既存 upper-aware projection が同じ closed module を作る。
- 差分がある場合、それが cast / diagnostic / hole default の責務へ移せる conflict として
  構造化されている。
- specialization request の key が upper-only projection に依存しない。
- 名前、module path、fixture 名を変えても同じ lower evidence から同じ候補が出る。

反証条件:

- 構文・宣言・symbol / role table から追加の observed lower edge を作れないのに、
  upper だけを使わないと実行に必要な concrete type が決まらない。
- upper-only projection が specialization key や VM 実行 shape を決めており、それを
  conflict / cast / hole default へ移すと意味が失われる。
- role associated type が receiver の observed lower から復元できず、requirement 側の
  upper だけが唯一の実行型根拠になる。

ただし、最初に upper-only が見つかっても即座に仮説棄却とはしない。`type_graph` が本来の
observed lower edge を落としているだけの可能性がある。反証とみなすのは、責務を正しく
分けた後でも structured lower evidence が存在しない場合だけである。

### 最初に疑う箇所

- 関数引数の反変位置。生の bounds ではなく、call edge の役割で evidence を正規化する。
- effect row。実行された effect は observed lower、許容 effect は required upper として扱う。
- `Never` / `Any`。空 lower と広すぎる upper は候補生成に使わず、hole / conflict 側へ送る。
- `mzero` / empty choice / unreachable branch。inhabited lower を持たないため、下界仮説の
  検証対象ではなく、期待文脈への適合または ambiguity として扱う。
- role impl / associated projection。receiver の実体から lower evidence を作り、requirement は
  impl 選択の検査に寄せる。
- 既存 `Expr.ty`。lower evidence として採用するには、その型がどの edge 由来かを持つ必要がある。

### crate 境界

`runtime2` のような新 crate を作るなら、名前は責務から決める。

候補:

- `yulang-runtime-ir`: runtime IR、runtime type、validation surface だけを持つ。
- `yulang-runtime-finalize`: monomorphize / type graph / cast insertion / hole default /
  specialization planning を持つ。
- `yulang-vm`: VM 実行、host bridge、control VM artifact を持つ。

現在の `yulang-runtime` は runtime IR と finalization をまだ同時に持っているため、
いきなり `yulang-runtime-finalize` を切ると依存が循環しやすい。次の分割は
`runtime IR` を先に薄い crate へ出し、その上に finalizer と VM を並べる形がよい。
今回の下界仮説検証は、後で `yulang-runtime-finalize` へ移せるように
`monomorphize/pipeline/type_graph.rs` を入口に集める。

2026-05-23 時点の初手として、`yulang-runtime-ir` を `publish = false` で追加し、
`Module` / `Binding` / `Expr` / `Pattern` / runtime `Type` を移した。既存利用側を
一度に壊さないため、`yulang-runtime::ir` と `yulang_runtime::Type` などの re-export は
互換入口として残す。

同日、`TypeGraph` の bounds evidence を target slot へ結びつけ、slot が
`lower_evidence` と `upper_requirements` を保持する形にした。これは lower-only solver が
下界 snapshot を明示的に受け取るための最小核であり、現段階では既存 pipeline の挙動を
変えず debug report にだけ出す。
続けて edge provenance を追加し、direct mismatch を equal / apply / let のどの由来で
見つけたかを report できるようにした。lower snapshot は複数下界が同じ slot に集まった
場合だけ conflict として数え、upper-only は bottom-like lower 除外と分けて扱う。
`total_substitute` preview は、lower evidence を union-find で equality / apply /
let-value-pattern edge へ伝播する lower-only solution を作る。現段階では module を
書き換えず、候補が入った slot と edge audit の件数だけを report する。
多相関数と role / 型クラスの検証用に、runtime slot とは別のレーンで type variable
lower evidence と role requirement bounds も集める。`ApplyEvidence` / principal
elaboration / runtime `TypeInstantiation` の substitutions は型変数への observed lower として扱い、
role requirement の input / associated bounds は lower candidate と upper requirement を
分けて観測する。これらは monomorphize 後には消費・消去されるため、debug preview は
pre-monomorphize と post-monomorphize の両方で出す。
型変数 lower evidence は `TypeVar` 名だけで束ねない。apply evidence / runtime
instantiation ごとの call-site scope を付け、`(scope, var)` を単位に解く。同じ多相関数を
複数回使ったときに、別 call の `a` が混ざって偽 conflict になるのを防ぐ。
scoped conflict は evidence source 別に分類する。`ApplyEvidence` の確定 substitution、
principal substitution candidate、principal elaboration、runtime instantiation が混ざった
conflict と、candidate 群だけの conflict を区別し、下界仮説の反証扱いにする前に
candidate 生成側の責務を確認する。
`int` と `float` のように既存の runtime compatibility で widening できる下界候補は、
偽 conflict にしない。slot の lower snapshot と type variable lower report は、候補を
追加する時点で `type_compatible` による join を行い、`1 + 2.3` のような mixed numeric
context は `float` へ寄せる。ここでも primitive 名の文字列分岐は持たず、互換性ルールを
唯一の根拠にする。
関連型については、role requirement の input lower が揃った場合だけ、`Module.role_impls`
の impl input と照合して associated type を射影する。射影した associated type は、requirement
側の associated bounds に含まれる型変数への lower evidence として追加する。input lower が
欠ける場合、該当 impl がない場合、または複数 impl が別候補を返す場合は、型を合成せず
preview report の resolution status に残す。
associated type を解いたときは、associated result だけでは足りない。impl input の照合で得た
structural substitution も lower evidence として同じ scope に入れる。例えば
`impl Index (lines 'e): type value = ref 'e str` では、`value = ref<t, str>` と同時に
`'e = t` も記録する。これにより、後続の再帰代入が `ref<t, str>` の内側を見られる。
ただし `t` 自体が concrete lower を持たない generic helper の文脈では、ここで無理に閉じない。
residual open として残し、concrete call site で閉じるべき変数と区別する。
型変数 lower は scope ごとの substitution map として畳む。`a = b`、`b = int` のような
連鎖は、同じ call-site scope 内で再帰的に `a = int` まで代入できるかを preview で数える。
cycle や未解決変数が残る場合は residual open として残し、別 scope の同名変数へは伝播しない。
この再帰代入は report 専用にしない。`close_type_substitution_map_recursively` を共通 helper
として置き、`TypeGraph::solve_type_var_lowers` は閉じた substitution map を solution として
保持する。runtime lowering の `TypeInstantiation` 生成でも同じ helper を通し、既に同一 call
site で得られている `a = b`、`b = int` のような lower は、instantiation metadata に出る前に
`a = int` へ materialize する。

role impl member の到達性は二段に分ける。specialization 中は role method から impl member へ
到達性を広げ、dispatch 候補を prune しない。VM に渡す最終 runtime module では、式/root から
直接届かない generic binding を削る。role dispatch metadata だけで generic impl member を
生かすと、`Display (list 'a)` や `Debug ('a, 'b)` のような generic impl が audit に残り、
実行責務と specialization 責務が混ざるためである。直接参照されている generic は削らず、
未解決多相として audit に落とす。

## 新しい責務境界

### 1. `type_graph`

runtime `Module` から、直接制約だけを集める。

候補 node:

- binding scheme slot
- expression value slot
- expression effect slot
- pattern slot
- apply callee / arg / result slot
- role associated slot
- constructor / variant payload slot

候補 edge:

- equality
- lower / upper bounds
- callable argument / result
- effect row inclusion
- declared scheme projection
- role associated projection

この段階では矛盾しても止めない。`TypeGraphConflict` として記録する。
推移 closure は保存しない。必要な伝播は solver 側の union-find / worklist が扱う。

### 2. `total_substitute`

`TypeGraph` を解き、既知情報を `Module` 全体へ一括反映する。

この pass の責務:

- node ごとに observed lower から最も閉じた型候補を選ぶ
- closed な value / effect を `Expr.ty`、binding scheme、pattern annotation へ代入する
- required upper の audit に失敗した矛盾は `TypeGraphConflict` として残す
- upper-only でしか候補が作れない slot は `UpperOnlyDependency` として残す

この pass でやらないこと:

- cast 挿入
- specialization emit
- `()` default
- path 文字列による意味復元

### 3. `insert_conflict_casts`

`TypeGraphConflict` を入力にして、説明可能な矛盾だけ semantic cast / `Coerce` に変換する。

条件:

- expected / actual が両方 closed
- 既存の cast / coercion ルールで説明できる
- cast を入れる位置が edge の由来から決まる

説明できない矛盾は structured diagnostic 用に残す。

### 4. `fill_type_holes`

最後まで残った穴を一箇所で埋める。

初期方針:

- value hole: `unit`
- closed empty effect hole: `Never`
- open effect row hole: 文脈付きで `Never` / `Any` を選ぶ

この pass 以外で `unit` default を作らない。

### 5. `specialize_closed_module`

全代入、cast、hole default 後の closed module から specialization request を作る。

方針:

- original binding は fixpoint 中に alias 化しない
- specialization key は `original + substitutions + input/output shape`
- single specialization alias は最後の cleanup のみ
- 旧 `principal_unify` の path 文字列分岐はここへ持ち込まない

## 段階的導入

### Milestone 1: skeleton

- `type_graph.rs`
- `total_substitute.rs`
- `conflict_casts.rs`
- `fill_holes.rs`

を追加する。

既存 pipeline の default behavior はまだ変えず、hidden / internal entrypoint で
`TypeGraph` を構築できる状態にする。

### Milestone 2: graph construction

最初は以下だけを graph 化する。

- binding scheme body
- expr runtime type
- apply evidence
- lambda param / body result
- block let pattern / value

この時点では solver は no-op に近くてよい。目的は「直接 edge を失わず集める」こと。
同時に、edge を equality / observed lower / required upper に分類し、debug report で
upper-only projection がどこから出たか追えるようにする。

### Milestone 3: total substitute

closed な equality edge だけを使って module へ一括反映する。
`ref '[fs] str` が `line_view` / `fold_lines` へ渡るときに、effect row が `Unknown` や
`unit` default に落ちないことを確認する。
その後、observed lower を使う solver に広げ、既存 upper-aware projection と closed
module / specialization request の差分を比較する。

### Milestone 4: conflict cast / fill holes

旧 `principal_unify` 内の cast 補正と `unit` default を新 pass へ移す。
この段階で、旧 pass 内の「矛盾したのでその場で式を書き換える」処理を削る。

### Milestone 5: specialization planning

specialization request を graph solution から作る。
fixpoint 中の original alias 化を廃止し、最後の cleanup だけに限定する。

## 今回の禁止事項

- monomorphize / type propagation の中で path 文字列を見て型を決めない。
- 特定の std helper 名、local 名、fixture 名だけを通す分岐を追加しない。
- `Expr.ty` の古い `unit` default を、直接制約より強い根拠として扱わない。
- original binding を、別 specialization が後から必要になる fixpoint 中に置き換えない。

## 最初に見るテスト

- `RUSTC_WRAPPER= cargo check -q -p yulang-runtime`
- `RUSTC_WRAPPER= cargo check -q -p yulang-vm`
- `RUSTC_WRAPPER= cargo test -q -p yulang-vm vm_runs_source_ref_string_lines_edit_example`
- `RUSTC_WRAPPER= cargo test -q -p yulang-vm vm_host_flushes_file_handle_string_edits`
