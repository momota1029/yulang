# dots T1b 結果 (2026-11-08)

**部分達成。T1b の受け入れ条件は未達。** 無条件の最終 `resolve_exact` と、
X13–X16 の外側入口での PROVED はまだない。今回の無条件の iff は、状態を返す
**1 回の再帰 pass** と独立判断 `Runs` の間の `run_exact` であり、最終解決の
完了を表す定理ではない。

## 対象・公開

- 取得した `integration/m1-final`: `4a9a6a16f30dcabaad4c75d19387b078123967ea`。
- 最終コード検証のローカル commit: `1c961b0e7`。
- 公開先は `work/dots-T1b` だけ。GitHub アプリのファイル単位 API を使用。
- 公開ファイル数: **12**（新 Lean 6、Yulang.lean/Audit.lean/README.md への追記3、設計1、質問1、本報告1）。
- spec、plan、lakefile、既存定理は変更していない。生成物は commit していない。
- 初回の11ファイル公開は開始から約28分、08:00:57 UTCまでに完了。その後root guard修正と本報告を公開。
- GitHub APIのcommitとローカルcommitは異なる。公開した内容はfetchしてtree比較する。

## 所要時間と公開照合

- 開始（clone起動）: 2026-11-08 07:32:44 UTC。
- 最終コード検証終了: 08:02:20 UTC。
- 報告を含む12ファイルを公開後、fetchして全tree一致を確認: 08:04:55 UTC、比較exit 0。
- ここまでの総所要時間: **32分11秒**。以後の変更はこの時刻記録の追記のみ。
- 照合した公開commit: `cf2def906200800fd6f6a8d4e199f1b8e6478d73`。
- この時点でworking treeはclean。最終コードと公開コードは一致。

## 受け入れとの対応

| 項目 | 結果 |
| --- | --- |
| 実 producer の child を二端点 Step に含め Acc を導く | **具体 structural producer について達成**。一般 narrowing-aware source producer の完全性ではない |
| 状態更新後に兄弟を再生成し、親を再計算する driver | **再帰 passとして達成**。各子に直前の子の戻りstateを渡し、全子後、全兄弟と親を最終stateで再生成する |
| FrontierExact・Accを外部仮定としないexactness | `frontier_exact` と `run_exact` を証明。ただし後者の対象は1回のpass。最終source resolverではない |
| 開いた区間の断片で最終 resolve_exact | **未達** |
| X13–X16の少なくとも一つが外側入口でPROVED | **未達**。表の状態を更新していない |
| 全体verify | **PASS、exit 0、1131 jobs** |

## 前回との差分

前回T1のstate accumulatorは、更新列を呼び出し側が事前に渡すものだった。
今回は `update` が実際に選ばれた宣言と、両端から取得したpayloadからcapture列を
生成する。`prepare` は既存の実制約生成器を呼び、旧stateの全atomを保持する。
`produce` は既存ordinary solverを呼び、そのstateにmodelがあるかを調べる。

`CommonRoleOpenRecursivePass.run` は実producerのchild関係に対して導いたAccで
再帰する。各子の再帰実行が返したstateを次の子に渡し、全子が返った時点のstateで
全兄弟と親を再度produceする。最終stateでの観測はtraceに残り、初期観測と同一だと
仮定していない。外部fuel・role rank・成功証明・FrontierExact・Accは入力しない。

しかし、これはsource worklistの飽和ではない。再計算で新しく有効になった子を
さらに展開するfixed-pointループ、その停止性、最終辞書のadequacyは残っている。

## モデルの正確な境界（重要）

1. `CommonRoleOpenProducer` は両端への独立 `Inspect` のstructural phaseである。
   rootのlowerがunknownならpending、regular rootならrejectedを先に行う。
   各宣言について両端がhitする場合にpayload対を返す。この両端照合は、候補が
   上界を絞ることで適合する一般の区間候補を網羅していない。
2. 宣言は既存unary head/template構文とその実checkを使う。Registryは全宣言の
   check=trueとkey重複なしを含む。端点の等しさは仮定しない。有限spineの深さ制限なし。
3. `Allocation n := Ty → Fin n` は**明示的な外部境界入力**である。実selected payload
   と生成するslotの対応は証明したが、そのmapが元のsource/graph/nominal意味を
   保存するallocatorであることは未証明。Commonのordinary stateとsource Tyの橋を
   閉じたとは言わない。
4. `produce` はstructural選択後のstate整合性を検査する段階で、各候補のordinary
   絞り込みを候補数の集計前に行う一般source frontierではない。これもcompletionを
   阻む残件で、独立Localとのiffだけではこのsource完全性は得られない。
5. `run_exact` は本当に無条件の「実行版と独立Runsのiff」だが、Runs自体が記述するのは
   この1回の再帰pass。中間pending/ambiguousをいつ最終結果にするかは決めていない。
   `notes/questions/2026-11-08-T1b-sibling-recollection.md` に遅延案を先頭として質問を残した。
6. 固定された更新列の並べ替えはmodelを変えないと証明したが、状態依存producerが
   どの順でも同じ更新列を作ることは証明していない。

## 追加定理の日本語の主張

以下の各項目の量化子・前提の完全なLean型は末尾の46定理一覧にある。
`State n` はn個のCommon value/row slot上の実ordinary atom列と既存solver grammar証明。
`Request` はrole・元のlower・元のupperを持つ。端点同一性のフィールドはない。

### CommonRoleOpenProducer

- `trial_exact`: 任意のrole、2端点、宣言、候補観測について、実trialの等号と、role一致・独立Inspectに基づくTrialRuleが同値。
- `scan_sound` / `scan_complete` / `scan_exact`: 任意の宣言列と端点で、実scanと独立Scanの結果が一致し、任意の候補結果列についてiff。
- `summarize_sound` / `summarize_complete`: 任意のRequestとTrial列について、K2/pending/空/単一/複数の独立Decisionとsummarizeの結果が一致。
- `frontier_sound` / `frontier_complete` / `frontier_exact`: 任意の宣言列・Request・Frontierについて、実frontierの等号 iff 独立Local。root未知/regularの規則を含む。全source候補の完全性を前提にも結論にもしていない。

### CommonRoleOpenProducerAccess

- `trial_hit_origin` / `scan_hit_origin`: 任意の実trial/scanでhitが返れば、その宣言の所属・role一致・元の両端へのInspect導出を回収できる。
- `mem_hits`: 任意のTrial列・宣言・payload対で、hitsの要素であること iff 元列のhitであること。
- `selected_origin` / `selected_production`: 任意の独立Local selected導出から、実宣言・両payload・宣言key・実requirementsからの全child列を回収できる。
- `child_step`: 任意の宣言列・親子とChild Local導出について、その子は前回T1の独立OpenDescent.Stepに含まれる。
- `child_decreases`: 任意のchecked Registry・親子と実Child Local導出について、子の両端サイズ和は親より小さい。
- `accessible`: 任意のchecked Registry・RequestについてAcc Child Local。別途のrank・fuel・成功仮定なし。

### CommonRoleOpenThreading

- `thread_exact`: 任意のchild実行関数と独立Step、および両者のiffという**明示的な仮定**の下で、任意のchild列・入出力state・出力列に対してthreadと独立Threadがiff。このgeneric補題はsource theoremではない。
- `refresh_exact`: 任意のproduce関数と独立Produceのiffを仮定し、任意の子列・同一state・観測列についてmapとAll₂ Produceがiff。
- `drive_exact`: 任意のchildren/produce/runと、それぞれの独立判断との3つの明示的iffを仮定し、任意のparent/state/traceでdriveとDrivenがiff。具体化のpass_exactでその仮定を実際に証明する。
- `thread_preserves`: 任意のStepがmodelを保存するという仮定とThread導出、任意の共通assignmentが最終stateを満たす場合、最初のstateも満たす。
- `recollect_models_permutation`: 任意のstate・同じbindings列の置換2つ・assignmentで、それぞれのT1 accumulator最終modelがiff。

### CommonRoleOpenPropagation

- `prepare_exact`: 任意の宣言列・allocation・request・state・assignmentに対し、生成後stateの充足 iff 元stateの充足と実update bindingsのCompatible。
- `consistent_exact`: 任意のstateで、実solverのfamilyが非空 iff そのstateにmodelがある。
- `produce_exact`: 任意の宣言列・allocation・request・state・frontierで、実state-gated produceと独立Producedがiff。
- `produced_child_step` / `produced_child_decreases`: 任意のstate-gated selected導出とchild所属証明から、前回Stepへの包含と、checked Registryでは厳密下降。
- `children_exact`: 任意の宣言列・allocation・request・state・child列で、実抽出と独立Childrenがiff。
- `advance_exact`: 同じ任意の入力と候補観測・次stateに対し、実capture更新を行うadvanceと独立Advanceがiff。
- `pass_exact`: 任意の宣言列・allocation・request・state・traceに対し、1段階の実兄弟passと具体Drivenがiff。genericの3つの橋は追加仮定でなく上記定理で証明済み。
- `advance_preserves` / `pass_preserves`: 任意の共通assignmentが実advance/passの最終stateを満たすなら元stateも満たす。

### CommonRoleOpenPropagationOrigin

- `capture_bounds` / `capture_present`: 任意のallocation・宣言・両payload・名前について、実captureのboundsに現れる対は元payloadの割当slot対であり、headにその名前があればその対が現れる。
- `capture_exact`: 任意のallocation・宣言・両payload・assignmentで、captureのCompatible iff headの名前列が空、またはlower slotの型<:upper slotの型。
- `selected_update_origin`: 任意のLocal selected導出とallocationで、実productionが返した宣言・payload対を用いたcaptureとupdateが等しい。
- `selected_prepare_exact`: 同じ任意の入力で、実production由来の宣言・payload対が存在し、すべてのassignmentについて、生成後state iff 元stateかつそのpayload対の部分型制約（名前なし例外）。

### CommonRoleOpenRecursivePass

- `child_origin`: 任意のstate-dependent produceの実childはstructural LocalのChildでもある。
- `runAcc_unfold`: 任意のRegistry/allocation/request/そのAcc/stateで、内部再帰版は具体的なprepare→child thread→final-state再生成に展開できる。
- `runAcc_eq_run`: 任意のそのAcc証明で実行結果はpublic runと同じ。証明の選び方を計算に混ぜない。
- `thread_attach`: 任意の実行関数・子列・stateについて、所属証明をattachしてからのthreadと通常のthreadは同じ。
- `run_unfold`: 任意のRegistry/allocation/request/stateで、public runの再帰方程式。全childも同じpublic runを呼ぶ。
- `run_exact`: 任意のchecked Registry、自然数n、Allocation n、Request、開始State n、任意のTraceと最終State nについて、runがその対を返す iff 独立Runs導出。外部FrontierExact・Acc・fuel・成功の仮定はない。
- `runs_preserves` / `run_preserves`: 任意の共通assignmentが、独立Runsまたは実runの最終stateを満たすなら元stateも満たす。
- `run_recollects`: 任意のRegistry/allocation/request/入出力state/trace構成要素について、runがそのnodeを返した等号を前提に、最終親と全兄弟のProducedが**同じ最終state**で成立。旧観測との一致や飽和は結論にしない。

## コマンドと結果

- `git clone --branch integration/m1-final --single-branch https://github.com/momota1029/yulang.git yulang-dots-T1b`: 成功。
- Leanは既存のelan管理 `leanprover/lean4:v4.35.0` を再利用。
- baseline `bash tools/verify-lean.sh . origin/integration/m1-final`: PASS、1125 jobs、公理81677。
- 各新モジュールを `lake build Yulang.<module> --wfail`: 最終すべて成功。
- 最終 `bash tools/verify-lean.sh . origin/integration/m1-final`: **exit 0、43秒（差分ビルド）**。
  開始08:01:37 UTC、終了08:02:20 UTC。
- `lake env lean --trust=0 ../../dots-T1b-logs/types.lean`: 公開46定理の型取得、exit 0。

最終verify出力全文:

```text
verify-lean: . @ 1c961b0e7 (base origin/integration/m1-final)
ok: lake build --wfail (Build completed successfully (1131 jobs).)
ok: Audit.lean exit 0
ok: axioms only propext/Classical.choice/Quot.sound over 6072 printed declarations
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended
ok: AXIOM-GATE-PASS: 82004 declarations
verify-lean: PASS
```

## 中断・失敗・制限

- baseline実行中にfocused buildを誤って並行実行し、focused側の既存ProducerContextualRegularの`.olean`にmissingエラーが出た。baseline自体はPASS。以後のfocused再実行と最終全体検証は成功。既存ソースを変更して回避していない。
- 新しい証明の作成中に型・tacticエラーを修正した。型一覧の取得時は未対応オプション`pp.width`を使ってexit1となり、そのオプションを除いた再実行はexit0。
- 環境再作成・時間切れ・セッション消失なし。使用量の計上先・消費量は不明。
- source saturationの最終判定方針は選ばず質問へ。未達をdoneと表示していない。

## 次の正確な残件

1. narrowingを扱うcandidateごとのstate更新と、その後に集計するsource frontier。
2. Ty端点・nominal意味・slot/source identityを保存する実allocatorとcapture provenance。
3. 再生成で現れたchildをさらに解くsource saturation、その進捗/停止性、order independenceまたは承認済みfinalization規則。
4. そのdriverの最終結果と独立source Classifyのiff、外側resolve_exact、X13–X16の本物の適合例。

## 全46公開定理の実際の型

以下は `#check @<完全修飾名>` の実出力。隠れたimplicit量化も@で表示した。

```lean
Yulang.CommonRoleOpenProducer.trial_exact : ∀ (role : Nat) (lo hi : Yulang.CommonRoleSettledSyntax.Ty)
  (d : Yulang.CommonRoleSettledSyntax.Declaration) (out : Option Yulang.CommonRoleOpenProducer.Trial),
  Yulang.CommonRoleOpenProducer.trial role lo hi d = out ↔ Yulang.CommonRoleOpenProducer.TrialRule role lo hi d out
Yulang.CommonRoleOpenProducer.scan_sound : ∀ (role : Nat) (lo hi : Yulang.CommonRoleSettledSyntax.Ty)
  (ds : List Yulang.CommonRoleSettledSyntax.Declaration),
  Yulang.CommonRoleOpenProducer.Scan role lo hi ds (Yulang.CommonRoleOpenProducer.scan role lo hi ds)
@Yulang.CommonRoleOpenProducer.scan_complete : ∀ {role : Nat} {lo hi : Yulang.CommonRoleSettledSyntax.Ty}
  {ds : List Yulang.CommonRoleSettledSyntax.Declaration} {results : List Yulang.CommonRoleOpenProducer.Trial},
  Yulang.CommonRoleOpenProducer.Scan role lo hi ds results → Yulang.CommonRoleOpenProducer.scan role lo hi ds = results
Yulang.CommonRoleOpenProducer.scan_exact : ∀ (role : Nat) (lo hi : Yulang.CommonRoleSettledSyntax.Ty)
  (ds : List Yulang.CommonRoleSettledSyntax.Declaration) (results : List Yulang.CommonRoleOpenProducer.Trial),
  Yulang.CommonRoleOpenProducer.scan role lo hi ds = results ↔ Yulang.CommonRoleOpenProducer.Scan role lo hi ds results
Yulang.CommonRoleOpenProducer.summarize_sound : ∀ (q : Yulang.CommonRoleOpenProducer.Request)
  (results : List Yulang.CommonRoleOpenProducer.Trial),
  Yulang.CommonRoleOpenProducer.Decision q results (Yulang.CommonRoleOpenProducer.summarize q results)
@Yulang.CommonRoleOpenProducer.summarize_complete : ∀ {q : Yulang.CommonRoleOpenProducer.Request}
  {results : List Yulang.CommonRoleOpenProducer.Trial}
  {result : Yulang.CommonRoleOutermostResolver.Frontier Yulang.CommonRoleOpenProducer.Request},
  Yulang.CommonRoleOpenProducer.Decision q results result → Yulang.CommonRoleOpenProducer.summarize q results = result
Yulang.CommonRoleOpenProducer.frontier_sound : ∀ (visible : List Yulang.CommonRoleSettledSyntax.Declaration)
  (q : Yulang.CommonRoleOpenProducer.Request),
  Yulang.CommonRoleOpenProducer.Local visible q (Yulang.CommonRoleOpenProducer.frontier visible q)
@Yulang.CommonRoleOpenProducer.frontier_complete : ∀ {visible : List Yulang.CommonRoleSettledSyntax.Declaration}
  {q : Yulang.CommonRoleOpenProducer.Request}
  {result : Yulang.CommonRoleOutermostResolver.Frontier Yulang.CommonRoleOpenProducer.Request},
  Yulang.CommonRoleOpenProducer.Local visible q result → Yulang.CommonRoleOpenProducer.frontier visible q = result
Yulang.CommonRoleOpenProducer.frontier_exact : ∀ (visible : List Yulang.CommonRoleSettledSyntax.Declaration),
  Yulang.CommonRoleOutermostResolver.FrontierExact (Yulang.CommonRoleOpenProducer.protocol visible)
Yulang.CommonRoleOpenProducerAccess.trial_hit_origin : ∀ (role : Nat) (lo hi : Yulang.CommonRoleSettledSyntax.Ty)
  (source d : Yulang.CommonRoleSettledSyntax.Declaration) (lowPayload highPayload : Yulang.CommonRoleSettledSyntax.Ty),
  Yulang.CommonRoleOpenProducer.trial role lo hi source =
      some (Yulang.CommonRoleOpenProducer.Trial.hit d lowPayload highPayload) →
    source = d ∧
      source.role = role ∧
        Yulang.CommonRoleSettledSyntax.Inspect d.head lo (Yulang.CommonRoleSettledSyntax.Observation.hit lowPayload) ∧
          Yulang.CommonRoleSettledSyntax.Inspect d.head hi (Yulang.CommonRoleSettledSyntax.Observation.hit highPayload)
Yulang.CommonRoleOpenProducerAccess.scan_hit_origin : ∀ (role : Nat) (lo hi : Yulang.CommonRoleSettledSyntax.Ty)
  (visible : List Yulang.CommonRoleSettledSyntax.Declaration) (d : Yulang.CommonRoleSettledSyntax.Declaration)
  (lp hp : Yulang.CommonRoleSettledSyntax.Ty),
  Yulang.CommonRoleOpenProducer.Trial.hit d lp hp ∈ Yulang.CommonRoleOpenProducer.scan role lo hi visible →
    d ∈ visible ∧
      d.role = role ∧
        Yulang.CommonRoleSettledSyntax.Inspect d.head lo (Yulang.CommonRoleSettledSyntax.Observation.hit lp) ∧
          Yulang.CommonRoleSettledSyntax.Inspect d.head hi (Yulang.CommonRoleSettledSyntax.Observation.hit hp)
Yulang.CommonRoleOpenProducerAccess.mem_hits : ∀ (results : List Yulang.CommonRoleOpenProducer.Trial)
  (d : Yulang.CommonRoleSettledSyntax.Declaration) (lp hp : Yulang.CommonRoleSettledSyntax.Ty),
  (d, lp, hp) ∈ Yulang.CommonRoleOpenProducer.hits results ↔ Yulang.CommonRoleOpenProducer.Trial.hit d lp hp ∈ results
Yulang.CommonRoleOpenProducerAccess.selected_origin : ∀ (visible : List Yulang.CommonRoleSettledSyntax.Declaration)
  (q : Yulang.CommonRoleOpenProducer.Request) (key : Nat) (cs : List Yulang.CommonRoleOpenProducer.Request),
  Yulang.CommonRoleOpenProducer.Local visible q (Yulang.CommonRoleOutermostResolver.Frontier.selected key cs) →
    ∃ d lp hp,
      d ∈ visible ∧
        d.role = q.role ∧
          Yulang.CommonRoleSettledSyntax.Inspect d.head q.lower (Yulang.CommonRoleSettledSyntax.Observation.hit lp) ∧
            Yulang.CommonRoleSettledSyntax.Inspect d.head q.upper (Yulang.CommonRoleSettledSyntax.Observation.hit hp) ∧
              key = d.key ∧ cs = Yulang.CommonRoleOpenProducer.children q d lp hp
Yulang.CommonRoleOpenProducerAccess.selected_production : ∀ (visible : List Yulang.CommonRoleSettledSyntax.Declaration)
  (q : Yulang.CommonRoleOpenProducer.Request) (key : Nat) (cs : List Yulang.CommonRoleOpenProducer.Request),
  Yulang.CommonRoleOpenProducer.Local visible q (Yulang.CommonRoleOutermostResolver.Frontier.selected key cs) →
    ∃ d lp hp,
      Yulang.CommonRoleOpenProducer.production visible q = some (d, lp, hp) ∧
        key = d.key ∧ cs = Yulang.CommonRoleOpenProducer.children q d lp hp
Yulang.CommonRoleOpenProducerAccess.child_step : ∀ (visible : List Yulang.CommonRoleSettledSyntax.Declaration)
  (q child : Yulang.CommonRoleOpenProducer.Request),
  Yulang.CommonRoleOutermostResolver.Child (Yulang.CommonRoleOpenProducer.Local visible) child q →
    Yulang.CommonRoleOpenDescent.Step visible child q
Yulang.CommonRoleOpenProducerAccess.child_decreases : ∀ (registry : Yulang.CommonRoleOpenProducer.Registry)
  (q child : Yulang.CommonRoleOpenProducer.Request),
  Yulang.CommonRoleOutermostResolver.Child (Yulang.CommonRoleOpenProducer.Local registry.declarations) child q →
    Yulang.CommonRoleOpenDescent.weight child < Yulang.CommonRoleOpenDescent.weight q
Yulang.CommonRoleOpenProducerAccess.accessible : ∀ (registry : Yulang.CommonRoleOpenProducer.Registry)
  (q : Yulang.CommonRoleOpenProducer.Request),
  Acc (Yulang.CommonRoleOutermostResolver.Child (Yulang.CommonRoleOpenProducer.Local registry.declarations)) q
@Yulang.CommonRoleOpenThreading.thread_exact : ∀ {α : Type u_1} {n : Nat} {β : Type u_2}
  (run : α → Yulang.CommonRoleSettledConstraints.State n → β × Yulang.CommonRoleSettledConstraints.State n)
  (Step : α → Yulang.CommonRoleSettledConstraints.State n → β → Yulang.CommonRoleSettledConstraints.State n → Prop),
  (∀ (child : α) (s : Yulang.CommonRoleSettledConstraints.State n) (result : β)
      (next : Yulang.CommonRoleSettledConstraints.State n), run child s = (result, next) ↔ Step child s result next) →
    ∀ (children : List α) (s : Yulang.CommonRoleSettledConstraints.State n) (results : List β)
      (final : Yulang.CommonRoleSettledConstraints.State n),
      Yulang.CommonRoleOpenThreading.thread run children s = (results, final) ↔
        Yulang.CommonRoleOpenThreading.Thread Step children s results final
@Yulang.CommonRoleOpenThreading.refresh_exact : ∀ {α : Type u_1} {n : Nat} {γ : Type u_2}
  (produce : α → Yulang.CommonRoleSettledConstraints.State n → γ)
  (Produce : α → Yulang.CommonRoleSettledConstraints.State n → γ → Prop),
  (∀ (child : α) (s : Yulang.CommonRoleSettledConstraints.State n) (result : γ),
      produce child s = result ↔ Produce child s result) →
    ∀ (children : List α) (s : Yulang.CommonRoleSettledConstraints.State n) (observations : List γ),
      List.map (fun child => produce child s) children = observations ↔
        Yulang.CommonRoleOutermostResolver.All₂ (fun child observation => Produce child s observation) children
          observations
@Yulang.CommonRoleOpenThreading.drive_exact : ∀ {α : Type} {n : Nat} {γ β : Type}
  (children : α → Yulang.CommonRoleSettledConstraints.State n → List α)
  (produce : α → Yulang.CommonRoleSettledConstraints.State n → γ)
  (run : α → Yulang.CommonRoleSettledConstraints.State n → β × Yulang.CommonRoleSettledConstraints.State n)
  (Children : α → Yulang.CommonRoleSettledConstraints.State n → List α → Prop)
  (Produce : α → Yulang.CommonRoleSettledConstraints.State n → γ → Prop)
  (Step : α → Yulang.CommonRoleSettledConstraints.State n → β → Yulang.CommonRoleSettledConstraints.State n → Prop),
  (∀ (parent : α) (s : Yulang.CommonRoleSettledConstraints.State n) (cs : List α),
      children parent s = cs ↔ Children parent s cs) →
    (∀ (child : α) (s : Yulang.CommonRoleSettledConstraints.State n) (result : γ),
        produce child s = result ↔ Produce child s result) →
      (∀ (child : α) (s : Yulang.CommonRoleSettledConstraints.State n) (result : β)
          (next : Yulang.CommonRoleSettledConstraints.State n),
          run child s = (result, next) ↔ Step child s result next) →
        ∀ (parent : α) (s : Yulang.CommonRoleSettledConstraints.State n)
          (trace : Yulang.CommonRoleOpenThreading.Trace α β γ n),
          Yulang.CommonRoleOpenThreading.drive children produce run parent s = trace ↔
            Yulang.CommonRoleOpenThreading.Driven Children Produce Step parent s trace
@Yulang.CommonRoleOpenThreading.thread_preserves : ∀ {α : Type u_1} {n : Nat} {β : Type u_2} {children : List α}
  {s : Yulang.CommonRoleSettledConstraints.State n} {results : List β}
  {final : Yulang.CommonRoleSettledConstraints.State n}
  (Step : α → Yulang.CommonRoleSettledConstraints.State n → β → Yulang.CommonRoleSettledConstraints.State n → Prop),
  (∀ (child : α) (s : Yulang.CommonRoleSettledConstraints.State n) (result : β)
      (next : Yulang.CommonRoleSettledConstraints.State n),
      Step child s result next →
        ∀ (assignment : Fin n → Yulang.Core.PresenceGeneration.Comp Yulang.Common.model),
          Yulang.PresenceNormalForm.All Yulang.Common.model assignment next.atoms →
            Yulang.PresenceNormalForm.All Yulang.Common.model assignment s.atoms) →
    Yulang.CommonRoleOpenThreading.Thread Step children s results final →
      ∀ (assignment : Fin n → Yulang.Core.PresenceGeneration.Comp Yulang.Common.model),
        Yulang.PresenceNormalForm.All Yulang.Common.model assignment final.atoms →
          Yulang.PresenceNormalForm.All Yulang.Common.model assignment s.atoms
@Yulang.CommonRoleOpenThreading.recollect_models_permutation : ∀ {n : Nat}
  (s : Yulang.CommonRoleSettledConstraints.State n)
  (first last : List (Yulang.CommonRoleCandidateConstraints.Bindings n)),
  first.Perm last →
    ∀ (assignment : Fin n → Yulang.Core.PresenceGeneration.Comp Yulang.Common.model),
      Yulang.PresenceNormalForm.All Yulang.Common.model assignment
          (Yulang.CommonRoleOpenState.recollect s first).atoms ↔
        Yulang.PresenceNormalForm.All Yulang.Common.model assignment (Yulang.CommonRoleOpenState.recollect s last).atoms
@Yulang.CommonRoleOpenPropagation.prepare_exact : ∀ {n : Nat}
  (visible : List Yulang.CommonRoleSettledSyntax.Declaration) (allocate : Yulang.CommonRoleOpenPropagation.Allocation n)
  (q : Yulang.CommonRoleOpenProducer.Request) (s : Yulang.CommonRoleSettledConstraints.State n)
  (assignment : Fin n → Yulang.Core.PresenceGeneration.Comp Yulang.Common.model),
  Yulang.PresenceNormalForm.All Yulang.Common.model assignment
      (Yulang.CommonRoleOpenPropagation.prepare visible allocate q s).atoms ↔
    Yulang.PresenceNormalForm.All Yulang.Common.model assignment s.atoms ∧
      Yulang.CommonRoleCandidateConstraints.Compatible (Yulang.CommonRoleOpenPropagation.update visible allocate q)
        assignment
@Yulang.CommonRoleOpenPropagation.consistent_exact : ∀ {n : Nat} (s : Yulang.CommonRoleSettledConstraints.State n),
  Yulang.CommonRoleOpenPropagation.consistent s = true ↔ s.Models
@Yulang.CommonRoleOpenPropagation.produce_exact : ∀ {n : Nat}
  (visible : List Yulang.CommonRoleSettledSyntax.Declaration) (allocate : Yulang.CommonRoleOpenPropagation.Allocation n)
  (q : Yulang.CommonRoleOpenProducer.Request) (s : Yulang.CommonRoleSettledConstraints.State n)
  (f : Yulang.CommonRoleOutermostResolver.Frontier Yulang.CommonRoleOpenProducer.Request),
  Yulang.CommonRoleOpenPropagation.produce visible allocate q s = f ↔
    Yulang.CommonRoleOpenPropagation.Produced visible allocate q s f
@Yulang.CommonRoleOpenPropagation.produced_child_step : ∀ {n : Nat}
  (visible : List Yulang.CommonRoleSettledSyntax.Declaration) (allocate : Yulang.CommonRoleOpenPropagation.Allocation n)
  (q child : Yulang.CommonRoleOpenProducer.Request) (s : Yulang.CommonRoleSettledConstraints.State n) (key : Nat)
  (cs : List Yulang.CommonRoleOpenProducer.Request),
  Yulang.CommonRoleOpenPropagation.Produced visible allocate q s
      (Yulang.CommonRoleOutermostResolver.Frontier.selected key cs) →
    child ∈ cs → Yulang.CommonRoleOpenDescent.Step visible child q
@Yulang.CommonRoleOpenPropagation.produced_child_decreases : ∀ {n : Nat}
  (registry : Yulang.CommonRoleOpenProducer.Registry) (allocate : Yulang.CommonRoleOpenPropagation.Allocation n)
  (q child : Yulang.CommonRoleOpenProducer.Request) (s : Yulang.CommonRoleSettledConstraints.State n) (key : Nat)
  (cs : List Yulang.CommonRoleOpenProducer.Request),
  Yulang.CommonRoleOpenPropagation.Produced registry.declarations allocate q s
      (Yulang.CommonRoleOutermostResolver.Frontier.selected key cs) →
    child ∈ cs → Yulang.CommonRoleOpenDescent.weight child < Yulang.CommonRoleOpenDescent.weight q
@Yulang.CommonRoleOpenPropagation.children_exact : ∀ {n : Nat}
  (visible : List Yulang.CommonRoleSettledSyntax.Declaration) (allocate : Yulang.CommonRoleOpenPropagation.Allocation n)
  (q : Yulang.CommonRoleOpenProducer.Request) (s : Yulang.CommonRoleSettledConstraints.State n)
  (cs : List Yulang.CommonRoleOpenProducer.Request),
  Yulang.CommonRoleOpenPropagation.children visible allocate q s = cs ↔
    Yulang.CommonRoleOpenPropagation.Children visible allocate q s cs
@Yulang.CommonRoleOpenPropagation.advance_exact : ∀ {n : Nat}
  (visible : List Yulang.CommonRoleSettledSyntax.Declaration) (allocate : Yulang.CommonRoleOpenPropagation.Allocation n)
  (q : Yulang.CommonRoleOpenProducer.Request) (s : Yulang.CommonRoleSettledConstraints.State n)
  (f : Yulang.CommonRoleOutermostResolver.Frontier Yulang.CommonRoleOpenProducer.Request)
  (next : Yulang.CommonRoleSettledConstraints.State n),
  Yulang.CommonRoleOpenPropagation.advance visible allocate q s = (f, next) ↔
    Yulang.CommonRoleOpenPropagation.Advance visible allocate q s f next
@Yulang.CommonRoleOpenPropagation.pass_exact : ∀ {n : Nat} (visible : List Yulang.CommonRoleSettledSyntax.Declaration)
  (allocate : Yulang.CommonRoleOpenPropagation.Allocation n) (q : Yulang.CommonRoleOpenProducer.Request)
  (s : Yulang.CommonRoleSettledConstraints.State n)
  (trace :
    Yulang.CommonRoleOpenThreading.Trace Yulang.CommonRoleOpenProducer.Request
      (Yulang.CommonRoleOutermostResolver.Frontier Yulang.CommonRoleOpenProducer.Request)
      (Yulang.CommonRoleOutermostResolver.Frontier Yulang.CommonRoleOpenProducer.Request) n),
  Yulang.CommonRoleOpenPropagation.pass visible allocate q s = trace ↔
    Yulang.CommonRoleOpenThreading.Driven (Yulang.CommonRoleOpenPropagation.Children visible allocate)
      (Yulang.CommonRoleOpenPropagation.Produced visible allocate)
      (Yulang.CommonRoleOpenPropagation.Advance visible allocate) q
      (Yulang.CommonRoleOpenPropagation.prepare visible allocate q s) trace
@Yulang.CommonRoleOpenPropagation.advance_preserves : ∀ {n : Nat}
  (visible : List Yulang.CommonRoleSettledSyntax.Declaration) (allocate : Yulang.CommonRoleOpenPropagation.Allocation n)
  (q : Yulang.CommonRoleOpenProducer.Request) (s next : Yulang.CommonRoleSettledConstraints.State n)
  (f : Yulang.CommonRoleOutermostResolver.Frontier Yulang.CommonRoleOpenProducer.Request),
  Yulang.CommonRoleOpenPropagation.Advance visible allocate q s f next →
    ∀ (assignment : Fin n → Yulang.Core.PresenceGeneration.Comp Yulang.Common.model),
      Yulang.PresenceNormalForm.All Yulang.Common.model assignment next.atoms →
        Yulang.PresenceNormalForm.All Yulang.Common.model assignment s.atoms
@Yulang.CommonRoleOpenPropagation.pass_preserves : ∀ {n : Nat}
  (visible : List Yulang.CommonRoleSettledSyntax.Declaration) (allocate : Yulang.CommonRoleOpenPropagation.Allocation n)
  (q : Yulang.CommonRoleOpenProducer.Request) (s : Yulang.CommonRoleSettledConstraints.State n)
  (assignment : Fin n → Yulang.Core.PresenceGeneration.Comp Yulang.Common.model),
  Yulang.PresenceNormalForm.All Yulang.Common.model assignment
      (Yulang.CommonRoleOpenPropagation.pass visible allocate q s).state.atoms →
    Yulang.PresenceNormalForm.All Yulang.Common.model assignment s.atoms
@Yulang.CommonRoleOpenPropagationOrigin.capture_bounds : ∀ {n : Nat}
  (allocate : Yulang.CommonRoleOpenPropagation.Allocation n) (d : Yulang.CommonRoleSettledSyntax.Declaration)
  (lo up : Yulang.CommonRoleSettledSyntax.Ty) (name : Nat) (pair : Fin n × Fin n),
  pair ∈ Yulang.CommonRoleCandidateConstraints.bounds (Yulang.CommonRoleOpenPropagation.capture allocate d lo up) name →
    pair = (allocate lo, allocate up)
@Yulang.CommonRoleOpenPropagationOrigin.capture_present : ∀ {n : Nat}
  (allocate : Yulang.CommonRoleOpenPropagation.Allocation n) (d : Yulang.CommonRoleSettledSyntax.Declaration)
  (lo up : Yulang.CommonRoleSettledSyntax.Ty) (name : Nat),
  name ∈ d.head.names →
    (allocate lo, allocate up) ∈
      Yulang.CommonRoleCandidateConstraints.bounds (Yulang.CommonRoleOpenPropagation.capture allocate d lo up) name
@Yulang.CommonRoleOpenPropagationOrigin.capture_exact : ∀ {n : Nat}
  (allocate : Yulang.CommonRoleOpenPropagation.Allocation n) (d : Yulang.CommonRoleSettledSyntax.Declaration)
  (lo up : Yulang.CommonRoleSettledSyntax.Ty)
  (assignment : Fin n → Yulang.Core.PresenceGeneration.Comp Yulang.Common.model),
  Yulang.CommonRoleCandidateConstraints.Compatible (Yulang.CommonRoleOpenPropagation.capture allocate d lo up)
      assignment ↔
    d.head.names = [] ∨ Yulang.Common.Subtype (assignment (allocate lo)).fst (assignment (allocate up)).fst
@Yulang.CommonRoleOpenPropagationOrigin.selected_update_origin : ∀ {n : Nat}
  (visible : List Yulang.CommonRoleSettledSyntax.Declaration) (allocate : Yulang.CommonRoleOpenPropagation.Allocation n)
  (q : Yulang.CommonRoleOpenProducer.Request) (key : Nat) (cs : List Yulang.CommonRoleOpenProducer.Request),
  Yulang.CommonRoleOpenProducer.Local visible q (Yulang.CommonRoleOutermostResolver.Frontier.selected key cs) →
    ∃ d lo up,
      Yulang.CommonRoleOpenProducer.production visible q = some (d, lo, up) ∧
        key = d.key ∧
          cs = Yulang.CommonRoleOpenProducer.children q d lo up ∧
            Yulang.CommonRoleOpenPropagation.update visible allocate q =
              Yulang.CommonRoleOpenPropagation.capture allocate d lo up
@Yulang.CommonRoleOpenPropagationOrigin.selected_prepare_exact : ∀ {n : Nat}
  (visible : List Yulang.CommonRoleSettledSyntax.Declaration) (allocate : Yulang.CommonRoleOpenPropagation.Allocation n)
  (q : Yulang.CommonRoleOpenProducer.Request) (key : Nat) (cs : List Yulang.CommonRoleOpenProducer.Request)
  (s : Yulang.CommonRoleSettledConstraints.State n),
  Yulang.CommonRoleOpenProducer.Local visible q (Yulang.CommonRoleOutermostResolver.Frontier.selected key cs) →
    ∃ d lo up,
      Yulang.CommonRoleOpenProducer.production visible q = some (d, lo, up) ∧
        key = d.key ∧
          cs = Yulang.CommonRoleOpenProducer.children q d lo up ∧
            ∀ (assignment : Fin n → Yulang.Core.PresenceGeneration.Comp Yulang.Common.model),
              Yulang.PresenceNormalForm.All Yulang.Common.model assignment
                  (Yulang.CommonRoleOpenPropagation.prepare visible allocate q s).atoms ↔
                Yulang.PresenceNormalForm.All Yulang.Common.model assignment s.atoms ∧
                  (d.head.names = [] ∨
                    Yulang.Common.Subtype (assignment (allocate lo)).fst (assignment (allocate up)).fst)
@Yulang.CommonRoleOpenRecursivePass.child_origin : ∀ {n : Nat}
  (visible : List Yulang.CommonRoleSettledSyntax.Declaration) (allocate : Yulang.CommonRoleOpenPropagation.Allocation n)
  (q : Yulang.CommonRoleOpenProducer.Request) (s : Yulang.CommonRoleSettledConstraints.State n)
  (child : Yulang.CommonRoleOpenProducer.Request),
  child ∈ Yulang.CommonRoleOpenPropagation.childList (Yulang.CommonRoleOpenPropagation.produce visible allocate q s) →
    Yulang.CommonRoleOutermostResolver.Child (Yulang.CommonRoleOpenProducer.Local visible) child q
@Yulang.CommonRoleOpenRecursivePass.runAcc_unfold : ∀ {n : Nat} (registry : Yulang.CommonRoleOpenProducer.Registry)
  (allocate : Yulang.CommonRoleOpenPropagation.Allocation n) (q : Yulang.CommonRoleOpenProducer.Request)
  (accessible :
    Acc (Yulang.CommonRoleOutermostResolver.Child (Yulang.CommonRoleOpenProducer.Local registry.declarations)) q)
  (s : Yulang.CommonRoleSettledConstraints.State n),
  Yulang.CommonRoleOpenRecursivePass.runAcc registry allocate q accessible s =
    have current := Yulang.CommonRoleOpenPropagation.prepare registry.declarations allocate q s;
    let initial := Yulang.CommonRoleOpenPropagation.produce registry.declarations allocate q s;
    let cs := Yulang.CommonRoleOpenPropagation.childList initial;
    match
      Yulang.CommonRoleOpenThreading.thread
        (fun child => Yulang.CommonRoleOpenRecursivePass.runAcc registry allocate child.val ⋯) cs.attach current with
    | (outputs, final) =>
      (Yulang.CommonRoleOpenRecursivePass.Trace.node initial outputs
          (List.map (fun child => Yulang.CommonRoleOpenPropagation.produce registry.declarations allocate child final)
            cs)
          (Yulang.CommonRoleOpenPropagation.produce registry.declarations allocate q final),
        final)
@Yulang.CommonRoleOpenRecursivePass.runAcc_eq_run : ∀ {n : Nat} (registry : Yulang.CommonRoleOpenProducer.Registry)
  (allocate : Yulang.CommonRoleOpenPropagation.Allocation n) (q : Yulang.CommonRoleOpenProducer.Request)
  (accessible :
    Acc (Yulang.CommonRoleOutermostResolver.Child (Yulang.CommonRoleOpenProducer.Local registry.declarations)) q),
  Yulang.CommonRoleOpenRecursivePass.runAcc registry allocate q accessible =
    Yulang.CommonRoleOpenRecursivePass.run registry allocate q
@Yulang.CommonRoleOpenRecursivePass.thread_attach : ∀ {α : Type u_1} {n : Nat} {β : Type u_2}
  (run : α → Yulang.CommonRoleSettledConstraints.State n → β × Yulang.CommonRoleSettledConstraints.State n)
  (xs : List α) (s : Yulang.CommonRoleSettledConstraints.State n),
  Yulang.CommonRoleOpenThreading.thread (fun x => run x.val) xs.attach s =
    Yulang.CommonRoleOpenThreading.thread run xs s
@Yulang.CommonRoleOpenRecursivePass.run_unfold : ∀ {n : Nat} (registry : Yulang.CommonRoleOpenProducer.Registry)
  (allocate : Yulang.CommonRoleOpenPropagation.Allocation n) (q : Yulang.CommonRoleOpenProducer.Request)
  (s : Yulang.CommonRoleSettledConstraints.State n),
  Yulang.CommonRoleOpenRecursivePass.run registry allocate q s =
    have current := Yulang.CommonRoleOpenPropagation.prepare registry.declarations allocate q s;
    have initial := Yulang.CommonRoleOpenPropagation.produce registry.declarations allocate q s;
    have cs := Yulang.CommonRoleOpenPropagation.childList initial;
    match
      Yulang.CommonRoleOpenThreading.thread (Yulang.CommonRoleOpenRecursivePass.run registry allocate) cs current with
    | (outputs, final) =>
      (Yulang.CommonRoleOpenRecursivePass.Trace.node initial outputs
          (List.map (fun child => Yulang.CommonRoleOpenPropagation.produce registry.declarations allocate child final)
            cs)
          (Yulang.CommonRoleOpenPropagation.produce registry.declarations allocate q final),
        final)
@Yulang.CommonRoleOpenRecursivePass.run_exact : ∀ {n : Nat} (registry : Yulang.CommonRoleOpenProducer.Registry)
  (allocate : Yulang.CommonRoleOpenPropagation.Allocation n) (q : Yulang.CommonRoleOpenProducer.Request)
  (s : Yulang.CommonRoleSettledConstraints.State n) (trace : Yulang.CommonRoleOpenRecursivePass.Trace)
  (final : Yulang.CommonRoleSettledConstraints.State n),
  Yulang.CommonRoleOpenRecursivePass.run registry allocate q s = (trace, final) ↔
    Yulang.CommonRoleOpenRecursivePass.Runs registry.declarations allocate q s trace final
@Yulang.CommonRoleOpenRecursivePass.runs_preserves : ∀ {n : Nat}
  (visible : List Yulang.CommonRoleSettledSyntax.Declaration) (allocate : Yulang.CommonRoleOpenPropagation.Allocation n)
  (q : Yulang.CommonRoleOpenProducer.Request) (s final : Yulang.CommonRoleSettledConstraints.State n)
  (trace : Yulang.CommonRoleOpenRecursivePass.Trace),
  Yulang.CommonRoleOpenRecursivePass.Runs visible allocate q s trace final →
    ∀ (assignment : Fin n → Yulang.Core.PresenceGeneration.Comp Yulang.Common.model),
      Yulang.PresenceNormalForm.All Yulang.Common.model assignment final.atoms →
        Yulang.PresenceNormalForm.All Yulang.Common.model assignment s.atoms
@Yulang.CommonRoleOpenRecursivePass.run_preserves : ∀ {n : Nat} (registry : Yulang.CommonRoleOpenProducer.Registry)
  (allocate : Yulang.CommonRoleOpenPropagation.Allocation n) (q : Yulang.CommonRoleOpenProducer.Request)
  (s : Yulang.CommonRoleSettledConstraints.State n)
  (assignment : Fin n → Yulang.Core.PresenceGeneration.Comp Yulang.Common.model),
  Yulang.PresenceNormalForm.All Yulang.Common.model assignment
      (Yulang.CommonRoleOpenRecursivePass.run registry allocate q s).snd.atoms →
    Yulang.PresenceNormalForm.All Yulang.Common.model assignment s.atoms
@Yulang.CommonRoleOpenRecursivePass.run_recollects : ∀ {n : Nat} (registry : Yulang.CommonRoleOpenProducer.Registry)
  (allocate : Yulang.CommonRoleOpenPropagation.Allocation n) (q : Yulang.CommonRoleOpenProducer.Request)
  (s final : Yulang.CommonRoleSettledConstraints.State n)
  (initial parent : Yulang.CommonRoleOutermostResolver.Frontier Yulang.CommonRoleOpenProducer.Request)
  (outputs : List Yulang.CommonRoleOpenRecursivePass.Trace)
  (refreshed : List (Yulang.CommonRoleOutermostResolver.Frontier Yulang.CommonRoleOpenProducer.Request)),
  Yulang.CommonRoleOpenRecursivePass.run registry allocate q s =
      (Yulang.CommonRoleOpenRecursivePass.Trace.node initial outputs refreshed parent, final) →
    Yulang.CommonRoleOpenPropagation.Produced registry.declarations allocate q final parent ∧
      Yulang.CommonRoleOutermostResolver.All₂
        (fun child observation =>
          Yulang.CommonRoleOpenPropagation.Produced registry.declarations allocate child final observation)
        (Yulang.CommonRoleOpenPropagation.childList initial) refreshed
```
