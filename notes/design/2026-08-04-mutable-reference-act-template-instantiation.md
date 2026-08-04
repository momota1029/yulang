# Mechanism 1 対処設計: 可変参照act-copyのtyped template instantiation

日付: 2026-08-04

状態: **M1-0〜M1-9 全スライス着地・完了（2026-08-04）。
Mechanism 1 は完全にclose。§7に最終結果を記録**

著者: Claude (Sonnet 5)（Codex `gpt-5.6-sol` xhigh の調査・設計提案を統合）

本書は
`notes/design/2026-08-04-mutable-reference-performance-investigation.md`
（可変参照性能調査、根本原因の特定）のMechanism 1（act-copy
オーバーヘッド）に対する具体的な対処設計である。Mechanism 2
（subtype replay増幅）は正しさに関わる領域のため対象外とし、
別途専用の調査・設計を行う。

## 1. 問題の再確認

`my $a`のようなmutable state束縛は、finalization時
（`crates/infer/src/module_map/finish.rs:340`）に
`std.control.var.var`テンプレートをCSTから丸ごとコピーし、
そのコピーを通常のbinding/method loweringで**毎回再lowering**
している（`crates/infer/src/lowering/body/act.rs:221`）。
1束縛あたり約24ms、束縛数にほぼ線形。

先行調査（Mechanism 1の根本原因調査、§3.3）で:

- 束縛ごとのfresh family/operation identityは**本物の意味論的
  要求**（他の束縛のhandlerが横取りしないため必須）。
- CST全体の再登録・再推論は**実装上の結合であって必然ではない**。
- 既存の`SchemeInstantiator`（通常の多相関数再利用機構）は
  constructor/effect pathをそのままcloneするため、そのまま
  流用はできない。

## 2. 対象範囲の切り分け（束縛固有の作業 vs 冗長な作業）

Codex `gpt-5.6-sol` xhighによるコード読解で確認した内訳:

**束縛ごとに必ず必要な作業**:

- destination actの`TypeDeclId`とexact family pathを新規発行する
  （他束縛のhandlerとの混線防止）。
- destination get/set `DefId`を新規発行し、`SyntheticVarEffect`
  経由でfamilyと紐付ける。
- 別々の`var_ref`/`run` `DefId`を維持する（既存test
  `case_03.rs:1315`が要求）。
- destination companion namespaceを作成する。
- arena-local body identity（`DefId`/`ExprId`/`PatId`/`RefId`/
  `SelectId`）を新規発行する——`run`が自身へ静的再帰参照を持ち、
  `var_ref`が自身のget/set operationへ静的参照を持つため、単純な
  共有はできない。
- destination family/operation identityを、cloneされたscheme・
  runtime body metadataへ代入する。
- ユーザーの実際のinitializer・read・write・wrapper呼び出しは
  通常どおりloweringする。

**構造的に冗長な作業（除去対象）**:

- 束縛のたびに同じ`var.yu`のCSTを歩き直す。
- 同じget/set annotation構造を再構築する。
- 同じ`var_ref`レコード（closure 2つ）・recursive `run`・
  catch armを再lowerする。
- 同じ外部名・method selectionを再解決する。
- alpha同値な制約グラフを再生成する。
- SCC settlement・subtype propagation・generalization・scheme
  finalizationを走らせて同じ4つのschemeを再発見する。
- `ref`/`ref_update`への同じ外部依存を再計算する。

テンプレート（`var.yu`、24行）の構造は、束縛先の要素型に依存しない
——payloadは`'t`として一般化されたまま残り、initializerの型は
後続の使用箇所を制約するだけで、新たにlowerされるhelper body自体を
specializeするわけではない。

## 3. 採用する設計方向: typed template instantiation

検討した3方向のうち、以下を採用する。

| 方向 | 評価 |
|---|---|
| nominal family pathをTypeVar/SubtractIdと並ぶ量化パラメータへ全面拡張 | 汎用だが範囲が広すぎる。全`Con` path・stack subtraction形・serializer・generalizer・cache境界・runtime operation・診断表現がfamily変数を扱う必要が生じ、しかもbody `DefId`のclone/remapは別途必要。XLスコープ・高い意味論的リスクのため不採用。 |
| **専用のtyped template instantiation（採用）** | 具体的pathを最終Poly IRに保持したまま、template import時に既知の1つのfamilyだけを明示的に置換し、finalize済みのbody/schemeを再利用する。shadow/oracleによる段階的展開に足る狭さ。 |
| canonical `var_ref`/`run` bodyを薄いwrapperの裏で共有 | runtime/IR変更なしには成立しない。canonical `run`はcanonicalなget/set pathをcatchしており、wrapperはその静的path/DefIdを再ターゲットできない。動的family parameterか新しいruntime primitiveが必要になる。不採用。 |
| 最初のsynthetic copyだけ推論し、以後の束縛はそれをcloneする | 最初の束縛自体には効果がなく、単一のpost-lowering analysis drainと衝突する。早期quantifyはforward referenceを壊すリスクがある。不採用。 |

### 3.1 機構の概要（Investigation A反映済み）

「型付きtemplateのimport + nominal identity置換」。

Investigation A（synthetic copyパターンの全数調査）により、
synthetic act-copyは**`var`と`label_sub`の2種類のみ**と確定した。

- `var`（`std.control.var.var`、`var.yu`）: operation
  `get`/`set`、private helper `var_ref`・recursive `run`、
  外部依存`ref`/`ref.update`/`ref_update.update`。nested
  nominal宣言は持たない。
- `label_sub`（`std.control.flow.label_sub`、`flow.yu`）:
  operation `return`、**nested nominal `struct label`**・その
  constructor・field method（`label.marker`の値/ref版）、
  `control_label`（copyされたnested labelを構築）、`sub`
  （copyのlocal `return`と、canonical外部
  `std.control.flow.sub.return`の**両方**をcatchする）。

`label_sub`はnested nominal型を持つため、当初の「1 act +
member一覧」という表現では表せない。identityは**コピーされた
nominal namespace全体の閉包**として一般化する必要がある。
（`act copy = source`というユーザ記述の明示的actコピー構文は、
`CopiedSourceExport`を使い`pub`/`our`のみをコピーする別物で、
本メカニズムの対象外とする——将来の拡張を妨げない表現には
するが、M1では`var`と`label_sub`のsynthetic copyのみを対象と
明示する。）

新設するデータ構造（すべてtransientなlowering内部データであり、
新しいPoly表面型やsurface構文ではない）:

```text
NominalActTemplateIdentity
    root_act: nominal type identity
    nominal_types:
        source TypeDeclId
        source exact path
        structural role: root act | nested declaration
    value_members:
        owner nominal type
        kind: operation | binding | constructor | field method
        name / receiver kind
        source DefId
        operation path（該当する場合）

NominalActInstanceSubstitution
    type_decl_map: source TypeDeclId -> destination TypeDeclId
    type_path_map: source nominal path -> destination nominal path
    def_map: source internal DefId -> destination DefId
    operation_path_map: source local operation path -> destination path

TypedActTemplate
    finalize済みmember scheme
    到達可能なtype graphのcompact表現
    Def/Expr/Pat/Ref/Select body graphのcompact表現
    internal/external DefId参照の分類
    source nominal namespace closure（NominalActTemplateIdentity）

TypedActInstantiationProduct
    destination scheme・body graph
    新規nested arena ID
    remapされたlabel
    destination effect-operation metadata
    finalize済みdestination definitionの一覧
```

`label_sub`の場合、`std.control.flow.label_sub`と
`std.control.flow.label_sub.label`の両方をdestination pathへ
書き換える必要がある一方、canonical外部の
`std.control.flow.sub.return`は書き換えてはならない——この
internal/external区別が最重要の正しさ条件になる（§5参照）。

最終的な`Scheme`・`Expr`ノードは、引き続き具体的な
destination pathを持つ（scheme自体にfamily変数を持たせない）。

### 3.2 Hook位置

1. **Module registration**はほぼ現状維持。
   `register_synthetic_var_act_copy`
   （`crates/infer/src/module_map/mod.rs:923`）がfresh act
   identityの発行を継続し、`materialize_act_copy`
   （`crates/infer/src/module_map/finish.rs:398`）がdestination
   companion・member shellの作成を継続する。finalization時に
   source-member → destination-memberの対応を明示的に保持する
   よう拡張する（`ResolvedActCopyDecl`拡張、または
   sibling `ResolvedActCopyMemberMap`）。

2. **finalize済みsource templateを、warm loweringの実行ごとに
   一度だけ取得する。** source は既にcompile済みのprefixから
   取得し、以下の厳格な適格性を満たす場合のみ使う:
   - コピー対象の全source memberがfinalize済みのclosed scheme
     を持つ。
   - 選択された全body ref/selectionが解決済み。
   - source/destination memberの形状が完全に対応する。
   - source defがprefix runtimeに属する。
   - templateがimporterのサポートするgraph/metadata形のみで
     構成される。
   到達可能なtemplate graph・type nodeのみをcaptureし、std
   Poly arena全体は取り込まない。

3. **既存のsynthetic-copy境界でinstantiateする。**
   `lower_synthetic_act_copy_bodies_for`
   （`crates/infer/src/lowering/body/act.rs:227`）が、synthetic
   var copyに対しまずtyped instantiationを試みる。成功した
   instanceは`lower_act_body_contents`をスキップする。sub-label
   copyや不適格なcopyは既存のCST経路を維持する。

4. **網羅的な置換を適用する。** type importerは以下の中の
   source familyを書き換える: `Pos::Con`・`Neg::Con`・
   `Neu::Con`・全`Subtractability::{Set, SetMany, AllExcept,
   AllExceptMany}` path。body importerは以下をremapする:
   解決済みref・再帰参照・pattern-local definition・selection
   resolution・`CatchOperation.def`/`CatchOperation.path`・
   get/set `EffectOperation.path`。`ref_update`・`ref.update`
   等の外部defは既存prefix DefIdへのmapを維持する。

5. **analysis drain前にinstanceをfinalize済みとして公開する。**
   SCC machineは既に`seed_quantified_def`でfinalize済み
   definitionのseedingをサポートしている。AnalysisSessionの
   小さな境界で、「closed typed-template scheme」として
   definitionを登録する。これは通常の`imported_scheme_defs`
   とは別に表現することを推奨する——template schemeは今回の
   実行におけるgeneralization記録を持たないが、freshen後は
   closedであり、prefix境界に依存しない。instantiationには
   既存のvalidated-finalized-scheme経路を空boundaryで使う。

6. **validate-then-commit方式を取る。** 適格性・member
   mapping・graph closure・scheme closure・nominal置換は、
   destination arenaを変更する前に全て検証する。検証後の
   commitは失敗しない機械的なallocation/remapのみとする。
   検証失敗時は、部分的にdestination definitionを作らないまま
   既存のCST loweringへfallbackする。

見積規模: `var`/`label_sub`両対応・warm/cold両経路を含めて
約1,800〜2,600行（当初のvar-only・warm-only見積り900〜1,500行の
約2倍）。production codeのリスクは中〜高だが局所的。global
family-quantifier案はこれより大幅に大きく、リスクも高い。

### 3.3 Cold/no-prefix経路の設計（Investigation B反映済み）

cold compile（std prefix未compileの状態、例: `--no-cache`での
初回CLI実行やWASM artifactのfrom-scratch再構築）では、
warm経路が前提とする「finalize済みprefixからtemplateを
captureする」という手段自体が使えない。2つの選択肢を検討した。

**選択肢(a) precompiled template artifact**: `var.yu`・
`flow.yu`のfinalize済みtemplateだけを含む、コンパクトな
専用bundleを事前生成し埋め込む。playgroundの
`compiled_playground_std.yucu`/`compiled_full_std.yucu`と
同じ「一度compileして埋め込み、実行時は安く読む」という
既存パターンの応用。

**選択肢(b) 境界を絞ったpartial-analysis lifecycle**:
通常のforward-reference依存のanalysis順序より前倒しで、
`var`/`label_sub`のtemplateだけを早期に確定させる。

Investigation Bの結論: **選択肢(a)を採用、選択肢(b)は却下**。

選択肢(b)を却下する理由: 挿入点候補
（`crates/infer/src/lowering/body/mod.rs:786`の直前）の時点で
既にuser bodyがsynthetic member shellへの未完成な参照を
発行済みであり、`AnalysisSession::drain_work`はSCC
generalization・method selection・role conformance・
synthetic-copy userを同じqueueで混在処理する。既存の
`drain_selection_work_for_parent`はselection workのみを
対象としdefinition/SCCをfinalizeしない。`seed_quantified_def`
はdefinitionが既にfinalize済みであることを前提とし、
template自体を生成する手段ではない。さらに`label_sub.sub`は
canonical `sub`との post-alias interval constraintを持ち、
`var`も`ref`/`ref.update`/`ref_update`に依存するため、
どちらも自己完結した依存境界を持たない。これを安全にするには
新しいtarget-SCC settlement protocol・依存閉包の証明・
conformance処理・queue分割・「未完成なsynthetic memberを
deferred workが観測しない」保証が必要になり、**局所的な
helperではなくscheduler本体の再設計**に相当する。よってM1の
範囲では選択肢(b)を採らない。

選択肢(a)の具体的な設計:

- `.yucu`全体ではなく、専用の`TypedActTemplateBundle`を
  新設する（現行`.yucu`は1プロファイルあたり0.7〜1.1MBあり、
  installation identityを含む保守的なsource keyを使うため、
  そのまま流用すると「cold source compilation」自体が
  「full std-prefix経路」に変わってしまう——Mechanism 1の
  スコープを超える）。
- legacy CST経路のみを使い、確定済みのstd loweringから生成する
  （生成時はtemplate instantiationを無効化し、自己参照的な
  検証にならないようにする）。
- `FullStd`と`PlaygroundStd`の2プロファイルを持ち、各々
  `std.control.var.var`と`std.control.flow.label_sub`両方の
  canonical templateを含む。
- envelope version・typed-template schema version・compiler
  互換性version・std moduleの意味論的fingerprint（sorted
  module path＋source hashで構成し、userのentry pathや
  installation filesystem pathは含めない）を持つ。
- internal arena identityはtemplate-local slotとしてシリアライズ
  する。外部参照は生の`DefId`ではなく、既存`.yucu`の分類法
  （module path・value path・`(owner type path, name, receiver
  kind)`のtype-field method key・castキー）にならった安定keyで
  シリアライズする。
- `yulang` crate自体に埋め込む（native CLIとWASM両方の経路が
  参照できるように）。`yulang`にはbuild scriptが無く、
  「templateの生成にはcompiler自体が要る」という自己ビルド
  依存循環を避けるため、明示的なgenerator/releaseステップ＋
  checked-inのgenerated assetという形にする。CIはlegacy経路で
  再生成し、既存assetとbyte/semantic比較して、乖離があれば
  失敗させる。
- process単位で一度だけdecodeし、module registration後に
  外部安定keyを当該runのDefIdへ束ねて、warm経路と同じ
  `TypedActTemplateCatalog`を構築する。
- 適格性はwarmと同じvalidate-then-commit方式。stale
  profile・custom std・未解決anchor・非対応graph node・形状
  不一致はいずれもproduction上ではlegacy CST loweringへ
  fallbackする。canonicalなfull/playgroundプロファイルは
  CIでeligibility assertionをhard-failさせる。
- `--no-cache`下でも使ってよい——これはuser cacheの読み書きを
  一切行わず、source収集やstd compilationをスキップするもの
  でもない。単に、synthetic templateの反復的な再loweringを
  compiler同梱の型付きデータへ置き換えるだけである。
- **スコープの明示的な境界**: 同梱bundleはshippedされている
  full/playground std profileに対してのみ初回実行の高速化を
  保証する。任意の変更済み`--std-root`は、対応する生成済み
  template profileが無ければ安全にlegacy経路へfallbackする
  （このケースまで高速化を保証するには、却下した
  partial-analysis設計かuser生成のtemplate artifactが必要に
  なる——本Mechanism 1のスコープ外とする）。

warmとcoldの違いはcatalogの取得元だけに閉じる:

```text
warm prefix
    -> importしたprefixからfinalize済みtemplateをcapture
    -> TypedActTemplateCatalog

cold/no prefix
    -> 埋め込みprofileをvalidate/decode
    -> 外部anchorを現在のModuleTableへ解決
    -> TypedActTemplateCatalog

両方共通
    -> 同じnominal substitution
    -> 同じdetached validation
    -> 同じcommit/installライフサイクル
```

## 4. 実装スライス計画（Investigation A・B反映済み、未承認・提案）

1. **M1-0 — 拡張された契約とmeasurementの固定**
   `Var | LabelSub`・`Prefix | Embedded`・eligible/miss/
   fallback・legacy CST loweringの4次元でcensusを追加。warm・
   cold両方のコスト傾きと正規化済みparityビューを固定する。
   production挙動は変更しない。

2. **M1-1 — Nominal namespace identityとshell mapping**
   単一family表現を、一般化されたnominal-closure表現
   （`NominalActTemplateIdentity`）へ置き換える。root act・
   nested type・constructor・field method・通常member・
   operationについて、materialization時にsource/destination
   対応を記録する。`var`と`label_sub`両方のshellをカバーする。
   production挙動は変更しない。

3. **M1-2 — Scheme/type template capture**
   両templateのclosed schemeと到達可能なtype graphをcapture
   する。全`Pos`/`Neg`/`Neu`constructorとsubtraction形に渡る
   multi-path nominal substitutionをサポートする。安定した
   外部参照keyを導入する。shadow-only。

4. **M1-3 — Body/runtime graph clone**
   Def/Expr/Pat/Ref/Select・再帰参照・constructor・nominal-
   record metadata・catch・effect operation・labelをdetached
   storageへcloneする。両template、特に`label_sub`の
   local/external混在catch pathについてlegacy parity oracleを
   追加する。

5. **M1-4 — 共有template catalogとinstance lifecycle**
   既存のsynthetic-copy phaseが消費する共通
   `TypedActTemplateCatalog`を導入する。単一の通常analysis
   drain前に、検証済みinstanceをclosed finalized definition
   としてinstallする。prefix-capture instanceとlegacy出力を
   比較する。production cutoverはまだ行わない。

6. **M1-5 — Warm production cutover（gate付き）**
   適格なprefix templateについて、`var`・`label_sub`両方の
   instantiationを有効化する。atomic fallbackとCI hard
   assertionを維持する。当初のvar-first warm cutoverをこれで
   置き換える。

7. **M1-6 — Cold bundle形式と再現可能なgenerator**
   versioned compact envelope・full/playgroundプロファイル・
   std意味論的fingerprint・legacy-onlyのcapture command・
   checked-in/release asset・CI再生成チェックを追加する。
   production未使用のまま、decodeと安定した外部anchor解決を
   検証する。

8. **M1-7 — Cold shadow integration**
   埋め込みcatalogをcold source lowering（`--no-cache`・WASM
   source fallback含む）へ供給する。埋め込みcatalog vs
   prefix-capture catalog、埋め込みinstantiation vs cold
   legacy CST lowering、full-std vs playground-stdプロファイル
   の挙動を比較する。

9. **M1-8 — Cold production cutover（gate付き）**
   parity確認後、cold経路を有効化する。空のuser cache・
   `--no-cache`・初回CLI実行・from-scratch WASM artifact構築・
   無効/staleなbundleのfallback・custom stdのfallbackを検証
   する。早期analysis drainが導入されていないことをassertする。

10. **M1-9 — Default cutoverとcloseout**
    warm/cold parity確認後、一時的なgateを外す。cache
    on/off・insertion order・portable artifact・診断・runtime
    isolation・nested label・複数束縛のsuiteを実行する。受け
    入れ基準: 適格な`var`/`label_sub`のCST re-loweringがゼロ
    件、distinctなnominal identityが保たれている、source
    familyの漏洩が無い、M1-0の実測に基づくsub-millisecond級の
    instance-materialization目標、cold/warmの出力parity。

（旧・任意扱いだったM1-5「cold対応の要否調査」は削除し、
cold対応をM1-6〜M1-8の必須スライス群として再定義した。）

## 5. リスク・不変条件の分析

- **Family漏洩**: 1つでも未書き換えのsource pathが残ると、
  新しい束縛がcanonical stdのoperationを送信・catchしてしまう。
  検証: 全destination scheme・stack weight・effect operation・
  catch armを走査し、canonicalなsource family/operation pathが
  一切残っていないことをassertする。

- **束縛間の混線**: get/set/run refが誤って別instanceを
  ターゲットしうる。検証: 2つのmutable bindingを絡めて使い、
  distinctなact ID・4つのdistinctなmember DefId・束縛local
  なcatch path・独立したruntime結果を確認する。

- **internal/external Def分類の不備**: 外部std methodをclone
  すると global identityが重複し、internal source defを保持
  すると instance同士がaliasする。検証: body graphを
  `Local(slot)`/`External(def)`の明示的identityで正規化し、
  legacy loweringと比較する。

- **Scheme不一致**: path置換やTypeVar/SubtractIdのfreshening
  がprincipal typeを変えうる。検証: 全operation/helper scheme
  について、stack quantifier・recursive bound・role predicateを
  含めたalpha正規化済み等価性を確認する。

- **SCC lifecycleの破壊**: queue済みのsuffix使用箇所が
  placeholder schemeを観測したり、openなlocal definitionとして
  誤分類されうる。検証: lifecycle traceで、template defが
  最初の`UseResolved` event drain前にfinalize済みとしてseedされ
  ていることを示す。成功したtyped instanceについて
  `RegisterDef`/`DefFinished`が発行されないことを確認する。

- **provenance/診断の欠落**: template bodyは現状意図的に
  source span/runtime rootを持たないが、legacy constraint
  generationはinternal provenanceを生成する。検証: 完全な
  診断・runtime root・source span不在・application provenance
  不在・specialization結果・runtime出力を比較する。template
  definitionはsource-owned definitionではなくcompiled-prefix
  definitionとして扱う。

- **Templateの将来的な変化**: 将来`var.yu`に子要素の種類が
  増えた場合、静かに見落とされうる。検証: 列挙されたfailure
  reasonを伴う厳格な構造的適格性チェックを行う。未サポートの
  形状は必ずlegacy loweringを使う。Expr/Pat/type variantは
  網羅的なRust enum matchで保護する。

- **部分fallbackの破損**: 一部のdestination defを書いた後に
  未サポートnodeを発見すると、legacy fallbackが無効になる。
  検証: detached validation → 単一のcommit境界という構成にし、
  precommitの各拒否点でfault-injection testを行う。

- **決定性とallocation順**: graph cloneはCST loweringとは
  異なる順でnested IDをallocateする。検証: insertion-order・
  repeated-run artifactの比較は、semantic/alpha正規化済みの
  内容で行う。raw arena IDはrun-localのままでよいが、新経路内
  でのallocationは決定的でなければならない。

## 6. オープンな設計判断（2026-08-04、ユーザ確認済み）

1. **対象範囲**: **cold/no-prefix compilationの高速化も含めて
   Mechanism 1完了とする**（Codexの推奨「warm-firstに限定し、
   coldはM1-5として別途調査」より広い範囲をユーザが選択）。
   §3.2の設計提案時点でCodexが指摘していたとおり、cold fast
   pathには「precompiled std template artifact」か「慎重に
   境界を絞ったpartial-analysis lifecycle」のいずれかが必要で、
   現行のlowering契約（全forward referenceが揃うまでanalysisを
   意図的に遅らせる）と両立させる設計がwarm経路とは別に要る。
   §4のスライス計画は、M1-5を「必要なら後で」ではなく
   本プロジェクトの必須スコープとして改訂する必要がある。

2. **適用範囲**: **sub-label copyも最初から含める**（Codexの
   推奨「まずvar-onlyから」より広い範囲をユーザが選択）。
   `NominalActIdentity`/`NominalActSubstitution`等の表現が
   sub-label copyの実際の構造（var copyとどれだけ形が
   似ているか、あるいは異なるか）にも対応できるかどうかを、
   実装着手前に確認する必要がある。

3. **適格性miss時の扱い**: **Codexの推奨どおり確定**——
   production（release build）では黙ってlegacy CST lowering
   へfallbackし処理は継続する。test/CIでは、canonicalな
   `var.yu`が常に適格であり続けることをhard assertionで検証し、
   退行を即座に検知する。

これらの決定を受け、以下の追加調査（Investigation A・B）を
実施し、本書§3・§4へ反映済み:

- **Investigation A（完了）**: sub-label copyの実際のパターン
  一覧と、var copyとの構造的な異同の調査。結論:
  synthetic copyは`var`と`label_sub`の2種類のみ。identity
  表現を「単一family」から「nominal namespace閉包」へ
  一般化する必要があると判明し、§3.1へ反映済み。
- **Investigation B（完了）**: cold pathでのtemplate
  instantiation機構の選定と設計。結論: precompiled artifact
  方式（選択肢a）を採用、partial-analysis lifecycle方式
  （選択肢b）は「局所的なhelperではなくscheduler本体の
  再設計に相当する」ため却下。§3.3へ反映済み。
- §4実装スライス計画は、上記2件を反映しM1-0〜M1-9の10段階へ
  改訂済み（cold対応をmust-haveのM1-6〜M1-8として明記）。

## 7. 完了報告（2026-08-04、M1-0〜M1-9 全スライス着地）

### 7.1 着地したスライス

- M1-0（契約とmeasurementの固定）: `0fb1bc8a`
- M1-1（nominal namespace identityとshell mapping）: `0edbfa23`
- M1-2（scheme/type template capture）: `fe805b1f`
- M1-3（body/runtime graph clone）: `d297ab01`
- 独立バグ修正（legacyの`label_sub`外部参照解決、M1-5作業中に
  発見・修正）: `e5c7b459`
- M1-4（共有template catalogとinstance lifecycle）: `359d5f54`
- M1-5（warm production cutover、gate付き——このプロジェクト初の
  production挙動変更）: `fd535c0b`
- M1-6（cold bundle形式とgenerator）: `fad04979`
- M1-7（cold shadow integration）: `7a998ffb`
- M1-8（cold production cutover、gate付き——2件目のproduction
  挙動変更。副産物としてSCC lifecycleの実バグを発見・修正）:
  `472326cf`
- M1-9（default cutoverとcloseout）: コード変更不要と確認
  （production temporary gateが存在しないことを確認、検証のみ）

### 7.2 受け入れ基準の達成状況

1. **適格な`var`/`label_sub`のCST re-loweringがゼロ件**:
   canonical std libraryに対するwarm/cold双方のeligibility test
   （`m1_5_repository_std_canonical_var_and_label_sub_are_warm_
   eligible`、`m1_8_full_std_canonical_var_and_label_sub_are_
   cold_eligible`、PlaygroundStd版）で`eligible=1、miss=0、
   fallback=0、legacy_cst_lowerings=0`を確認。
2. **distinctなnominal identityの保持**: 複数instance間で
   source→destination mappingが正しく分離されることをM1-1の
   testで確認、runtime isolation testでも独立したget/set
   familyを確認。
3. **source familyの漏洩なし**: M1-2の網羅的nominal substitution
   test、M1-3のmixed local/external catch parity testで確認。
   template-local familyは常にdestination identityへ置換され、
   意図的なexternal参照（`std.control.flow.sub.return`等）だけ
   canonical pathを維持する。
4. **sub-millisecond級のinstance-materialization**: 実測（warm
   prefix cache、release native、5回計測の中央値）で
   - `var`: legacy 27.139ms → typed **0.237ms**（約114倍）
   - `label_sub`: legacy 2.857ms → typed **0.359ms**（約8倍）
   両方ともsub-millisecond目標を達成。
5. **cold/warm出力parity**: M1-7・M1-8のFullStd/PlaygroundStd
   3-way parity test（embedded typed instantiation・live-prefix
   capture・legacy CST lowering）が全てgreen。

### 7.3 副産物として発見・修正した独立バグ

本プロジェクトの実装過程で、Mechanism 1自体とは別に、以下の
production correctnessバグを発見・修正した（いずれもshadow/
parity検証が実際に効いた実例）:

- **legacy `label_sub`の外部参照解決バグ**（`e5c7b459`）:
  synthetic copyの再lowering時、相対参照`sub::return`が
  destination contextで解決できず、raw未解決の短縮pathを記録
  していた。M1-5のwarm cutover検証中に発見。
- **SCC lifecycleの実バグ**（`472326cf`内）: `seed_quantified_def`
  が、既に存在するedge-only placeholder componentを正しく
  処理せず、predecessorが永久にquantifyされない場合があった。
  cold cutoverでのみ発現（warm cutoverは早期installのため
  この経路を通らない）。「missing type scheme」および
  「MissingRecordField("index")」という2つの異なる症状の
  共通原因だった。M1-8の実CLIシナリオ検証で発見。

### 7.4 残された作業（本プロジェクトのスコープ外）

- **custom/stale std**: 設計どおりlegacy fallbackとなる。この
  ケースでのcold高速化はMechanism 1の対象外（§3.3の明示的な
  スコープ境界どおり）。
- **Mechanism 2（read-modify-write時のsubtype replay増幅）**:
  `notes/design/2026-08-04-mutable-reference-performance-
  investigation.md`の§4で特定した、Mechanism 1とは独立した
  正しさに関わる領域の問題。本プロジェクトでは対象外のまま。
  別途専用の調査・設計が必要。

---

著者: Claude (Sonnet 5)（Codex `gpt-5.6-sol` xhigh の調査・設計提案を統合）

M1-0〜M1-9 全スライスが着地・検証済み（2026-08-04）。
Mechanism 1（act-copyオーバーヘッド）は完全にcloseとして扱う。
