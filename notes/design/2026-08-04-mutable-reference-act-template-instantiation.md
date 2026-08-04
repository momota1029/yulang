# Mechanism 1 対処設計: 可変参照act-copyのtyped template instantiation

日付: 2026-08-04

状態: **ユーザ確認済み（2026-08-04）。§6の3判断は解決済み——
下記のとおりCodexの推奨より広い範囲で確定した。実装スライスは
この決定を反映するよう§4を改訂する必要がある（本書では未改訂、
次段階の追加設計で行う）**

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

### 3.1 機構の概要

「型付きtemplateのimport + nominal identity置換」。

新設するデータ構造（すべてtransientなlowering内部データであり、
新しいPoly表面型やsurface構文ではない）:

```text
NominalActIdentity
    act: TypeDeclId
    family_path: Vec<String>
    members:
        member kind/name
        DefId
        operation path（該当する場合）

NominalActSubstitution
    source: NominalActIdentity
    destination: NominalActIdentity
    root_def_map: source member DefId -> destination member DefId

TypedActTemplate
    finalize済みmember scheme
    到達可能なtype graphのcompact表現
    Def/Expr/Pat/Ref/Select body graphのcompact表現
    internal/external DefId参照の分類
    source nominal identity

TypedActInstantiationProduct
    destination scheme・body graph
    新規nested arena ID
    remapされたlabel
    destination effect-operation metadata
    finalize済みdestination definitionの一覧
```

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

見積規模: 網羅的なgraph/type traversal・統合・telemetry・
parity testを含めて約900〜1,500行。production codeのリスクは
中〜高だが局所的。global family-quantifier案はこれより
大幅に大きく、リスクも高い。

## 4. 実装スライス計画（未承認・提案）

1. **M1-0 — 契約とmeasurementの固定**
   template適格性/miss件数のcensusを追加。alpha正規化済みの
   scheme/body/runtime-metadataビューを追加。1/2/3束縛での
   コスト傾きを固定する。production挙動は変更しない。

2. **M1-1 — Nominal identityとtype-template instantiation**
   source/destination memberの対応を記録。`NominalActIdentity`/
   `NominalActSubstitution`を追加。到達可能なschemeのcompact
   captureを実装。path付きの全type・全subtraction variantを
   testでカバーする。production cutoverなし。

3. **M1-2 — Body graph cloneをshadowで**
   Def/Expr/Pat/Ref/Selectの閉包をdetached arenaへclone。
   正規化した出力をlegacy re-loweringと比較する。再帰・catch
   operation path・selection・label・外部def identityをカバー
   する。

4. **M1-3 — Warm-prefix production cutover（明示的gate付き）**
   finalize済みtemplate defを、現行のsynthetic-body phaseで
   installする。完全な適格性チェック後のみCST loweringを
   スキップする。自動legacy fallbackを維持する。gate有効時と
   legacy挙動をend-to-endで比較する。

5. **M1-4 — Default warm cutoverとcloseout**
   全oracleが一致した後、defaultで有効化する。compiled-prefix
   decode・cache on/off・nested owner・insertion order・
   portable artifact・診断・runtime state isolationを検証する。
   固定した性能fixtureを再計測する。受け入れ基準は「適格な
   CST re-loweringがゼロ件」「束縛ごとのmaterialization傾きが
   sub-millisecond付近」——ただし正確な閾値は実測から設定し、
   仮定しない。

6. **M1-5 — Cold/no-prefix対応の要否調査（必要なら）**
   別設計が済むまでlegacy挙動を維持する。cold fast pathには
   precompiled std template artifactか、慎重に境界を絞った
   partial-analysis lifecycleのいずれかが必要になる。現行の
   lowering契約は全forward referenceが揃うまでanalysisを
   意図的に遅らせているため、早期の全面drainは安全でない。

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

これらの決定を受け、実装着手前に以下の追加調査・設計改訂が
必要である（本書では未実施）:

- sub-label copyの実際のパターン一覧と、var copyとの構造的な
  異同の調査。
- cold pathでのtemplate instantiation機構——precompiled
  artifact方式かpartial-analysis lifecycle方式かの選定と設計。
- 上記を反映した§4実装スライス計画の改訂（M1-5をmust-haveの
  スライス群として再定義する）。

---

著者: Claude (Sonnet 5)（Codex `gpt-5.6-sol` xhigh の調査・設計提案を統合）

本書は設計提案であり、§6の3件のオープンな判断はユーザの確認を
得て確定した（2026-08-04）。cold path・sub-label copyを含めた
拡張スコープの詳細設計は、別途の追加調査を経てから実装
（M1-0以降のスライス）に着手する。
