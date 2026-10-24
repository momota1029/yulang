# Yulangの型健全性研究資料

このページは、現在読む証明稿、規範的な研究仕様、監査記録、歴史的資料を区別する索引である。証明を追加したり、証明 gate の状態を変更したりする文書ではない。

## 2026年10月24日の統合稿と追加証明

[意味論と型健全性の統合稿](yulang-semantics-and-soundness-ja.md)は、値・効果・保護・解除・継続の寿命を共通の記法で読む入口である。採用済みの観測条件と未採用の候補規則を区別し、全言語の完了を主張しない。

[全体証明の主定理と現在の到達点](yulang-whole-proof-closure-ja.md)は、査読済みの生成・有限 interface・値型/継続の結果を定理 C として合成する。全言語への接続と元の推論 A/B を別の未完了義務として明示する。

[Leanによる全体定理の接続](../notes/theory/lean/README.md)は、その合成を機械検査するための証明プロジェクトである。任意有限 prefix と繰返し再開の合成定理、および未構成の source・推論・coverage・停止性の義務を分離する。具体的な Yulang machine/typing/cell/source instance を供給する前の条件付き定理であり、Lean の検査成功を全言語の証明完了と同一視しない。査読・検査の正確な状態は同 README と sprint outcome に記す。 制御層は [七 frame の対応稿](../notes/theory/2026-10-24-lean-control-correspondence.md)で具体化し、全 control 保存・進行と、外部再開を含む全有限 trace の型安全性を Lean で検査した。元値/metadata/全 body/source への対応はなお未完である。 [元構文・代入](../notes/theory/2026-10-24-lean-core-correspondence.md)には全 raw 木の代入合成と、unit/variable/delay + Ret/Force/let、union/intersection/Top/Bottom の構造規則を含む全 raw trace 安全性を追加した。intersection は同じ値の二導出を用い、消すのは型証拠だけである。full constructor typing と control/body bridge は未完である。

intrusion の現行資格は[生成レベル別 SCC の直接決定](../notes/design/2026-10-24-birth-level-scc-intrusion.md)に従う。以下の旧稿の跨レベル F/G・O/E qualification とその拒否履歴は旧規則についての結果として保持し、現行規則へそのまま適用しない。

- [生成レベル別 SCC と extrusion の親子等置](../notes/theory/2026-10-24-birth-level-scc-intrusion.md): 固定 birth ごとの誘導グラフ、経路・更新と局所 extrusion 結果の適用、nested helper/odd-even の変更を扱う。全体の source-scoped 保存と実装対応を区別する。[固定版と査読記録](../tasks/agent-loop/sprints/birth-level-scc-20261024-outcome.md)を参照。
- [同生成レベルの再帰と低い捕捉先への replay](../notes/theory/2026-10-24-birth-level-replay-intrusion.md): 一つの実 source の原 scalar bounds、後続コピー、実 source support の集合和と pair consumer を追跡する。依存元集合とコピーの所属を区別し、source 対応 BR-ATTR を残す。
- [replay 後の公開と二使用](../notes/theory/2026-10-24-birth-level-publication-replay.md): 正確な freshening map、元 native の独立 Int/Bool 使用と、争点の等置を公開前に加えた場合の拒否を導出する。新規則の反例や全体保存は未確定。[成果・査読範囲](../tasks/agent-loop/sprints/birth-level-replay-20261024-outcome.md)を参照。
- [保持 Value グラフの SCC と replay の境界経路](../notes/theory/2026-10-24-retained-value-graph-replay-attribution.md)と[公開への適用](../notes/theory/2026-10-24-retained-graph-publication-consequence.md): 実隣接表・singleton SCC・fresh copy から元の h-call 境界への記録の遡及を構成する。依存グラフは実際に保持されている。境界経路と現 `any` consumer の判定を具体的に計算し、元の occurrence との対応証明を残す。[固定版と査読](../tasks/agent-loop/sprints/retained-graph-replay-20261024-outcome.md)を参照。

- [共起分析と保護・解除の保存](../notes/theory/2026-10-24-cooccurrence-release-preservation.md): [ユーザーの直接訂正](../notes/design/2026-10-24-cooccurrence-release-clarification.md)に従う後続稿。`'e?` を独立した実行規則の選択として扱わず、同じ共変位置に現れる変数の集約と保護・解除の対応を示す。source 全体の証明範囲は稿内の適用境界に従う。
- [共変位置から受領対応表を作る](../notes/theory/2026-10-24-cooccurrence-source-recipes.md): 有限 signed graph での位置判定と入力 recipe、actual receipt の分離、単射改名、限定された collector 対応を構成した。
- [任意型代入と recipe](../notes/theory/2026-10-24-source-recipe-substitution.md): T1–T5 が由来を保持した source 導出の任意代入、有限経路、AllE/template、元成分別 schema を構成する。既存の捕捉証拠は固定する。一般の非正則 class 計算・実 native 対応は未完。
- [Scoped weight の集約と将来の観測](../notes/theory/2026-10-24-scoped-weight-join-compatibility.md): 単独の存在観測、正の同時観測、存在・不在の同時観測に対し、保存に必要十分な要約をそれぞれ導いた。実際の weight 実装を承認・検証したものではない。
- [現在状態に基づく handler 分岐の保存](../notes/theory/2026-10-24-correlated-handler-observation.md): 真偽両 filter、候補を飛ばす経路、arm が No を返す経路と current-world Rejoin を構成した。指定された有限候補 graph について独立査読を通過した。後続の全制御経路稿が、有限 source 導出からの生成対応を追加する。
- [修正機械の有限表示と simulation](../notes/theory/2026-10-24-corrected-machine-simulation.md): 新規 witness の生成、異なる経路の保持、保存した evidence と現在状態の再接続を明示した。初稿の三つの不備を修正し、有限な候補構成の範囲で独立査読を通過した。後続の全制御経路稿が Gen(d) の生成 edge との対応を追加し、全表層・実 compiler への対応は未完である。
- [source からの全制御経路と失敗終端](../notes/theory/2026-10-24-source-core-action-coverage.md): 13式・11 pattern・3 statement、直接証拠・eapp から Gen(d) を作り、No と継続の現在状態、失敗の吸収を証明する候補構成。結果 adapter への接続漏れを修正し、記載した前提の下で G1–G5 の独立査読を通過した。失敗専用表示では観測されない world を忘れ、具体的 cleanup は承認しない。
- [生成核の有限 interface](../notes/theory/2026-10-24-source-core-finite-interface.md): I1–I6 が有限観測欄・非正則 instance の現在 query・七 frame 接続を構成し、G5 の表示前提を除く。実 successor の包含を証明し、任意 source の recipe 生成や小さい証明書の精度は主張しない。
- [修正核の値・継続](../notes/theory/2026-10-24-corrected-core-value-continuation.md): V1–V7 が値型保存・進行・型付き反復再開を証明し、内部 code/continuation の導入契約を構成する。両稿と G5 の合成は[独立査読記録](../tasks/agent-loop/sprints/core-interface-value-20261024-outcome.md)の範囲で受理された。
- [静的 Yumark の展開](../notes/theory/2026-10-24-surface-elaboration-closure.md): 内部 node 全場合の builder と値型導出、凍結 lowering の成功時の Expr 構造との対応を構成した。独立査読でこの限定範囲に blocking/major 指摘はなかった。全 Yumark 構文や効果包含の検査成功を証明したものではない。
- [文字列補間の展開](../notes/theory/2026-10-24-string-interpolation-elaboration.md): SI1–SI6 が有限 parts 全場合の展開、型導出と完全 Call の順序を構成する。任意代入稿とともに[独立査読](../tasks/agent-loop/sprints/source-substitution-surface-20261024-outcome.md)を通過した。必要な選択/role 証拠の発見までを証明したものではない。
- [相関を持つ局所関数の核の導出](../notes/theory/2026-10-24-correlated-helper-core-derivation.md)と[元の member/world 構成試行](../notes/theory/2026-10-24-correlated-helper-original-member.md): 同じ再帰 f を捕捉する g の Int/Bool 二使用を候補核で型付けし、元の意味論へ移す際の J_rec/J_pub を特定した。[査読](../tasks/agent-loop/sprints/original-member-bridge-20261024-outcome.md)はこの部分構成の範囲を受理した。元の主型性の反例や全体閉包は得ていない。
- [extrusion / intrusion と Value SCC](../notes/theory/2026-10-24-value-scc-qualification-proof.md): source 所属参照、helper graph、SCC の計算と辺追加、実 occurrence の資格、有限 activation、局所 extrusion の終了、全旧制約を保つ型等置を証明する。全 source の coverage と combined inference の停止性は残る。
- [再帰 formation の実構成](../notes/theory/2026-10-24-original-recursive-formation-construction.md): actual registry/capture/pending plan と active-f 参照 record を構成し、選択済み native signature grammar を適用した。残る接続は active-root の完全 Call/admission と Generalize の全 typed field action。両稿の固定版と判定は [SCC sprint 記録](../tasks/agent-loop/sprints/extrusion-intrusion-scc-20261024-outcome.md)にある。
- [完全 Call の carrier 入力構成](../notes/theory/2026-10-24-original-call-admission-construction.md): 同じ full policy の refinement 射影 CA1 と、actual world/value の下での NameDelay 証拠 CA2 を構成した。今回の未注釈 witness の inlet 選択で入力 checking を閉じた。全 joint one-step proof と recursive membership は未完。
- [ActiveCapture の一般化と閉包判定](../notes/theory/2026-10-24-active-capture-generalization-closure.md): 元の field walk と template eligibility を展開し、全依存 graph/action の未構成部分を特定した。表示型や同根性だけから一般化を結論しない。両稿の限定された結果は [Call/active-capture 査読記録](../tasks/agent-loop/sprints/original-call-active-walk-20261024-outcome.md)の範囲で受理された。J_rec/J_pub と元の全体命題は未完。
- [Raw observation による再帰構成](../notes/theory/2026-10-24-original-raw-observation-postfixedness.md): raw result の相関、全 prefix、exact H の relative lift と candidate-relative inlet action を構成する。[査読記録](../tasks/agent-loop/sprints/original-raw-postfixed-20261024-outcome.md)は残項集約への MAJOR 指摘と修正を記す。元の full descriptor、各 closure/world/carrier/field の条件が残る。
- [固定二 view と source 合成](../notes/theory/2026-10-24-active-capture-field-graph.md): 一つの U Parameter/inlet、同じ g の intersection、monomorphic Bind/Name による二使用を構成する。完成済み memberships を入力とする条件付き結果であり、polymorphic J_pub の証明ではない。必要な受理契約が与えられた場合の native failure の含意 FG3 も区別する。

査読範囲、修正履歴、固定 hash、未完了義務は[今回の outcome](../tasks/agent-loop/sprints/semantics-proof-20261024-outcome.md)に記録する。既存の三つの大きな原稿全体を再査読したという意味ではない。

共起・解除の後続稿は、共起する位置集合の性質と完全な動的証拠を保持する局所表示定理の範囲で独立査読を通過した。[後続 outcome](../tasks/agent-loop/sprints/cooccurrence-release-20261024-outcome.md)が、撤回した質問の前提、固定 hash、source 対応の未完了箇所を記録する。

さらに recipe 構成 S1–S6 と join の定理 1–3 は、それぞれの有限 graph・観測言語の範囲で独立査読を通過した。[構成と集約の outcome](../tasks/agent-loop/sprints/cooccurrence-source-20261024-outcome.md)に固定 hash と残る source/consumer 対応を記録する。

[handler 分岐の outcome](../tasks/agent-loop/sprints/correlated-handler-20261024-outcome.md)は、その次の consumer 証明 H1–H5 の査読範囲と固定 hash を記録する。有限 table の経路についての等式と、具体実行に対する片方向 inclusion を区別する。

[生成証明の outcome](../tasks/agent-loop/sprints/source-core-coverage-20261024-outcome.md)は G1–G5 の固定版と査読結果、全表層・有限 interface・foreign 契約などの残項を記録する。

- [完全 Call の receiving incidence と delayed extrusion](../notes/theory/2026-10-24-replay-receiving-occurrence-proof.md): authentic inputs の下で source placement を構成し、監査した構造公理に限る association の非含意を示す。全意味論の独立性や source 保存の反証ではない。
- [extrusion の可換性と有限使用の解の引戻し](../notes/theory/2026-10-24-replay-extrusion-commutation.md): 具体的な store の局所可換性 EC1 と occurrence の相違 EC2、任意有限回の freshening/quotient の可換性 EC3、任意有限 client 制約についての片方向の解対応 EC4 を証明する。RG-OWNER と元の全体命題は未完。[成果と査読範囲](../tasks/agent-loop/sprints/replay-receiver-proof-20261024-outcome.md)を参照。

- [同生成レベル Call の extrusion 反例](../notes/theory/2026-10-24-birth-level-extrusion-redundancy.md): 元の native grammar から、自己呼出しの反変引数が低い捕捉先へ replay され実 copy を作る有限履歴を構成する。copy-free 候補不変条件を反証し、選択された intrusion 規則自体は反証しない。
- [両極性の残余要求と source occurrence](../notes/theory/2026-10-24-residual-demand-source-association.md): positive/negative boundary の cut、改名との可換性、ScopedDemand の実保持/消費範囲を導く。source typed map と native 生成の対応は未完。[成果と査読](../tasks/agent-loop/sprints/birth-residual-closure-20261024-outcome.md)を参照。

- [source-indexed constraint の生成](../notes/theory/2026-10-24-source-indexed-constraint-derivation.md): 実 Application の operand origins、有限 obligation graph と native erasure を構成する。SC4 の Record/rebind 実現は semantic substitution の不足により撤回。既存 NameDelay の条件付き入場結果を保ち、全 Call/再帰 membership、一般 realization は未完。
- [native level 閉包と publication](../notes/theory/2026-10-24-native-level-closure-and-publication.md): 全 ordinary native 有限履歴の bound-level invariant、固定 anchor の依存閉包、実 freshening partition を導く。有限に検査できる quotient 条件の下で任意有限使用との clause 対応と解の pullback を構成し、既存の具体例へ適用する。全 source-scoped completeness の閉包とは区別する。

- [actual Return からの fresh ValueBind と Call](../notes/theory/2026-10-24-fresh-valuebind-complete-call.md): 元の Return/rebind からの新しい binding、同じ carrier の admission、全 Call phase を構成する。継承した complete invocation Comp port がある instance では元の unannotated result assignment と CIncl を与える。抽象 P_H* の source 表示、全 certificate/profile、再帰 history は残る。
- [copy 系譜による有限履歴の消去](../notes/theory/2026-10-24-copy-genealogy-history-erasure.md): 初期 bounds/source seeds の有限 closure から、全 replay/構造分解/extrusion/parent-copy quotient の comparison を導く。closure による rejection 保存と全 cut の同時 diagonal lift を構成する。fresh use をまたぐ source strategy と全体停止性は別の親義務である。[固定版と査読記録](../tasks/agent-loop/sprints/call-realization-history-20261024-outcome.md)を参照。

- [generated ReadInvoke と局所 Call typing](../notes/theory/2026-10-24-generated-call-descriptor-typing.md): 選択済み pure Name result constructor を actual h Call に適用し、HC-RESULT をその範囲で閉じる。全依存 field map・由来分割・局所 typing 関数を構成し、local profile/permission と独立 arm laws の残余を分ける。
- [captured Record wrapper の導入](../notes/theory/2026-10-24-captured-record-wrapper-introduction.md): actual x の証拠と元の独立 kernel laws から `lambda z.{a=x}` の complete Strict membership と world を構成する。creation-time capture、実 Force/rebind、潜在 field を含む result/future を保持する。[成果と査読範囲](../tasks/agent-loop/sprints/generated-call-operator-20261024-outcome.md)を参照。

- [Name Call による原再帰 instance の同時導入](../notes/theory/2026-10-24-name-call-recursive-closure-membership.md): 同じ f と各 actual inner closure を全 world/carrier/observation と同時に構成する。元の独立 kernel/formation 前提を保持した一つの monomorphic instance で、HC-REC/HISTORY に actual Return/rebind を供給する。全 source/publication/native 対応は残る。
- [native local profile の構成](../notes/theory/2026-10-24-native-local-profile-construction.md): 実 introduction と licensed field の証拠に沿って local default、inherited policy と全依存 packet を構成する。uniform local law と actual recursive membership、static policy と dynamic authority を区別する。[成果と査読範囲](../tasks/agent-loop/sprints/name-recursion-profile-20261024-outcome.md)を参照。

- [原再帰例の全 native closure model](../notes/theory/2026-10-24-explicit-recursive-native-model.md): 全 source seeds と有限 closure を一つの guarded regular-tree valuation で満たし、GE6 の model premise を具体例で除く。全 copy/cut の同時 lift と failure 排除を導く。source の full projection、publication と全体停止性とは区別する。

- [actual replay の receiving diagram](../notes/theory/2026-10-24-actual-replay-receiving-diagram.md): actual recursive Return、新しい x、capture と後の h Call を同じ全依存 event family で接続し、旧 binding を変えない middle matching を構成する。対応する Argument/Swap・Replay・T/Y 記録を保持し、native actual occurrence の receiving field との同一性は残す。[両稿の固定版と査読範囲](../tasks/agent-loop/sprints/actual-replay-model-20261024-outcome.md)を参照。

- [公開後の実二使用と逆向きモデル輸送](../notes/theory/2026-10-24-publication-reverse-coverage.md): 原 T/Y 等置の前後で全 freshening rows と App/Sel/succ 制約を比較し、共有 anchors を固定する具体的 reverse repair を構成する。actual lower demands を等式に変えない。
- [同じ外部 h/f の Int・Bool 使用](../notes/theory/2026-10-24-two-input-recursive-source-use.md): Union/Record の ground data 証拠、genuine h₀、U=Int|Bool に対する共同再帰 membership、原 Bind/Name client の full use judgments を構成する。native App syntax との全 inference 対応と一般化、資格の証明を区別する。[両稿の固定版と査読範囲](../tasks/agent-loop/sprints/publication-two-use-20261024-outcome.md)を参照。

- [有限 next 観測の全出力契約を保つ公開輸送](../notes/theory/2026-10-24-finite-next-observation-coverage.md): 任意有限 depth/branching、共有 alias、実 next upper、fixed whole output contracts について、全 node refinement と低 anchor 保存を構成する。定義した client grammar の可解性対応であり、任意 client の定理ではない。
- [有限観測の actual callee と Call phase](../notes/theory/2026-10-24-finite-observation-source-bridge.md): FO1 は元 whole-carrier checking の下で実 Return/provider と receiver phase を構成する。FO2 初稿の carrier checking 推論には MAJOR 指摘があり、χ_e family を明示した条件付き合成だけを残す。独立 computed-result descriptor、native MonoBind、χ_e の一般構成は未完。[査読と訂正](../tasks/agent-loop/sprints/finite-next-coverage-20261024-outcome.md)を参照。


- [let-free 高階 client の reverse coverage](../notes/theory/2026-10-24-let-free-client-reverse-coverage.md): 既存の一意-label regular-tree model で全有限 Lam/App/Rcd/Sel/Var/Lit clients を構造帰納し、低 anchors と出力契約を保つ。local-let/全 source 対応と区別する。この範囲で独立査読受理。
- [computed argument の whole-carrier checking](../notes/theory/2026-10-24-computed-argument-carrier-checking.md): 実 h₀/f/g の source code から有限 computed argument の全 source execution と Delay criterion を構成する。独立 arms の target-specific checking は条件として保持し、succ と独立 computed-result descriptor の未完を残す。FO2 全体の無条件閉鎖ではない。この範囲で独立査読受理。[査読記録](../tasks/agent-loop/sprints/let-free-carrier-20261024-outcome.md)を参照。


- [nonrecursive local-let の公開への接続](../notes/theory/2026-10-24-nonrecursive-let-client-coverage.md): RHS level+1、captured context への extrusion、保存 graph の freshening を検討する。具体的 captured-k client の全コピーと repair は独立査読受理。全 let-client theorem は未閉鎖。
- [computed Call の phase と訂正した Bind result](../notes/theory/2026-10-24-computed-call-bind-result.md): CB1/operational composition は受理。旧 CB2/CB3 の descriptor 橋は MAJOR により無条件主張を撤回した。[新 EvalInvoke 定義](../notes/design/2026-10-24-computed-call-result-constructor.md)が missing formation/interpretation を明示し、introduction と checked Name specialization は再査読受理し、この生成 case を選択した。固定 foreign R と native result-slot 対応は残す。[固定版と査読記録](../tasks/agent-loop/sprints/computed-result-definition-20261024-outcome.md)を参照。

- [polar copy と nested let publication](../notes/theory/2026-10-24-let-polar-publication-simulation.md): LP1 は実 selected-bound obligations、LP2 は内側 low copy が外側で high/freshened となる具体的導出。共同 repair により誤った coverage 反例を排除するが、全 Let theorem は未閉鎖。
- [generated computed result と元結果欄](../notes/theory/2026-10-24-generated-computed-result-correspondence.md): EI の定義 view を実 Call/IF に形成し、scope・共有・actual result/future の一致と、元 proof への付加・消去を構成する。独立な Comp target と CIncl を保持する。native 全 result encoding や全 target inclusion の証明ではない。両稿はこの範囲で独立査読を通過した。[固定版と査読範囲](../tasks/agent-loop/sprints/let-polar-result-slot-20261024-outcome.md)に全体未完了の境界を記録する。

- [signed updates と extrusion の段階合成](../notes/theory/2026-10-24-signed-update-extrusion-corridor.md): SU1–SU5は全finite nonrecursive-Let clientsのbound更新と両list fresheningを帰納し、Y系への後着upperを排除する。EC1/EC2は一般storeの二段→一段model transportと間の固定publicationを構成する。任意interleaved historyへの合成と全Let coverageは未完。この範囲で独立査読受理。[記録](../tasks/agent-loop/sprints/signed-extrusion-corridor-20261024-outcome.md)を参照。

## 現在読む証明稿

以下の3稿は、限定された対象について紙上導出を記す個別の原稿である。いずれも独立査読と機械検証を終えた証明として扱わない。

| 文書 | 導出の対象 | 適用範囲と未完了部分 |
| --- | --- | --- |
| [操作的意味論と型健全性](yulang-operational-type-safety-ja.tex) | 宣言的型付けを持つ操作的計算について、値・操作の応答・継続の保存と進行を扱う。有限な効果と profile を含む安全性も別の定理として導く。 | この計算についての紙上導出であり、推論器や現行コンパイラーの全対応を示さない。原稿自身がソース対応を未完としている。実行 owner と保持する receiver evidence の区別は、後続のソース稿にある訂正を適用する。 |
| [ソース導出と実行核の接続](yulang-source-type-safety-ja.tex) | 2026年10月24日時点のソースから計算への導出を扱う。実行 owner と過去の receiver evidence を分け、rank-2、scoped release、wildcard、dot selection に関する候補構成も記す。 | 単独著者の未査読・未機械化稿である。候補規則の言語仕様への採用、ソースと native 実装および現行コンパイラーとの対応は未完であり、証明 gate の閉鎖を意味しない。 |
| [dot selection の安全性](yulang-dot-selection-safety-ja.tex) | 有限な選択証拠から、選択済みコードと型付け導出を構成する。 | 操作的計算に依存する。resolver の一意性と完全性、現行コンパイラーとの対応、独立査読は未完である。ソース稿は、この選択構成の一部を統合し、関連する前提を訂正している。 |

依存関係を読むときは、操作的意味論稿を実行核の紙上結果、dot selection 稿を有限証拠からその核へ接続する構成、ソース稿をソース導出と既存の owner 規則へ戻す後続稿として扱う。先行稿の証明を後続稿の訂正後の機械へ無検査で移してはならない。

## 規範的な研究仕様

[全言語意味論と型推論の拡張稿](yulang-whole-language-semantics-ja-expanded-20261023.tex)は、全言語を対象にする規範体系を提案する研究稿である。型付き意味論、推論手順、実装との照合目標を記すが、採用済みの言語仕様や全体証明の完了報告ではない。局所 evidence を構成する義務を含む未完了部分が残る。

この仕様は証明稿として引用しない。定義や目標を確認するときに参照し、成立済みの定理や現行実装との対応を主張するときは、対応する証明稿と現在の gate 状態を別に確認する。

## 監査と現在の gate 状態

R345監査が gate 基準として hash を固定する意味論稿は、拡張稿ではなく[拡張前の稿](yulang-whole-language-semantics-ja.tex)（SHA-256 `6246e7dc179a795b372603eac8cd64bf783ba69e9a4a733bcfc012ebd6869612`）である。拡張稿への切替や採用を暗黙に示さない。

[R345更新版の全言語意味論整合監査](Yulang%20Simple-sub%20%E6%8B%A1%E5%BC%B5%EF%BC%9A%E5%85%A8言語意味論整合監査・証明設計%EF%BC%88R345更新版%EF%BC%89.md)は、証拠、実装監査、未解決 gate を整理する監査・状態資料であり、証明本文ではない。

このブランチの[agent loop の現在状態](../tasks/agent-loop/current.json)は、今回の文書・証明作業だけを記録する。分岐元 `424566114` の記録では `OP-SEMANTICS-FULL-EFFECT`、`DOT-SELECTION-EVIDENCE-BRIDGE`、`CONSTRUCTOR-POLYMORPHISM-SCOPED-RELEASE`、`SOURCE-SAFETY-BRIDGE` は `OPEN_REVIEW`、R149 は `PARTIAL_REVIEWED`、元の A/B も未完了であった。今回の局所査読はこれらを閉じない。元の実装作業場所の状態・lease は変更していない。

## 歴史的資料と安全な整理

次の文書は履歴や旧設計を調べる資料であり、現在の証明 authority ではない。

- [拡張前の全言語意味論稿](yulang-whole-language-semantics-ja.tex)
- [旧監査と crosswalk](Yulang%20Simple-sub%20%E6%8B%A1%E5%BC%B5%EF%BC%9A全体証明への移行監査・証明設計.md)、[全言語意味論整合版 crosswalk](Yulang%20Simple-sub%20%E6%8B%A1%E5%BC%B5%EF%BC%9A全体証明への移行監査・証明設計（全言語意味論整合版）.md)

旧証明コンパニオンと旧統合設計計画は、現行稿と重なる主張・訂正済みの設計説明を含むため、現行の docs から退役させた。内容を再確認するときは、[proof companion の固定版](https://github.com/momota1029/yulang/blob/8e4229bdc2d83d8fde9b38edb14f305419d5f5ea/docs/yulang-proof-companion-ja.md)と[統合設計計画の固定版](https://github.com/momota1029/yulang/blob/929f3a790b03261b28a04239fa65cfa5af5e9479/docs/yulang-unified-design-and-proof-plan-ja.md)を Git 履歴で読む。R255 と R302 の記録もこの固定版を指す。旧稿本文を現行の証明 authority として再利用しない。

拡張前の意味論稿と旧監査・crosswalk は、現行の gate が固定した入力・履歴として参照するため残す。これらは現行証明稿ではないが、A/B の元の主張、監査基準、各 gate が依拠した資料を追えるようにする。古い資料をさらに退役させる場合も、記録からの参照先と固定 hash を保つ。

現行資料の整理は次の状態にした。

1. この索引を現行の入口とし、証明3稿、規範的な研究仕様、監査・状態資料の役割を分けた。
2. 旧証明コンパニオンと統合設計計画の現行コピーを退役させ、R255/R302 の参照を固定した Git 版へ向けた。
3. gate 入力として固定された意味論稿・監査・crosswalk と、task/theory の履歴は残した。

旧 task や監査記録に使われたことは、その資料を現行の証明 authority にしない。反対に、現在の証明 authority ではないことも、gate の入力・履歴 pointer を消してよい理由にはならない。

| [Let/LetRec 元履歴の共同モデル](../notes/theory/2026-10-24-canonical-let-history-model.md) | CH0–CH7：実 recursive Z placeholder、全 copy の production witness、全元履歴の一つの canonical repair、Z projection を保つ等式追加。固定 f/P1 の有限履歴。CH0–CH7 と CH8 の低い boundary factor／freshening 保存は独立査読受理 | 別の early-intrusion 履歴との allocation/共有/event 対応、全 source A/B は未完 |
