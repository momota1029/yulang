# I52 rebase successor Step — partial implementation plan

Latest integration a44b8b310, read14:55 UTC. Stop adding old-family finite Views.
This design supersedes the earlier research priority, not its verified results.

Finite representation: fixed finite candidate fact universe, in canonical order.
Facts identify an owner's lower basis atom, upper basis atom, fixed binder fact,
or installed flag. Store a canonical sublist of facts not yet present; derive
normal-form atom lists by selecting present facts from the fixed universe.
Owner slots are fixed by the layout. No historical definitions or fresh private
slots are appended. Writing an owner updates its selected atom sets in place.

Partial executable step: an observation/compiler function returns a finite list
of proposals, each a finite list of facts. A proposal removes those facts from
remaining. A Step requires this removal to change remaining, so an unchanged
observation has no transition. The generic observer is an EXPLICIT parameter:
no all-source observer/compiler or its semantic correctness is claimed.

Measure: remaining.length strictly decreases. Prove structural Acc for every
observer, but distinguish it from Acc of a language-faithful complete kernel.
The latter needs the missing observation/installation correspondence.

Concrete I45 regression: one owner, fixed initial basis, fixed binder equations,
one proposal corresponding to the canonically transported terminal packet.
Commit once; all later identical proposals are no-ops. Relate the two reachable
states' public model projections to the old initial/positive family using the
already-proved uniform reconstruction. This supplies a genuine partial Step
with a concrete stopping regression, not a relabeling of the nonterminating
old Step. 239's complete observation bridge and general source completeness
remain open unless proved explicitly.

Representation choice: canonical remaining-fact sublists avoid function
extensionality in executable change detection. An owner-indexed bit vector is
an equivalent future alternative; no language semantics is selected here.

## Verified partial successor, 15:03 UTC
Three modules now define the real finite-state write relation and prove `Acc`
for every supplied observer by strict remaining-list length. The concrete I45
terminal observer has one eligible fixed proposal. It installs once, reaches
five fixed facts, cannot take a second step, and every positive old completed
stage projects to that terminal state. A separate theorem proves sound and
complete public-model correspondence for each completed I45 stage, preserving
all initial components 0..4 and all rows, allowing the private binder to change.

This is a partial successor, NOT a faithful general source kernel yet. The
observer is an explicit fixture table, not a proven compiler from general
inspection. Models formally assigns its else predicate to every noninitial subset; only
the two reachable fixture states have a proved correspondence, and arbitrary
intermediate subsets have no claimed language interpretation.
No simulation of all old administrative microsteps, complete constructor or
presence handling, 239 concrete correspondence, general source fixed basis,
or general semantics-preserving termination theorem is established. The proved
Acc applies to this newly defined gated relation only, not the old Step.

## Numeric and duplicate-install regression
`GeneralRebaseBudget258.Runs` counts actual new Step edges. The run length plus
remaining facts is at most the initial remaining count. Starting from initial,
there are at most basis.length steps; in the I45 fixture at most one. Rewriting
the same proposal is idempotent and `tryWrite` then returns `none`. These are
properties of the defined new relation, not an assertion that every source
observation is represented, nor a bound on old microsteps or running time.

## 次の具体的な橋（15:10 UTC の source 読取）

1. I45 の `GeneralDictionaryReportProjection257.actual_report n` は既存の
   実packet report全fieldを初期reportへ運ぶ等式である。これを固定表observer
   の提案の由来として接続するには、Report等式だけでなく planのHolds、
   ownerへのwrite、binder factをまとめた source-derived proposal certificate
   が必要。現状observeはそのcertificateを検査していない。この箇所を次に
   定義し、observerを単に常に提案する表から実観測に由来するものへ置き換える。
2. 239 の `GeneralDictionaryVersionLoopIteration239.state n` はn+4slots。
   `Round239.models_general` はcurrent journal Modelsだけでなく、当該packet
   Holdsを別前提に取る。`FamilyNovel239.bad n` はfuture upper型だけをbottom
   にし、old journalモデルと新packet未commitを分離する。この反例を無視して
   I45の5slot投影をそのまま使うことはできない。先に239の初期4成分とbinder
   条件の正確な公開射影を作り、retained upper定義除去とsource起源を確認する。
3. 一般sourceでは有限basisを返すproducer、sourceのowner/keyと固定binderの
   出所、constructor/presence consumer、および新たな真の情報が必要なときに
   提案が失われない完全性を証明する。その前に現在の有限novelty gateだけを
   「言語全体の停止性」と呼ばない。表現選択は変更可能だが、通るプログラムの
   集合を変更する決定は今回していない。

### 239 の境界候補を絞った追加読取（15:13 UTC）
`VersionLoopSource237` の実sourceは4slot、0/1がInt方程式、slot2が
Foo(slot0)、slot3がPair(slot2,slot2)。`VersionLoopInitial238.scalar_fixed /
foo_fixed / root_fixed` は任意初期rawモデルでそれぞれ固定S/F/Pとの
**Equivalent** を与える。したがって次の239断片では一般任意basisを最初から
扱うより、初期0〜3と全rowsを固定し、他の型を既存modelの値に戻す候補を
検証できる。ただしこれは未検証の候補であり、全private型を無根拠に同一視する
証明ではない。

重要な差分: `ActiveSupport258.models_iff` は型の等号を要求するが、ここで
得られるのはEquivalentだけ。これを等号としてrewriteしてはいけない。
既存 `FamilyFull238.packet_holds` は固定modelの定理なので、任意境界への
移送には raw ordinary、descriptor Fits、mode-sensitive headSchema、shared
binder FitsそれぞれのEquivalent不変性が必要。`Round239.models_general`
への入力はその全consumerを満たしてから渡す。新observerの1回だけinstallと
停止性は既存有限write関係を再利用できるが、公開対応を省略して239回帰完了と
呼ばない。この分解を次cycleの最初の具体課題にする。

### 再利用できる congruence と残るrow義務（15:14 UTC）
全consumerのEquivalent不変性はゼロから作る必要はない。
`GeneralNominalAssignmentCongruence238.Same` は各名の型Equivalentとrow等号。
`GeneralNominalVersionedPacketCongruence238.holds_iff` は任意planに適用でき、
`GeneralNominalVersionedSourceCongruence238.source_models_iff` は実到達stateの
全journalに適用できる（legacy空はreachableから導出）。ただし既存固定modelは
全rowEmptyであり、初期public境界は任意rowを許すので、そのままSameにできない。
次は `(value name, boundary name の row)` というrow-parametric固定型モデルが
239の全consumerを満たすかを先に確認する必要がある。これが通れば、初期0〜3の
Equivalentと残りの固定型等号でSameを構成し、既存congruenceを使ってcandidate
completionへ移送できる。rowを勝手にEmptyへ変更して公開境界同値を弱めない。

239の`FamilyHead238.merge_model`はlowerの同一2項unionとupperの同一2項interの
4組方程式へ展開でき、ここにはrowLe atomがない。projectionはsource3の二つの
nominal parameterを観測する。一方これだけで全journalのrow不依存は証明されず、
historical state、site、effectsまで必要である。次cycleではこの実consumer列を
先にチェックし、単に「fixtureは型だけなのでrow無関係」と仮定しない。
