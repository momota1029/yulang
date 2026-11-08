# dots cycle 2 — I-2 部分達成

開始: 2026-11-08 09:11:50 UTC / 18:11:50 JST。
基点: integration/m1-final `5fd6ffa2c2a29d6104684e7f94c425051d32885e`。
最新 standing orders と inbox I-2 ACTIVE を取得し直して開始。最大12サイクルの2回目。
公開先は `work/dots-main` のみ。integration/m1-final、yulang3、main、spec、plan、lake設定は変更しなかった。


最終コード検証: **PASS**、1147 jobs、Audit 6216 printed declarations、公理gate 82606 declarations。
117公開定理、13新Leanモジュール。本報告を含む公開対象32files。
最終コードcommit `6de46dac02f76e508eae71704c100c6a7d71c279`。
完全cold測定は同じ証明コードのa3fd16f0d（後続差分は新規草稿末尾の空行1行だけ）で
2026-11-08 09:51:19.932〜09:56:04.134 UTC、**284.203秒（4分44秒）、exit0**。
末尾空行の清掃後も全体verify PASS、48.668秒。

## 結論と境界

**T1c は部分達成のまま。外側の無条件 resolve_exact と X13〜X16 の外側PROVEDは今回も未達。**

- 実際の関連型宣言 `Right str` の value=int から、source store→ordinary 制約生成→実solver→制約の証拠に基づく Parent 引数の再構成→実 Parent 辞書という入口を構成した。empty入力の成功・辞書由来・全modelでslot=intを証明した。さらに任意の開始stateでrunがsomeを返した場合にも、argument=intかつvisible由来の実resolved辞書になることをsuccess_resolvedで証明した。呼出元がordinary atomsを手で渡す例ではない。
- ただし、元の `Parent(box 'a) where Left 'a, Right 'a` の例ではない。関連型の名前/RHS/出力binding/既知receiverが省略されており、勝手に意味論を決めなかった。既知Right-strという別の明示例で、出力slotとParent引数の対応は明示的。任意source parserからの抽出ではない。質問は `notes/questions/2026-11-08-cycle2-associated-parent-source.md`。
- source IDが同じ有限occurrenceの型成分を双方向制約で共有し、全modelで一致する橋を証明。IDは入力であり、parser/graphからのID抽出は未達。effectの同一性は主張しない。
- checked Paterson条件から固定producerの有限child閉包を実計算。そこに現れる実payloadを保存するallocatorを構成。fuel/Acc/有限宇宙を外部入力しない。ただし構文Tyの等しさによるallocatorで、別々のunknown source変数のidentityには使えない。
- 実固定passの全model exactnessと1回後の意味的安定性を証明。固定した関連型要求listのbatchにも全model exactness/意味的冪等性。これは更新に応じて新しいsource requestを生成する一般飽和driverではない。traceやatom listの構文的同一性、一般の兄弟順序独立性も主張しない。
- ordinary atomsからのscalar knownnessは明示的な両向きatomに対してのみ完全。任意の論理的帰結に対して完全ではない。矛盾stateをsolverで排除したが、Option.noneはpending/unsupported/inconsistentを区別しない。language-visible分類ではない。

## 独立に進めた作業

T7a: 既存の主要定理を正確な前提つきで再掲する文芸的Lean草稿 `MainStatementsDraft`。固定passの局所安定命題はk=1で証明。承認済み全体B4/B6 statementの形式化は未完。root Mainファイルとverify gateの許可パスに衝突があるためYulang配下に置き、質問ノートに記録。

T7b: read-only `tools/Reach.lean` で型とopaque proof bodyの定数依存を辿った。削除なし。主定理8 rootsの最終測定（112定理candidate b8312811c）: `REACH: 8 roots; 5373/82820 non-system declarations reachable`。全Audit rootsでは `REACH: 6363 roots; 40013/82820 non-system declarations reachable`、exit 0。到達しない＝不要ではない。Yulang/Audit等の運用importを残すと安全に削除できるmodule候補は0。過去snapshotとの違いは別reachability報告に区別した。

T4: `SpecConformanceIndex` にX1〜X24の状態・入口・証拠名・境界を統合。X22は新source入口の既存PROVED、旧strict入口のmismatchを混同せず。X15/16は局所のみ。今回新たに外側PROVEDにした例はない。

T3: 18個の既存定理の型を調べ、variance→nominal carrierに足りない橋を実名つきで設計ノートに整理。実装したとは主張しない。

## 未達と次の一手

1. 元のParent/Right例の関連型bindingを明示して、source graphからshared identityと関連型出力対応を導出する。既知性をimplの一意性から逆算しない。
2. 状態依存の絞り込みproducer、再生成したchildへのallocator閉包、Paterson/K2からの全飽和停止性を接続する。固定passの意味的冪等性で置き換えない。
3. EOF安定状態のlanguage-visible Classify、外側dictionary exactness、X13〜X16の実source入口をつなぐ。
4. 全体B4/B6の独立source判断自体と文芸的主定理を完成する。既存の限定的statementを全体仕様と呼ばない。

## 検証と制限

実行環境はLean 4.35.0（elan）。小単位のlocal commit、focused build、複数回の `cd lean && lake build --wfail` を実施。109定理candidateのincremental全体buildは1145 jobs PASS。当時の全109public theoremをAuditに登録。別途 `#check @...` 全109の型を出力しexit0。最初の一時型出力では未対応オプションpp.widthでexit1となり、その一時ファイルだけを修正して再実行した。

fresh検証の追跡にミスがあった。09:36:43開始の長時間sessionについて、別execのpsには見えず、終了情報未取得の段階で消失と誤判断し、09:38:39に同じworktreeで再実行した。初回は実際には継続し、両者が一時的に重複した。初回は09:41:28にexit1、284.433秒。buildに複数 `.olean` の `no such file or directory (error code: 2)`、続いてAuditとgateのYulang.olean不足が出た。重複buildによる競合と整合するが、原因をログ以上に断定しない。これは環境再作成や時間切れの確認ではない。並列重複を避けて最終検証を別途確定させた。

初回verify出力全文:
```text
verify-lean: . @ 785fd7f6a (base origin/integration/m1-final)
FAIL: lake build exit 1 (see /tmp/tmp.l43YWkCsKQ/build.out)
FAIL: Audit exit 1 (see /tmp/tmp.l43YWkCsKQ/audit.out)
ok: axioms only propext/Classical.choice/Quot.sound over 0 printed declarations
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended
FAIL: supervisor axiom gate (see /tmp/tmp.l43YWkCsKQ/gate.out)
/workspace/scratch/1d0b4aaa3394/yulang-dots-cycle2-fresh/tools/AxiomGate.lean:3:0: error: object file '/workspace/scratch/1d0b4aaa3394/yulang-dots-cycle2-fresh/lean/.lake/build/lib/lean/Yulang.olean' of module Yulang does not exist
verify-lean: FAIL

```

重複していた2回目もexit1、196.850秒（09:38:39〜09:41:56）。全文:
```text
verify-lean: . @ 785fd7f6a (base origin/integration/m1-final)
FAIL: lake build exit 1 (see /tmp/tmp.zSCxvAb9XJ/build.out)
FAIL: Audit exit 1 (see /tmp/tmp.zSCxvAb9XJ/audit.out)
ok: axioms only propext/Classical.choice/Quot.sound over 0 printed declarations
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended
FAIL: supervisor axiom gate (see /tmp/tmp.zSCxvAb9XJ/gate.out)
/workspace/scratch/1d0b4aaa3394/yulang-dots-cycle2-fresh/tools/AxiomGate.lean:3:0: error: object file '/workspace/scratch/1d0b4aaa3394/yulang-dots-cycle2-fresh/lean/.lake/build/lib/lean/Yulang.olean' of module Yulang does not exist
verify-lean: FAIL

```

単独再検証（両終了後）: commit `b8312811c`、09:43:15.705〜09:44:33.011 UTC、77.306秒、exit0。全文:
```text
verify-lean: . @ b8312811c (base origin/integration/m1-final)
ok: lake build --wfail (Build completed successfully (1146 jobs).)
ok: Audit.lean exit 0
ok: axioms only propext/Classical.choice/Quot.sound over 6211 printed declarations
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended
ok: AXIOM-GATE-PASS: 82598 declarations
verify-lean: PASS

```

## コマンド一覧と再現

```bash
git fetch origin integration/m1-final:refs/remotes/origin/integration/m1-final
git merge origin/integration/m1-final
# 各新モジュールについて
cd lean && lake build Yulang.<module> --wfail
cd lean && lake build --wfail
bash tools/verify-lean.sh . origin/integration/m1-final
cd lean && lake env lean /tmp/cycle2-types.lean
YULANG_REACH_ROOTS=/tmp/cycle2-final-roots.txt \
YULANG_REACH_OUTPUT=/tmp/cycle2-final-reach2.tsv lake env lean ../tools/Reach.lean
YULANG_REACH_ROOTS=/tmp/cycle2-audit-roots-final.txt \
YULANG_REACH_OUTPUT=/tmp/cycle2-audit-reach-final.tsv lake env lean ../tools/Reach.lean
git diff --exit-code <local-commit> origin/work/dots-main
```

Git CLIはfetch/local commitのみ。公開はGitHubアプリcontents API。開始時にwork/dots-mainの既存先頭が最新基点の祖先であることを確認し、force=falseとexpected_sha付きでworkブランチだけをfast-forward。その後はfile単位で公開。git push成功とは書かない。途中失敗しても既公開checkpointから復元できる。

独立読取レビューは既存Lean削除0、主要定理の前提保存、sourceと局所fragmentの境界を確認。新意味論の採用、既存定理の弱化、sorry/new axiom/native_decideはない。Audit/公理gateの成功はソース仕様全体の達成を意味しない。

## 中間公開

1. 約09:25、13 files、remote f7afb3bcc48bdfe40f23a4e38f0cbcb57cfa28c4 とlocal f44fdc991の全tree一致。
2. 09:31:35、累計20 files、remote f0b465be842c53201512934d718ccdba9ab08062 とlocal38859f960の全tree一致。
3. 約09:43、累計28 files、remote bc37a9bcbbee577c129a3085ead034ec605bdbd6 とlocal785fd7f6aの全tree一致。
4. 09:45:31、累計29 files、remote814930aa4c4b05b294970fcf4aa04406d1dfc50e とlocalb8312811cの全tree一致。

## 条件・制限

通常execのps表示だけでは長時間tool sessionの終了判定はできなかった。次回はsession IDとwrite_stdin結果を保持し、終了確認なしに同worktreeのbuildを再実行しない。環境再作成・time limit killは確認していない。今回の実測をプラットフォーム最大実行時間とは扱わない。使用量の枠/課金内訳はツールから確認できず不明。

standing ordersは見出し50分以内と後追加step8の50〜55分に食い違い。最新inboxの「50分近く」を尊重し、途中公開しつつ実装・独立レビュー・cold検証・適合例候補調査・回帰を続けた。待機だけで時間を埋めることはしなかった。

## 検証の追加記録

独立した完全cold worktree、b8312811c: 09:45:00.207〜09:49:36.575 UTC、276.368秒（4分36秒）、exit0。全文:
```text
verify-lean: . @ b8312811c (base origin/integration/m1-final)
ok: lake build --wfail (Build completed successfully (1146 jobs).)
ok: Audit.lean exit 0
ok: axioms only propext/Classical.choice/Quot.sound over 6211 printed declarations
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended
ok: AXIOM-GATE-PASS: 82598 declarations
verify-lean: PASS

```

最後の5定理追加後の最終コードa3fd16f0d: 09:50:15.501〜09:51:04.357 UTC、48.856秒、1147jobs、exit0。既存cacheを利用。全文:
```text
verify-lean: . @ a3fd16f0d (base origin/integration/m1-final)
ok: lake build --wfail (Build completed successfully (1147 jobs).)
ok: Audit.lean exit 0
ok: axioms only propext/Classical.choice/Quot.sound over 6216 printed declarations
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended
ok: AXIOM-GATE-PASS: 82606 declarations
verify-lean: PASS

```

### 最後の具体的exactness補強

`CommonRoleAssociatedParentExact.success_exact` は任意の開始State1を量化し、実runの成功と、元のatom全て＋slot0=intにモデルがあることの同値を証明する。successful_stateは返されたstate=extend s0intも証明する。追加の成功/knownness仮定は置かない。固定known-Right-str例だけのexactnessであり、元の未指定Right-a例や一般source判断の完了ではない。

最終は13新module、117公開定理。namespaceを追った機械的照合で全public theoremのAudit登録を確認。最終117件の#check全文出力exit0、最終1147jobs build exit0、独立3回帰を最終コードでも再検査exit0。新しいprivate helperは公理gateの対象。

### 適合例候補

確定したspec6.3〜6.5から、唯一implでも未確定型をdefaultしない、関連型と旧制約の衝突、SCCで固定したroleからfieldへ切替えない、ref内部への暗黙委譲禁止、union method owner/cast、分岐unionと期待型境界の6候補を整理。仕様本文と実在theorem名を照合し、source統合gapを明記した。新たなPROVED判定は付けていない。
# cycle 2: 117 定理の日本語主張

型と全量化子・前提の正確な表記は別添の `#check` 全文を参照。以下で「モデル」は記載した ordinary atom を満たす assignment、「同値」は該当する Common の意味的同値を指す。「保存」は出力モデルが入力制約も満たす方向であり、入力の全モデルを残すという意味ではない。

## CommonRoleSourceIdentity

任意の有限 source-ID 表 table、適切な長さの状態 state、slot、Common 計算型 assignment を対象とする。Coherent は同じ source ID の slot の型が意味的に同値であること。表自体の source 構文からの生成は前提外。

- `Yulang.CommonRoleSourceIdentity.pair_exact`: 二つの slot に生成した双方向制約を満たすことと、その二つの型の意味的同値は同値。
- `Yulang.CommonRoleSourceIdentity.mem_atoms`: atom が表の同一性制約に含まれることと、同じ source ID を持つある二つの slot の双方向制約に含まれることは同値。
- `Yulang.CommonRoleSourceIdentity.atoms_exact`: 表の全同一性制約を満たすことと Coherent は同値。
- `Yulang.CommonRoleSourceIdentity.pullback_coherent`: 任意の source ID ごとの valuation を出現 slot に引き戻した assignment は Coherent。
- `Yulang.CommonRoleSourceIdentity.pullback_satisfies`: 任意の source valuation の引き戻しは表から生成した全同一性制約を満たす。
- `Yulang.CommonRoleSourceIdentity.pair_grammar`: 任意の二つの slot の双方向制約は child、width、source-row の三つの許容文法を満たす。
- `Yulang.CommonRoleSourceIdentity.atoms_grammar`: 任意の表から生成した全同一性制約は同じ三つの許容文法を満たす。
- `Yulang.CommonRoleSourceIdentity.extend_exact`: 同一性制約を追加した状態のモデルであることと、元のモデルでありかつ Coherent であることは同値。
- `Yulang.CommonRoleSourceIdentity.consistent_exact`: 同一性追加後の実 ordinary solver が true を返すことと、元の制約を満たす Coherent な assignment が存在することは同値。
- `Yulang.CommonRoleSourceIdentity.shared_source_equivalent`: 同一性追加後の任意のモデルで、同じ source ID の二つの slot の型は同値。
- `Yulang.CommonRoleSourceIdentity.fits_shared_source`: 同じ source ID の二つの slot における任意の candidate の実現可能性は、同一性追加後の状態で一致する。
- `Yulang.CommonRoleSourceIdentity.fits_after_shared_equation`: 同じ source ID の別出現に scalar head の等式を追加した後の candidate の実現可能性は、追加前の実現可能性と head=candidate.head の連言に一致する。
- `Yulang.CommonRoleSourceIdentity.retain_source`: 表の末尾に任意の表を追加しても、保持された旧 slot の source ID は変わらない。
- `Yulang.CommonRoleSourceIdentity.retain_shared`: 表の末尾追加の前後で、保持された旧二 slot の source ID が等しいという関係は同値。
## CommonRoleAssociatedStateFlow

任意の associated 環境 env、role 宣言 roles、cores の WellFormed 証明 wf、receiver・関連名・出力 slot を持つ request q、状態 s を対象とする。Computed は ground receiver と実 assocOf の結果を scalar として読めること。一般の source 意味論全体ではない。

- `Yulang.CommonRoleAssociatedStateFlow.value_exact`: value が head を返すことと Computed q head は同値。
- `Yulang.CommonRoleAssociatedStateFlow.source_store_agrees`: 実 addAssociated の出力 Store を下げる fromSourceStore は、このモジュールの produce と同じ結果を返す。
- `Yulang.CommonRoleAssociatedStateFlow.produce_exact`: produce が out を返すことと、ある Computed な head の等式を s の出力 slot に追加すると out になることは同値。
- `Yulang.CommonRoleAssociatedStateFlow.models_exact`: head が Computed で produce が out を返すなら、任意の assignment が out を満たすことと、s を満たし出力 slot の型が head と同値であることは同値。
- `Yulang.CommonRoleAssociatedStateFlow.unknown_preserved`: receiver の argsBound が非零なら、produce は none を返す。候補が一つでも未知 receiver を選ばない。
- `Yulang.CommonRoleAssociatedStateFlow.computed_of_derivation`: AssocWellFormed、ground receiver、実 resolve の resolved、独立 AssocDerives による rhs、rhs の scalar 復号を仮定すると Computed が成立する。
- `Yulang.CommonRoleAssociatedStateFlow.unresolved_preserved`: 実 assocOf が none なら produce も none。
- `Yulang.CommonRoleAssociatedStateFlow.recollect_exact`: Computed な head があるとき、再収集結果に candidate が入ることと、元の出力 slot でその candidate が収集され head が candidate.head に等しいことは同値。
- `Yulang.CommonRoleAssociatedStateFlow.recollect_shared_exact`: 出力 slot と兄弟 slot が同じ source ID で Computed な head があるなら、同一性追加後の兄弟再収集結果への所属は、元の兄弟候補への所属と head の一致に同値。
- `Yulang.CommonRoleAssociatedStateFlow.Example.declaration_computes`: 具体的な boxImpl と Index(box str,int) の request の関連値は str として Computed。
- `Yulang.CommonRoleAssociatedStateFlow.Example.derived_narrowing`: その具体例を空状態から実行すると Left str は残り、Left int は残らない。
- `Yulang.CommonRoleAssociatedStateFlow.Example.shared_before`: source ID 7 を共有する二出現だけを持つ空状態では、任意の scalar candidate が slot 0 で実現可能。
- `Yulang.CommonRoleAssociatedStateFlow.Example.shared_declaration_narrowing`: 同じ source ID の slot 1 に関連値を生成し slot 0 を再収集する具体例で、Left str は残り Left int は残らない。
## CommonRoleOpenFiniteClosure

任意の checked Registry と structural request を対象とする。Reach は固定した局所 producer の子関係の反射推移的到達可能性であり、narrowing が新たに作る source request の閉包ではない。

- `Yulang.CommonRoleOpenFiniteClosure.mem_next`: next の子リストへの所属と実局所判断の Child 関係は同値。
- `Yulang.CommonRoleOpenFiniteClosure.closure_complete`: root から到達可能な任意の request は計算した有限 closure に含まれる。
- `Yulang.CommonRoleOpenFiniteClosure.closure_sound`: 計算した closure に含まれる任意の request は root から到達可能。
- `Yulang.CommonRoleOpenFiniteClosure.closure_exact`: closure への所属と Reach は同値。
- `Yulang.CommonRoleOpenFiniteClosure.reach_trans`: q から middle、middle から target に到達できれば q から target に到達できる。
- `Yulang.CommonRoleOpenFiniteClosure.closure_children_closed`: closure 内の request の実 Child は同じ closure に含まれる。
- `Yulang.CommonRoleOpenFiniteClosure.reachable_slots`: 到達可能な各 request には closure 内の index があり、計算した端点表で割り当て・復号した上下 slot は元の lower・upper に一致する。
## CommonRoleAssociatedBatch

任意の well-formed cores を持つ associated 環境、固定 request リスト qs、状態 s、assignment を対象とする。Obligations は各 request で Computed な scalar の出力等式。動的 request 生成や最終解決ではない。

- `Yulang.CommonRoleAssociatedBatch.advance_models`: 一 request の advance 後のモデルは、元のモデルかつその request の全 Computed head の出力等式を満たすものにちょうど一致する。
- `Yulang.CommonRoleAssociatedBatch.run_models`: 固定 batch 実行後のモデルは、元のモデルかつ全 Obligations を満たすものにちょうど一致する。
- `Yulang.CommonRoleAssociatedBatch.run_preserves`: 固定 batch 実行後の任意のモデルは元の状態のモデルでもある。
- `Yulang.CommonRoleAssociatedBatch.run_idempotent_models`: 同じ batch を二度実行した状態と一度実行した状態は、各 assignment に対して同じモデルを持つ。
- `Yulang.CommonRoleAssociatedBatch.run_permutation_models`: 二つの request リストが順列であるなら、どちらの batch 実行結果も各 assignment に対して同じモデルを持つ。
- `Yulang.CommonRoleAssociatedBatch.pending_exact`: request が pending リストに入ることと、元リストに入り Computed な head が一つもないことは同値。
- `Yulang.CommonRoleAssociatedBatch.candidate_stable`: 同じ batch を一度実行した状態と二度実行した状態で、任意の slot・candidate の実現可能性は同じ。
## CommonRoleAssociatedParentGround

ここは固定具体例のみ。Parent(box a) の子は Left a と既知 receiver の Right str、Right str の関連値は int。全宣言を含む visible を使う。未知 Right a を決定した例ではない。

- `Yulang.CommonRoleAssociatedParentGround.declarations_checked`: 具体的な全 visible 宣言に対する checkDatabase は true。
- `Yulang.CommonRoleAssociatedParentGround.declarations_wellFormed`: 具体的な visible 宣言群は WellFormed。
- `Yulang.CommonRoleAssociatedParentGround.environment_cores`: 関連値用環境の cores は全 visible 宣言群に等しい。
- `Yulang.CommonRoleAssociatedParentGround.right_wellFormed`: 関連値用環境の cores は WellFormed。
- `Yulang.CommonRoleAssociatedParentGround.right_assocWellFormed`: 具体的な関連値環境と role 宣言は AssocWellFormed。
- `Yulang.CommonRoleAssociatedParentGround.right_resolved`: その環境の実 resolve は Right str を resolved とする。
- `Yulang.CommonRoleAssociatedParentGround.right_value`: その環境の実 assocOf は Right str の関連名 0 に int を返す。
- `Yulang.CommonRoleAssociatedParentGround.equation_from_declaration`: 具体的な関連 request の出力値 int は Computed。
- `Yulang.CommonRoleAssociatedParentGround.left_int_resolved`: 全 visible 宣言における実 resolve は Left int を resolved とする。
- `Yulang.CommonRoleAssociatedParentGround.visible_right_resolved`: 全 visible 宣言における実 resolve は Right str を resolved とする。
- `Yulang.CommonRoleAssociatedParentGround.parent_int_resolved`: 全 visible 宣言における実 resolve は Parent(box int) を resolved とする。
- `Yulang.CommonRoleAssociatedParentGround.final_parent_resolved`: 具体例の finalParent は some resolved。
- `Yulang.CommonRoleAssociatedParentGround.final_dictionary_provenance`: 具体例の finalDictionary はある resolved plan を返し、その plan 中のすべての実装は visible に含まれる。
## CommonRoleOpenPassStability

任意の checked registry、外部 Allocation n、request q、状態 s、assignment を対象とする。Good は固定 structural closure の各 update と assignment の Compatible。安定性は全モデルの一致であり atom 列・trace の構文的固定点や最終選択ではない。

- `Yulang.CommonRoleOpenPassStability.good_unfold`: Good q は、q 自身の update との Compatible と、next のすべての子での Good の連言に同値。
- `Yulang.CommonRoleOpenPassStability.produce_of_model`: prepare 後の状態を満たす assignment があるなら、状態検査付き produce の子リストは structural next と一致する。
- `Yulang.CommonRoleOpenPassStability.thread_models`: 任意の worker と property について、各子・各開始状態で worker のモデルが元モデルと property の連言に一致するなら、thread 全体のモデルは元モデルと全子の property の連言に一致する。
- `Yulang.CommonRoleOpenPassStability.run_state`: 実再帰 run の返す状態は、prepare 後の状態から produce の子リストを同じ run で thread した状態に一致する。
- `Yulang.CommonRoleOpenPassStability.run_models_exact`: 実再帰 pass 後の状態を満たすことと、開始状態を満たしかつ Good q が成立することは、各 assignment について同値。
- `Yulang.CommonRoleOpenPassStability.run_semantically_idempotent`: 同じ固定 structural pass を二度実行した状態と一度実行した状態は各 assignment に対して同じモデルを持つ。
## MainStatements

既存成分定理の公開用再掲と局所安定性。承認済み B1〜B6 全体の主定理を完成したものではなく、各項の断片・入力前提に限定する。

- `Yulang.MainStatements.settled_role_exact`: 任意の checked settled registry、request、結果について、実 classify がその結果を返すことと独立 Classify 判断がその結果を導くことは同値。
- `Yulang.MainStatements.settled_role_accessible`: 任意の checked settled registry と request について実局所判断の子関係は accessible。呼出側の Acc や rank は不要。
- `Yulang.MainStatements.open_pass_exact`: 任意の checked open registry、外部 allocation、request、開始・終了状態、trace について、実 run の返値と独立 Runs 判断は同値。一回の pass に限定。
- `Yulang.MainStatements.declaration_variance_registry_exact`: 任意の DecidableEq を持つ Index/Formal、宣言 program、解析 universe、順序付き headers、結果 registry について、実生成結果との一致と独立 RegistryJudgment は同値。
- `Yulang.MainStatements.checked_cast_cost_bound`: 任意の有限 plan、check=true の証明、node、cost、実 Run の導出に対し、その cost は同じ plan から計算した budget 以下。
- `Yulang.MainStatements.optional_source_x22`: 固定 X22 source arms の制約は固定 assignment で成立し、空 record の program は 80 を返し、任意の整数 port の present program はその port を返す。旧 strict 入口は変更しない。
- `Yulang.MainStatements.current_core_principal`: 任意の元 Core term と Common 計算型 result について、空環境の現行 Core.Typing と、infer が返すある scheme をある unrestricted parameters で instantiate した型が result 以下であることは同値。
- `Yulang.MainStatements.open_pass_stabilizes`: 任意の slot 数、checked registry、外部 allocation、request、開始状態について、既存 structural pass を有限回反復すると次回と全モデルが同じになる。証明は一回後の安定性であり一般 narrowing の停止性ではない。
## CommonRoleOpenClosureAllocation

任意の checked registry と root に対し、固定 structural closure の構文 Ty から有限表を計算する。型の同じ構文は同じ slot となり、未知 source 変数の同一性を完全に表現する allocator ではない。

- `Yulang.CommonRoleOpenClosureAllocation.table_nonempty`: 計算した型表の長さは正。
- `Yulang.CommonRoleOpenClosureAllocation.decode_allocate`: 型が表に含まれるなら、その型を allocate して decode すると元の型に戻る。
- `Yulang.CommonRoleOpenClosureAllocation.allocate_injective_on_table`: 表に含まれる二つの型の allocate 結果が等しいなら、その型自体が等しい。
- `Yulang.CommonRoleOpenClosureAllocation.request_types_present`: root から到達可能な request の requestTypes に含まれる任意の型は計算した表に含まれる。
- `Yulang.CommonRoleOpenClosureAllocation.request_endpoints_present`: root から到達可能な request の lower と upper はともに表に含まれる。
- `Yulang.CommonRoleOpenClosureAllocation.production_payloads_present`: 到達可能な request の実 production が宣言と二 payload を返すなら、その二 payload は表に含まれる。
- `Yulang.CommonRoleOpenClosureAllocation.production_payloads_preserved`: 同じ production 成功前提のもとで、二 payload の allocate 後の decode はそれぞれ元の構文型に一致する。
- `Yulang.CommonRoleOpenClosureAllocation.assignment_preserved`: 任意の型解釈 interpret と表内の型について、allocate した slot の計算 assignment は元の型の interpret に一致する。
- `Yulang.CommonRoleOpenClosureAllocation.selected_prepare_exact`: 到達可能な request の Local が selected key children を導くなら、対応する実 production の宣言・二 payload が存在し key と children は一致する。任意の状態と型解釈で prepare 後のモデルは、元モデルかつ「宣言 head の names が空、または元 lower payload の解釈が元 upper payload の解釈の部分型」であることに同値。
- `Yulang.CommonRoleOpenClosureAllocation.state_children_closed`: 到達可能な request と任意の ordinary 状態に対し、実状態検査付き produce の子は root から到達可能。
- `Yulang.CommonRoleOpenClosureAllocation.run_exact`: 任意の開始・終了状態と trace に対し、計算した allocator を使う実 run の返値と同じ allocator に対する独立 Runs 判断は同値。
- `Yulang.CommonRoleOpenClosureAllocation.run_models_exact`: 計算した allocator を使う pass 後の各モデルは、元モデルかつ同じ allocator の Good を満たすものにちょうど一致する。
- `Yulang.CommonRoleOpenClosureAllocation.run_semantically_idempotent`: 計算した allocator を使う同じ pass を二度実行した状態と一度実行した状態は、各 valuation に対し同じモデルを持つ。
## CommonRoleOrdinaryKnownness

任意の n、ordinary atom リスト、slot、scalar base、Common assignment を対象とする。Evidence は var≤base と base≤var の両 atom が明示的に存在すること。推移閉包を含む全 entailment の判定ではない。materialize は対応済み int/str のみ。

- `Yulang.CommonRoleOrdinaryKnownness.upper_head_exact`: 一 atom の upperHead が base を返すことと、その atom が slot の var≤base であることは同値。
- `Yulang.CommonRoleOrdinaryKnownness.lower_head_exact`: 一 atom の lowerHead が base を返すことと、その atom が base≤slot の var であることは同値。
- `Yulang.CommonRoleOrdinaryKnownness.upper_exact`: base が上界抽出リストに含まれることと、対応する var≤base atom が元リストに含まれることは同値。
- `Yulang.CommonRoleOrdinaryKnownness.lower_exact`: base が下界抽出リストに含まれることと、対応する base≤var atom が元リストに含まれることは同値。
- `Yulang.CommonRoleOrdinaryKnownness.candidates_exact`: base が候補リストに含まれることと、その base に対する Evidence があることは同値。
- `Yulang.CommonRoleOrdinaryKnownness.detect_evidence`: detect が base を返すなら、その base に対する Evidence がある。
- `Yulang.CommonRoleOrdinaryKnownness.evidence_models`: Evidence があり assignment が全 atom を満たすなら、その slot の型は base と意味的に同値。
- `Yulang.CommonRoleOrdinaryKnownness.detect_sound`: detect が base を返し assignment が全 atom を満たすなら、その slot の型は base と意味的に同値。
- `Yulang.CommonRoleOrdinaryKnownness.detect_exists`: detect が何らかの base を返すことと、何らかの base の Evidence があることは同値。
- `Yulang.CommonRoleOrdinaryKnownness.evidence_unique`: 全 atom を満たす assignment が存在し同じ slot に二つの base の Evidence があるなら、その二つの base は等しい。
- `Yulang.CommonRoleOrdinaryKnownness.encode_scalar`: encode が term を返すなら、その term を scalar として復号した結果は元の base。
- `Yulang.CommonRoleOrdinaryKnownness.materialize_sound`: materialize が term を返し assignment が atom を満たすなら、term を復号する base が存在し、その slot の型はその base と同値。
- `Yulang.CommonRoleOrdinaryKnownness.empty_pending`: 任意の slot で空 atom リストの materialize は none。
- `Yulang.CommonRoleOrdinaryKnownness.explicit_pair_detected`: 一つの slot と base の明示的双方向等式リストから detect はその base を返す。
- `Yulang.CommonRoleOrdinaryKnownness.index_from_detected_str`: 状態の receiver slot で str が検出されるなら、実 Index 関連値 producer は出力 slot に str 等式を追加した状態を返す。
- `Yulang.CommonRoleOrdinaryKnownness.index_preserves`: produceIndex が out を返すなら、out を満たす任意の assignment は元の状態も満たす。
- `Yulang.CommonRoleOrdinaryKnownness.index_empty_pending`: 空状態の任意の receiver・output slot では produceIndex は none。
- `Yulang.CommonRoleOrdinaryKnownness.recorded_receiver_to_associated`: 空状態の receiver に str 等式を記録して produceIndex を実行すると、receiver 等式を保ち出力にも str 等式を追加した状態を返す。
- `Yulang.CommonRoleOrdinaryKnownness.checked_exact`: checkedProduceIndex が out を返すことと、produceIndex が out を返しかつ out にモデルが存在することは同値。
- `Yulang.CommonRoleOrdinaryKnownness.checked_models`: checkedProduceIndex が out を返すなら out にはモデルが存在する。
- `Yulang.CommonRoleOrdinaryKnownness.checked_preserves`: checkedProduceIndex が out を返すなら、out の任意のモデルは元の状態のモデルでもある。
- `Yulang.CommonRoleOrdinaryKnownness.inconsistent_not_accepted`: 開始状態にモデルが存在しないなら checkedProduceIndex は none。矛盾した証拠だけで成功とはしない。
## CommonRoleAssociatedParentPipeline

固定された既知 Right str の具体的宣言を、実 addAssociated→ordinary 状態→整合性検査→materialize→実親辞書生成へ接続する。出力 slot と親引数の対応は明示的であり、任意の source 構文からの自動 lowering ではない。

- `Yulang.CommonRoleAssociatedParentPipeline.run_models`: 任意の State 1 と返値 out・argument・answer について、run がその返値を返すなら out にモデルが存在する。out のすべてのモデルは入力も満たし slot 0 は int と同値で、argument が復号する scalar とも同値。任意入力の answer=resolved は主張しない。
- `Yulang.CommonRoleAssociatedParentPipeline.produced_state`: 空状態から具体的 Right str の実 source store を下げると resultState を返す。
- `Yulang.CommonRoleAssociatedParentPipeline.result_consistent`: 具体的 resultState の実 ordinary 整合性検査は true。
- `Yulang.CommonRoleAssociatedParentPipeline.result_materialized`: 具体的 resultState の slot 0 を materialize すると int を返す。
- `Yulang.CommonRoleAssociatedParentPipeline.empty_source_result`: 空状態からの run は resultState、int、ある resolved 辞書 plan を返す。その plan の全実装は visible に含まれ、resultState のすべてのモデルで slot 0 は int と同値。
## SpecConformanceIndex

対照表の構造検査。各行の説明文全体の意味的正しさをこの単一等式から導くものではない。

- `Yulang.SpecConformanceIndex.ids_exact`: 対照表 entries の ID 列はちょうど 1 から 24 までの順序付きリストに等しい。

## CommonRoleAssociatedParentSuccess

任意の開始State 1、出力out、argument、answerを量化し、唯一の追加前提は具体入口runがそのsome値を返したこと。モデル存在はrun_modelsから導くので仮定しない。

- `Yulang.CommonRoleAssociatedParentSuccess.argument_int`: 成功した返値のargumentは実際のRoles.Examples.intと等しい。
- `Yulang.CommonRoleAssociatedParentSuccess.answer_elaborate`: 成功したanswerは同じvisible宣言とparentGoal argumentに対する実RoleDictionaries.elaborateの結果と等しい。
- `Yulang.CommonRoleAssociatedParentSuccess.success_resolved`: 成功したargument=int、かつあるplanに対してanswer=.resolved planで、plan内の全implementationがvisibleに含まれる。noneの分類や一般source resolverの完全性は含まない。

## CommonRoleAssociatedParentExact

固定Right-str宣言例について任意のState 1を量化する。一般source入力に対する完全性ではない。

- `Yulang.CommonRoleAssociatedParentExact.source_generated`: 任意のsで実source storeからの生成結果はextended s（元制約にslot0=intの両向き制約を追加した状態）。
- `Yulang.CommonRoleAssociatedParentExact.materialized_int`: extended sにモデルが存在すれば、実materializerはslot0をintとして返す。
- `Yulang.CommonRoleAssociatedParentExact.run_of_models`: extended sにモデルが存在すれば、run sはそのstate、int引数、実Parent elaborateの結果を返す。
- `Yulang.CommonRoleAssociatedParentExact.success_exact`: 任意のsについてrun sがsome値を返すことと、元の全atomを満たしslot0がintと同値になるvaluationが存在することは同値。成功・knownnessを追加前提にしない。
- `Yulang.CommonRoleAssociatedParentExact.successful_state`: 任意s/out/argument/answerでrun sがそのsome返値を返すなら、outはextended sと等しい。

## 全117公開定理の型（暗黙引数も明示）

```text
@Yulang.CommonRoleSourceIdentity.pair_exact : ∀ {n : Nat} (left right : Fin n)
  (assignment : Fin n → Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model),
  Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model assignment
      (Yulang.CommonRoleSourceIdentity.pairAtoms left right) ↔
    Yulang.Common.Equivalent (Prod.fst.{0, 0} (assignment left)) (Prod.fst.{0, 0} (assignment right))
Yulang.CommonRoleSourceIdentity.mem_atoms : ∀ (table : Yulang.CommonRoleSourceIdentity.Table)
  (atom : Yulang.PresenceNormalForm.Atom (Yulang.CommonRoleSourceIdentity.Slot table)),
  Membership.mem.{0, 0} (Yulang.CommonRoleSourceIdentity.atoms table) atom ↔
    Exists.{1} fun left =>
      Exists.{1} fun right =>
        Eq.{1} (Yulang.CommonRoleSourceIdentity.source table left)
            (Yulang.CommonRoleSourceIdentity.source table right) ∧
          Membership.mem.{0, 0} (Yulang.CommonRoleSourceIdentity.pairAtoms left right) atom
Yulang.CommonRoleSourceIdentity.atoms_exact : ∀ (table : Yulang.CommonRoleSourceIdentity.Table)
  (assignment :
    Yulang.CommonRoleSourceIdentity.Slot table → Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model),
  Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model assignment (Yulang.CommonRoleSourceIdentity.atoms table) ↔
    Yulang.CommonRoleSourceIdentity.Coherent table assignment
Yulang.CommonRoleSourceIdentity.pullback_coherent : ∀ (table : Yulang.CommonRoleSourceIdentity.Table)
  (valuation : Nat → Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model),
  Yulang.CommonRoleSourceIdentity.Coherent table (Yulang.CommonRoleSourceIdentity.pullback table valuation)
Yulang.CommonRoleSourceIdentity.pullback_satisfies : ∀ (table : Yulang.CommonRoleSourceIdentity.Table)
  (valuation : Nat → Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model),
  Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model (Yulang.CommonRoleSourceIdentity.pullback table valuation)
    (Yulang.CommonRoleSourceIdentity.atoms table)
@Yulang.CommonRoleSourceIdentity.pair_grammar : ∀ {n : Nat} (left right : Fin n),
  Yulang.PresenceGeneratedChildGrammar.GoodAtoms (Yulang.CommonRoleSourceIdentity.pairAtoms left right) ∧
    Yulang.PresenceGeneratedWidth.WidthAtoms (Yulang.CommonRoleSourceIdentity.pairAtoms left right) ∧
      Yulang.PresenceSourceConstraintSupport.GoodAtoms (Yulang.CommonRoleSourceIdentity.pairAtoms left right)
Yulang.CommonRoleSourceIdentity.atoms_grammar : ∀ (table : Yulang.CommonRoleSourceIdentity.Table),
  Yulang.PresenceGeneratedChildGrammar.GoodAtoms (Yulang.CommonRoleSourceIdentity.atoms table) ∧
    Yulang.PresenceGeneratedWidth.WidthAtoms (Yulang.CommonRoleSourceIdentity.atoms table) ∧
      Yulang.PresenceSourceConstraintSupport.GoodAtoms (Yulang.CommonRoleSourceIdentity.atoms table)
Yulang.CommonRoleSourceIdentity.extend_exact : ∀ (table : Yulang.CommonRoleSourceIdentity.Table)
  (state : Yulang.CommonRoleSettledConstraints.State (List.length.{0} table))
  (assignment :
    Yulang.CommonRoleSourceIdentity.Slot table → Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model),
  Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model assignment
      (Yulang.CommonRoleSourceIdentity.extend table state).atoms ↔
    Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model assignment state.atoms ∧
      Yulang.CommonRoleSourceIdentity.Coherent table assignment
Yulang.CommonRoleSourceIdentity.consistent_exact : ∀ (table : Yulang.CommonRoleSourceIdentity.Table)
  (state : Yulang.CommonRoleSettledConstraints.State (List.length.{0} table)),
  Eq.{1} (Yulang.CommonRoleOpenPropagation.consistent (Yulang.CommonRoleSourceIdentity.extend table state)) true ↔
    Exists.{1} fun assignment =>
      Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model assignment state.atoms ∧
        Yulang.CommonRoleSourceIdentity.Coherent table assignment
Yulang.CommonRoleSourceIdentity.shared_source_equivalent : ∀ (table : Yulang.CommonRoleSourceIdentity.Table)
  (state : Yulang.CommonRoleSettledConstraints.State (List.length.{0} table))
  (assignment :
    Yulang.CommonRoleSourceIdentity.Slot table → Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model),
  Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model assignment
      (Yulang.CommonRoleSourceIdentity.extend table state).atoms →
    ∀ (left right : Yulang.CommonRoleSourceIdentity.Slot table),
      Eq.{1} (Yulang.CommonRoleSourceIdentity.source table left) (Yulang.CommonRoleSourceIdentity.source table right) →
        Yulang.Common.Equivalent (Prod.fst.{0, 0} (assignment left)) (Prod.fst.{0, 0} (assignment right))
Yulang.CommonRoleSourceIdentity.fits_shared_source : ∀ (table : Yulang.CommonRoleSourceIdentity.Table)
  (state : Yulang.CommonRoleSettledConstraints.State (List.length.{0} table))
  (left right : Yulang.CommonRoleSourceIdentity.Slot table),
  Eq.{1} (Yulang.CommonRoleSourceIdentity.source table left) (Yulang.CommonRoleSourceIdentity.source table right) →
    ∀ (candidate : Yulang.CommonRoleCandidateStateFrontier.Candidate),
      Yulang.CommonRoleCandidateStateFrontier.Fits (Yulang.CommonRoleSourceIdentity.extend table state) left candidate ↔
        Yulang.CommonRoleCandidateStateFrontier.Fits (Yulang.CommonRoleSourceIdentity.extend table state) right
          candidate
Yulang.CommonRoleSourceIdentity.fits_after_shared_equation : ∀ (table : Yulang.CommonRoleSourceIdentity.Table)
  (state : Yulang.CommonRoleSettledConstraints.State (List.length.{0} table))
  (left right : Yulang.CommonRoleSourceIdentity.Slot table),
  Eq.{1} (Yulang.CommonRoleSourceIdentity.source table left) (Yulang.CommonRoleSourceIdentity.source table right) →
    ∀ (head : Yulang.Inference.Base) (candidate : Yulang.CommonRoleCandidateStateFrontier.Candidate),
      Yulang.CommonRoleCandidateStateFrontier.Fits
          (Yulang.CommonRoleCandidateStateFrontier.extend (Yulang.CommonRoleSourceIdentity.extend table state) right
            head)
          left candidate ↔
        Yulang.CommonRoleCandidateStateFrontier.Fits (Yulang.CommonRoleSourceIdentity.extend table state) left
            candidate ∧
          Eq.{1} head candidate.head
Yulang.CommonRoleSourceIdentity.retain_source : ∀ (table extra : Yulang.CommonRoleSourceIdentity.Table)
  (slot : Yulang.CommonRoleSourceIdentity.Slot table),
  Eq.{1}
    (Yulang.CommonRoleSourceIdentity.source (HAppend.hAppend.{0, 0, 0} table extra)
      (Yulang.CommonRoleSourceIdentity.retain table extra slot))
    (Yulang.CommonRoleSourceIdentity.source table slot)
Yulang.CommonRoleSourceIdentity.retain_shared : ∀ (table extra : Yulang.CommonRoleSourceIdentity.Table)
  (left right : Yulang.CommonRoleSourceIdentity.Slot table),
  Eq.{1}
      (Yulang.CommonRoleSourceIdentity.source (HAppend.hAppend.{0, 0, 0} table extra)
        (Yulang.CommonRoleSourceIdentity.retain table extra left))
      (Yulang.CommonRoleSourceIdentity.source (HAppend.hAppend.{0, 0, 0} table extra)
        (Yulang.CommonRoleSourceIdentity.retain table extra right)) ↔
    Eq.{1} (Yulang.CommonRoleSourceIdentity.source table left) (Yulang.CommonRoleSourceIdentity.source table right)
@Yulang.CommonRoleAssociatedStateFlow.value_exact : ∀ {n : Nat} (env : Yulang.Roles.AssocEnv)
  (roles : Yulang.Roles.RoleDecls) (wf : Yulang.Roles.WellFormed env.cores)
  (q : Yulang.CommonRoleAssociatedStateFlow.Request n) (head : Yulang.Inference.Base),
  Eq.{1} (Yulang.CommonRoleAssociatedStateFlow.value env roles wf q) (some.{0} head) ↔
    Yulang.CommonRoleAssociatedStateFlow.Computed env roles wf q head
@Yulang.CommonRoleAssociatedStateFlow.source_store_agrees : ∀ {n : Nat} (env : Yulang.Roles.AssocEnv)
  (roles : Yulang.Roles.RoleDecls) (wf : Yulang.Roles.WellFormed env.cores)
  (q : Yulang.CommonRoleAssociatedStateFlow.Request n) (s : Yulang.CommonRoleSettledConstraints.State n),
  Eq.{1} (Yulang.CommonRoleAssociatedStateFlow.fromSourceStore env roles wf q s)
    (Yulang.CommonRoleAssociatedStateFlow.produce env roles wf q s)
@Yulang.CommonRoleAssociatedStateFlow.produce_exact : ∀ {n : Nat} (env : Yulang.Roles.AssocEnv)
  (roles : Yulang.Roles.RoleDecls) (wf : Yulang.Roles.WellFormed env.cores)
  (q : Yulang.CommonRoleAssociatedStateFlow.Request n) (s out : Yulang.CommonRoleSettledConstraints.State n),
  Eq.{1} (Yulang.CommonRoleAssociatedStateFlow.produce env roles wf q s) (some.{0} out) ↔
    Exists.{1} fun head =>
      Yulang.CommonRoleAssociatedStateFlow.Computed env roles wf q head ∧
        Eq.{1} (Yulang.CommonRoleCandidateStateFrontier.extend s q.output head) out
@Yulang.CommonRoleAssociatedStateFlow.models_exact : ∀ {n : Nat} (env : Yulang.Roles.AssocEnv)
  (roles : Yulang.Roles.RoleDecls) (wf : Yulang.Roles.WellFormed env.cores)
  (q : Yulang.CommonRoleAssociatedStateFlow.Request n) (s out : Yulang.CommonRoleSettledConstraints.State n)
  (head : Yulang.Inference.Base),
  Yulang.CommonRoleAssociatedStateFlow.Computed env roles wf q head →
    Eq.{1} (Yulang.CommonRoleAssociatedStateFlow.produce env roles wf q s) (some.{0} out) →
      ∀ (assignment : Fin n → Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model),
        Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model assignment out.atoms ↔
          Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model assignment s.atoms ∧
            Yulang.Common.Equivalent (Prod.fst.{0, 0} (assignment q.output))
              (Yulang.CommonSyntax.Layer.base.{0, 0} head)
@Yulang.CommonRoleAssociatedStateFlow.unknown_preserved : ∀ {n : Nat} (env : Yulang.Roles.AssocEnv)
  (roles : Yulang.Roles.RoleDecls) (wf : Yulang.Roles.WellFormed env.cores)
  (q : Yulang.CommonRoleAssociatedStateFlow.Request n) (s : Yulang.CommonRoleSettledConstraints.State n),
  Ne.{1} (Yulang.Roles.argsBound q.receiver.args) 0 →
    Eq.{1} (Yulang.CommonRoleAssociatedStateFlow.produce env roles wf q s) none.{0}
@Yulang.CommonRoleAssociatedStateFlow.computed_of_derivation : ∀ {n : Nat} (env : Yulang.Roles.AssocEnv)
  (roles : Yulang.Roles.RoleDecls) (wf : Yulang.Roles.WellFormed env.cores),
  Yulang.Roles.AssocWellFormed env roles →
    ∀ (q : Yulang.CommonRoleAssociatedStateFlow.Request n) (rhs : Yulang.Roles.Term) (head : Yulang.Inference.Base),
      Eq.{1} (Yulang.Roles.argsBound q.receiver.args) 0 →
        Eq.{1} (Yulang.Roles.resolve env.cores wf q.receiver) Yulang.Roles.Result.resolved →
          Yulang.Roles.AssocDerives env roles q.receiver q.name rhs →
            Eq.{1} (Yulang.CommonRoleAssociatedStateFlow.scalar rhs) (some.{0} head) →
              Yulang.CommonRoleAssociatedStateFlow.Computed env roles wf q head
@Yulang.CommonRoleAssociatedStateFlow.unresolved_preserved : ∀ {n : Nat} (env : Yulang.Roles.AssocEnv)
  (roles : Yulang.Roles.RoleDecls) (wf : Yulang.Roles.WellFormed env.cores)
  (q : Yulang.CommonRoleAssociatedStateFlow.Request n) (s : Yulang.CommonRoleSettledConstraints.State n),
  Eq.{1} (Yulang.Roles.assocOf env roles wf q.receiver q.name) none.{0} →
    Eq.{1} (Yulang.CommonRoleAssociatedStateFlow.produce env roles wf q s) none.{0}
@Yulang.CommonRoleAssociatedStateFlow.recollect_exact : ∀ {n : Nat} (env : Yulang.Roles.AssocEnv)
  (roles : Yulang.Roles.RoleDecls) (wf : Yulang.Roles.WellFormed env.cores)
  (q : Yulang.CommonRoleAssociatedStateFlow.Request n) (s : Yulang.CommonRoleSettledConstraints.State n)
  (head : Yulang.Inference.Base),
  Yulang.CommonRoleAssociatedStateFlow.Computed env roles wf q head →
    ∀ (visible : List.{0} Yulang.CommonRoleCandidateStateFrontier.Candidate)
      (c : Yulang.CommonRoleCandidateStateFrontier.Candidate),
      (Exists.{1} fun found =>
          Eq.{1} (Yulang.CommonRoleAssociatedStateFlow.recollect env roles wf q s visible) (some.{0} found) ∧
            Membership.mem.{0, 0} found c) ↔
        Membership.mem.{0, 0} (Yulang.CommonRoleCandidateStateFrontier.collect s q.output visible) c ∧
          Eq.{1} head c.head
Yulang.CommonRoleAssociatedStateFlow.recollect_shared_exact : ∀ (env : Yulang.Roles.AssocEnv)
  (roles : Yulang.Roles.RoleDecls) (wf : Yulang.Roles.WellFormed env.cores)
  (table : Yulang.CommonRoleSourceIdentity.Table)
  (q : Yulang.CommonRoleAssociatedStateFlow.Request (List.length.{0} table))
  (s : Yulang.CommonRoleSettledConstraints.State (List.length.{0} table)) (sibling : Fin (List.length.{0} table)),
  Eq.{1} (Yulang.CommonRoleSourceIdentity.source table sibling)
      (Yulang.CommonRoleSourceIdentity.source table q.output) →
    ∀ (head : Yulang.Inference.Base),
      Yulang.CommonRoleAssociatedStateFlow.Computed env roles wf q head →
        ∀ (visible : List.{0} Yulang.CommonRoleCandidateStateFrontier.Candidate)
          (c : Yulang.CommonRoleCandidateStateFrontier.Candidate),
          (Exists.{1} fun found =>
              Eq.{1}
                  (Yulang.CommonRoleAssociatedStateFlow.recollectAt env roles wf q
                    (Yulang.CommonRoleSourceIdentity.extend table s) sibling visible)
                  (some.{0} found) ∧
                Membership.mem.{0, 0} found c) ↔
            Membership.mem.{0, 0}
                (Yulang.CommonRoleCandidateStateFrontier.collect (Yulang.CommonRoleSourceIdentity.extend table s)
                  sibling visible)
                c ∧
              Eq.{1} head c.head
Yulang.CommonRoleAssociatedStateFlow.Example.declaration_computes : Yulang.CommonRoleAssociatedStateFlow.Computed
  (Yulang.Roles.AssocExamples.singletonEnv Yulang.Roles.AssocExamples.boxImpl) Yulang.Roles.AssocExamples.requiredRoles
  Yulang.Roles.AssocExamples.box_paterson Yulang.CommonRoleAssociatedStateFlow.Example.request Yulang.Inference.Base.str
Yulang.CommonRoleAssociatedStateFlow.Example.derived_narrowing : (Exists.{1} fun found =>
    Eq.{1} Yulang.CommonRoleAssociatedStateFlow.Example.run (some.{0} found) ∧
      Membership.mem.{0, 0} found Yulang.CommonRoleCandidateStateFrontier.leftStr) ∧
  ¬Exists.{1} fun found =>
      Eq.{1} Yulang.CommonRoleAssociatedStateFlow.Example.run (some.{0} found) ∧
        Membership.mem.{0, 0} found Yulang.CommonRoleCandidateStateFrontier.leftInt
Yulang.CommonRoleAssociatedStateFlow.Example.shared_before : ∀ (c : Yulang.CommonRoleCandidateStateFrontier.Candidate),
  Yulang.CommonRoleCandidateStateFrontier.Fits
    (Yulang.CommonRoleSourceIdentity.extend Yulang.CommonRoleAssociatedStateFlow.Example.sourceTable
      Yulang.CommonRoleSettledConstraints.State.empty)
    0 c
Yulang.CommonRoleAssociatedStateFlow.Example.shared_declaration_narrowing : (Exists.{1} fun found =>
    Eq.{1} Yulang.CommonRoleAssociatedStateFlow.Example.sharedRun (some.{0} found) ∧
      Membership.mem.{0, 0} found Yulang.CommonRoleCandidateStateFrontier.leftStr) ∧
  ¬Exists.{1} fun found =>
      Eq.{1} Yulang.CommonRoleAssociatedStateFlow.Example.sharedRun (some.{0} found) ∧
        Membership.mem.{0, 0} found Yulang.CommonRoleCandidateStateFrontier.leftInt
Yulang.CommonRoleOpenFiniteClosure.mem_next : ∀ (registry : Yulang.CommonRoleOpenProducer.Registry)
  (q child : Yulang.CommonRoleOpenProducer.Request),
  Membership.mem.{0, 0} (Yulang.CommonRoleOpenFiniteClosure.next registry q) child ↔
    Yulang.CommonRoleOutermostResolver.Child.{0} (Yulang.CommonRoleOpenProducer.Local registry.declarations) child q
Yulang.CommonRoleOpenFiniteClosure.closure_complete : ∀ (registry : Yulang.CommonRoleOpenProducer.Registry)
  (q target : Yulang.CommonRoleOpenProducer.Request),
  Yulang.CommonRoleOpenFiniteClosure.Reach registry q target →
    Membership.mem.{0, 0} (Yulang.CommonRoleOpenFiniteClosure.closure registry q) target
Yulang.CommonRoleOpenFiniteClosure.closure_sound : ∀ (registry : Yulang.CommonRoleOpenProducer.Registry)
  (q target : Yulang.CommonRoleOpenProducer.Request),
  Membership.mem.{0, 0} (Yulang.CommonRoleOpenFiniteClosure.closure registry q) target →
    Yulang.CommonRoleOpenFiniteClosure.Reach registry q target
Yulang.CommonRoleOpenFiniteClosure.closure_exact : ∀ (registry : Yulang.CommonRoleOpenProducer.Registry)
  (q target : Yulang.CommonRoleOpenProducer.Request),
  Membership.mem.{0, 0} (Yulang.CommonRoleOpenFiniteClosure.closure registry q) target ↔
    Yulang.CommonRoleOpenFiniteClosure.Reach registry q target
Yulang.CommonRoleOpenFiniteClosure.reach_trans : ∀ (registry : Yulang.CommonRoleOpenProducer.Registry)
  (q middle target : Yulang.CommonRoleOpenProducer.Request),
  Yulang.CommonRoleOpenFiniteClosure.Reach registry q middle →
    Yulang.CommonRoleOpenFiniteClosure.Reach registry middle target →
      Yulang.CommonRoleOpenFiniteClosure.Reach registry q target
Yulang.CommonRoleOpenFiniteClosure.closure_children_closed : ∀ (registry : Yulang.CommonRoleOpenProducer.Registry)
  (root q child : Yulang.CommonRoleOpenProducer.Request),
  Membership.mem.{0, 0} (Yulang.CommonRoleOpenFiniteClosure.closure registry root) q →
    Yulang.CommonRoleOutermostResolver.Child.{0} (Yulang.CommonRoleOpenProducer.Local registry.declarations) child q →
      Membership.mem.{0, 0} (Yulang.CommonRoleOpenFiniteClosure.closure registry root) child
Yulang.CommonRoleOpenFiniteClosure.reachable_slots : ∀ (registry : Yulang.CommonRoleOpenProducer.Registry)
  (root q : Yulang.CommonRoleOpenProducer.Request),
  Yulang.CommonRoleOpenFiniteClosure.Reach registry root q →
    Exists.{1} fun index =>
      Eq.{1}
          (Yulang.CommonRoleEndpointSlots.slotEndpoint
            (Yulang.CommonRoleEndpointSlots.collect (Yulang.CommonRoleOpenFiniteClosure.closure registry root))
            (Yulang.CommonRoleEndpointSlots.allocate
              (Yulang.CommonRoleEndpointSlots.collect (Yulang.CommonRoleOpenFiniteClosure.closure registry root))
              (Yulang.CommonRoleEndpointSlots.requestSource (Yulang.CommonRoleOpenFiniteClosure.closure registry root)
                index false)))
          q.lower ∧
        Eq.{1}
          (Yulang.CommonRoleEndpointSlots.slotEndpoint
            (Yulang.CommonRoleEndpointSlots.collect (Yulang.CommonRoleOpenFiniteClosure.closure registry root))
            (Yulang.CommonRoleEndpointSlots.allocate
              (Yulang.CommonRoleEndpointSlots.collect (Yulang.CommonRoleOpenFiniteClosure.closure registry root))
              (Yulang.CommonRoleEndpointSlots.requestSource (Yulang.CommonRoleOpenFiniteClosure.closure registry root)
                index true)))
          q.upper
Yulang.CommonRoleAssociatedBatch.advance_models : ∀ (env : Yulang.Roles.AssocEnv) (roles : Yulang.Roles.RoleDecls)
  (wf : Yulang.Roles.WellFormed env.cores) {n : Nat} (q : Yulang.CommonRoleAssociatedStateFlow.Request n)
  (s : Yulang.CommonRoleSettledConstraints.State n)
  (assignment : Fin n → Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model),
  Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model assignment
      (Yulang.CommonRoleAssociatedBatch.advance env roles wf q s).atoms ↔
    Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model assignment s.atoms ∧
      ∀ (head : Yulang.Inference.Base),
        Yulang.CommonRoleAssociatedStateFlow.Computed env roles wf q head →
          Yulang.Common.Equivalent (Prod.fst.{0, 0} (assignment q.output)) (Yulang.CommonSyntax.Layer.base.{0, 0} head)
Yulang.CommonRoleAssociatedBatch.run_models : ∀ (env : Yulang.Roles.AssocEnv) (roles : Yulang.Roles.RoleDecls)
  (wf : Yulang.Roles.WellFormed env.cores) {n : Nat} (qs : List.{0} (Yulang.CommonRoleAssociatedStateFlow.Request n))
  (s : Yulang.CommonRoleSettledConstraints.State n)
  (assignment : Fin n → Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model),
  Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model assignment
      (Yulang.CommonRoleAssociatedBatch.run env roles wf qs s).atoms ↔
    Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model assignment s.atoms ∧
      Yulang.CommonRoleAssociatedBatch.Obligations env roles wf qs assignment
Yulang.CommonRoleAssociatedBatch.run_preserves : ∀ (env : Yulang.Roles.AssocEnv) (roles : Yulang.Roles.RoleDecls)
  (wf : Yulang.Roles.WellFormed env.cores) {n : Nat} (qs : List.{0} (Yulang.CommonRoleAssociatedStateFlow.Request n))
  (s : Yulang.CommonRoleSettledConstraints.State n)
  (assignment : Fin n → Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model),
  Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model assignment
      (Yulang.CommonRoleAssociatedBatch.run env roles wf qs s).atoms →
    Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model assignment s.atoms
Yulang.CommonRoleAssociatedBatch.run_idempotent_models : ∀ (env : Yulang.Roles.AssocEnv)
  (roles : Yulang.Roles.RoleDecls) (wf : Yulang.Roles.WellFormed env.cores) {n : Nat}
  (qs : List.{0} (Yulang.CommonRoleAssociatedStateFlow.Request n)) (s : Yulang.CommonRoleSettledConstraints.State n)
  (assignment : Fin n → Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model),
  Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model assignment
      (Yulang.CommonRoleAssociatedBatch.run env roles wf qs
          (Yulang.CommonRoleAssociatedBatch.run env roles wf qs s)).atoms ↔
    Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model assignment
      (Yulang.CommonRoleAssociatedBatch.run env roles wf qs s).atoms
Yulang.CommonRoleAssociatedBatch.run_permutation_models : ∀ (env : Yulang.Roles.AssocEnv)
  (roles : Yulang.Roles.RoleDecls) (wf : Yulang.Roles.WellFormed env.cores) {n : Nat}
  (left right : List.{0} (Yulang.CommonRoleAssociatedStateFlow.Request n))
  (s : Yulang.CommonRoleSettledConstraints.State n),
  List.Perm.{0} left right →
    ∀ (assignment : Fin n → Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model),
      Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model assignment
          (Yulang.CommonRoleAssociatedBatch.run env roles wf left s).atoms ↔
        Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model assignment
          (Yulang.CommonRoleAssociatedBatch.run env roles wf right s).atoms
Yulang.CommonRoleAssociatedBatch.pending_exact : ∀ (env : Yulang.Roles.AssocEnv) (roles : Yulang.Roles.RoleDecls)
  (wf : Yulang.Roles.WellFormed env.cores) {n : Nat} (qs : List.{0} (Yulang.CommonRoleAssociatedStateFlow.Request n))
  (q : Yulang.CommonRoleAssociatedStateFlow.Request n),
  Membership.mem.{0, 0} (Yulang.CommonRoleAssociatedBatch.pending env roles wf qs) q ↔
    Membership.mem.{0, 0} qs q ∧
      ∀ (head : Yulang.Inference.Base), ¬Yulang.CommonRoleAssociatedStateFlow.Computed env roles wf q head
Yulang.CommonRoleAssociatedBatch.candidate_stable : ∀ (env : Yulang.Roles.AssocEnv) (roles : Yulang.Roles.RoleDecls)
  (wf : Yulang.Roles.WellFormed env.cores) {n : Nat} (qs : List.{0} (Yulang.CommonRoleAssociatedStateFlow.Request n))
  (s : Yulang.CommonRoleSettledConstraints.State n) (slot : Fin n)
  (c : Yulang.CommonRoleCandidateStateFrontier.Candidate),
  Yulang.CommonRoleCandidateStateFrontier.Fits
      (Yulang.CommonRoleAssociatedBatch.run env roles wf qs (Yulang.CommonRoleAssociatedBatch.run env roles wf qs s))
      slot c ↔
    Yulang.CommonRoleCandidateStateFrontier.Fits (Yulang.CommonRoleAssociatedBatch.run env roles wf qs s) slot c
Yulang.CommonRoleAssociatedParentGround.declarations_checked : Eq.{1}
  (Yulang.CheckedRoles.checkDatabase Yulang.CommonRoleAssociatedParentGround.visible) true
Yulang.CommonRoleAssociatedParentGround.declarations_wellFormed : Yulang.Roles.WellFormed
  Yulang.CommonRoleAssociatedParentGround.visible
Yulang.CommonRoleAssociatedParentGround.environment_cores : Eq.{1}
  Yulang.CommonRoleAssociatedParentGround.rightEnvironment.cores Yulang.CommonRoleAssociatedParentGround.visible
Yulang.CommonRoleAssociatedParentGround.right_wellFormed : Yulang.Roles.WellFormed
  Yulang.CommonRoleAssociatedParentGround.rightEnvironment.cores
Yulang.CommonRoleAssociatedParentGround.right_assocWellFormed : Yulang.Roles.AssocWellFormed
  Yulang.CommonRoleAssociatedParentGround.rightEnvironment Yulang.CommonRoleAssociatedParentGround.rightRoles
Yulang.CommonRoleAssociatedParentGround.right_resolved : Eq.{1}
  (Yulang.Roles.resolve Yulang.CommonRoleAssociatedParentGround.rightEnvironment.cores
    Yulang.CommonRoleAssociatedParentGround.right_wellFormed Yulang.CommonRoleAssociatedParentGround.rightGoal)
  Yulang.Roles.Result.resolved
Yulang.CommonRoleAssociatedParentGround.right_value : Eq.{1}
  (Yulang.Roles.assocOf Yulang.CommonRoleAssociatedParentGround.rightEnvironment
    Yulang.CommonRoleAssociatedParentGround.rightRoles Yulang.CommonRoleAssociatedParentGround.right_wellFormed
    Yulang.CommonRoleAssociatedParentGround.rightGoal 0)
  (some.{0} Yulang.Roles.Examples.int)
Yulang.CommonRoleAssociatedParentGround.equation_from_declaration : Yulang.CommonRoleAssociatedStateFlow.Computed
  Yulang.CommonRoleAssociatedParentGround.rightEnvironment Yulang.CommonRoleAssociatedParentGround.rightRoles
  Yulang.CommonRoleAssociatedParentGround.right_wellFormed Yulang.CommonRoleAssociatedParentGround.request
  Yulang.Inference.Base.int
Yulang.CommonRoleAssociatedParentGround.left_int_resolved : Eq.{1}
  (Yulang.Roles.resolve Yulang.CommonRoleAssociatedParentGround.visible
    Yulang.CommonRoleAssociatedParentGround.declarations_wellFormed
    { role := 21, args := List.cons.{0} Yulang.Roles.Examples.int List.nil.{0} })
  Yulang.Roles.Result.resolved
Yulang.CommonRoleAssociatedParentGround.visible_right_resolved : Eq.{1}
  (Yulang.Roles.resolve Yulang.CommonRoleAssociatedParentGround.visible
    Yulang.CommonRoleAssociatedParentGround.declarations_wellFormed Yulang.CommonRoleAssociatedParentGround.rightGoal)
  Yulang.Roles.Result.resolved
Yulang.CommonRoleAssociatedParentGround.parent_int_resolved : Eq.{1}
  (Yulang.Roles.resolve Yulang.CommonRoleAssociatedParentGround.visible
    Yulang.CommonRoleAssociatedParentGround.declarations_wellFormed
    (Yulang.CommonRoleAssociatedParentGround.parentGoal Yulang.Roles.Examples.int))
  Yulang.Roles.Result.resolved
Yulang.CommonRoleAssociatedParentGround.final_parent_resolved : Eq.{1}
  Yulang.CommonRoleAssociatedParentGround.finalParent (some.{0} Yulang.Roles.Result.resolved)
Yulang.CommonRoleAssociatedParentGround.final_dictionary_provenance : Exists.{1} fun plan =>
  Eq.{1} Yulang.CommonRoleAssociatedParentGround.finalDictionary
      (some.{0} (Yulang.RoleDictionaries.Answer.resolved plan)) ∧
    ∀ (implementation : Yulang.Roles.Impl),
      Membership.mem.{0, 0} plan.declarations implementation →
        Membership.mem.{0, 0} Yulang.CommonRoleAssociatedParentGround.visible implementation
@Yulang.CommonRoleOpenPassStability.good_unfold : ∀ {n : Nat} (registry : Yulang.CommonRoleOpenProducer.Registry)
  (allocate : Yulang.CommonRoleOpenPropagation.Allocation n) (q : Yulang.CommonRoleOpenProducer.Request)
  (assignment : Fin n → Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model),
  Yulang.CommonRoleOpenPassStability.Good registry allocate q assignment ↔
    Yulang.CommonRoleCandidateConstraints.Compatible
        (Yulang.CommonRoleOpenPropagation.update registry.declarations allocate q) assignment ∧
      ∀ (child : Yulang.CommonRoleOpenProducer.Request),
        Membership.mem.{0, 0} (Yulang.CommonRoleOpenFiniteClosure.next registry q) child →
          Yulang.CommonRoleOpenPassStability.Good registry allocate child assignment
@Yulang.CommonRoleOpenPassStability.produce_of_model : ∀ {n : Nat} (registry : Yulang.CommonRoleOpenProducer.Registry)
  (allocate : Yulang.CommonRoleOpenPropagation.Allocation n) (q : Yulang.CommonRoleOpenProducer.Request)
  (s : Yulang.CommonRoleSettledConstraints.State n)
  (assignment : Fin n → Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model),
  Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model assignment
      (Yulang.CommonRoleOpenPropagation.prepare registry.declarations allocate q s).atoms →
    Eq.{1}
      (Yulang.CommonRoleOpenPropagation.childList
        (Yulang.CommonRoleOpenPropagation.produce registry.declarations allocate q s))
      (Yulang.CommonRoleOpenFiniteClosure.next registry q)
@Yulang.CommonRoleOpenPassStability.thread_models.{u_1} : ∀ {n : Nat} {β : Type u_1}
  (worker :
    Yulang.CommonRoleOpenProducer.Request →
      Yulang.CommonRoleSettledConstraints.State n → Prod.{u_1, 0} β (Yulang.CommonRoleSettledConstraints.State n))
  (property : Yulang.CommonRoleOpenProducer.Request → Prop) (xs : List.{0} Yulang.CommonRoleOpenProducer.Request)
  (assignment : Fin n → Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model),
  (∀ (child : Yulang.CommonRoleOpenProducer.Request),
      Membership.mem.{0, 0} xs child →
        ∀ (before : Yulang.CommonRoleSettledConstraints.State n),
          Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model assignment
              (Prod.snd.{u_1, 0} (worker child before)).atoms ↔
            Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model assignment before.atoms ∧ property child) →
    ∀ (s : Yulang.CommonRoleSettledConstraints.State n),
      Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model assignment
          (Prod.snd.{u_1, 0} (Yulang.CommonRoleOpenThreading.thread.{0, u_1} worker xs s)).atoms ↔
        Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model assignment s.atoms ∧
          ∀ (child : Yulang.CommonRoleOpenProducer.Request), Membership.mem.{0, 0} xs child → property child
@Yulang.CommonRoleOpenPassStability.run_state : ∀ {n : Nat} (registry : Yulang.CommonRoleOpenProducer.Registry)
  (allocate : Yulang.CommonRoleOpenPropagation.Allocation n) (q : Yulang.CommonRoleOpenProducer.Request)
  (s : Yulang.CommonRoleSettledConstraints.State n),
  Eq.{1} (Prod.snd.{0, 0} (Yulang.CommonRoleOpenRecursivePass.run registry allocate q s))
    (Prod.snd.{0, 0}
      (Yulang.CommonRoleOpenThreading.thread.{0, 0} (Yulang.CommonRoleOpenRecursivePass.run registry allocate)
        (Yulang.CommonRoleOpenPropagation.childList
          (Yulang.CommonRoleOpenPropagation.produce registry.declarations allocate q s))
        (Yulang.CommonRoleOpenPropagation.prepare registry.declarations allocate q s)))
@Yulang.CommonRoleOpenPassStability.run_models_exact : ∀ {n : Nat} (registry : Yulang.CommonRoleOpenProducer.Registry)
  (allocate : Yulang.CommonRoleOpenPropagation.Allocation n) (q : Yulang.CommonRoleOpenProducer.Request)
  (s : Yulang.CommonRoleSettledConstraints.State n)
  (assignment : Fin n → Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model),
  Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model assignment
      (Prod.snd.{0, 0} (Yulang.CommonRoleOpenRecursivePass.run registry allocate q s)).atoms ↔
    Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model assignment s.atoms ∧
      Yulang.CommonRoleOpenPassStability.Good registry allocate q assignment
@Yulang.CommonRoleOpenPassStability.run_semantically_idempotent : ∀ {n : Nat}
  (registry : Yulang.CommonRoleOpenProducer.Registry) (allocate : Yulang.CommonRoleOpenPropagation.Allocation n)
  (q : Yulang.CommonRoleOpenProducer.Request) (s : Yulang.CommonRoleSettledConstraints.State n)
  (assignment : Fin n → Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model),
  Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model assignment
      (Prod.snd.{0, 0}
          (Yulang.CommonRoleOpenRecursivePass.run registry allocate q
            (Prod.snd.{0, 0} (Yulang.CommonRoleOpenRecursivePass.run registry allocate q s)))).atoms ↔
    Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model assignment
      (Prod.snd.{0, 0} (Yulang.CommonRoleOpenRecursivePass.run registry allocate q s)).atoms
@Yulang.MainStatements.settled_role_exact : ∀ {n : Nat} (registry : Yulang.CommonRoleSettledFrontier.Registry)
  (q : Yulang.CommonRoleSettledFrontier.Request n) (result : Yulang.CommonRoleOutermostResolver.Result),
  Eq.{1} (Yulang.CommonRoleSettledResolver.classify registry q) result ↔
    Yulang.CommonRoleOutermostResolver.Classify.{0} (Yulang.CommonRoleSettledFrontier.Local registry.declarations) q
      result
@Yulang.MainStatements.settled_role_accessible : ∀ {n : Nat} (registry : Yulang.CommonRoleSettledFrontier.Registry)
  (q : Yulang.CommonRoleSettledFrontier.Request n),
  Acc.{1} (Yulang.CommonRoleOutermostResolver.Child.{0} (Yulang.CommonRoleSettledFrontier.Local registry.declarations))
    q
@Yulang.MainStatements.open_pass_exact : ∀ {n : Nat} (registry : Yulang.CommonRoleOpenProducer.Registry)
  (allocate : Yulang.CommonRoleOpenPropagation.Allocation n) (q : Yulang.CommonRoleOpenProducer.Request)
  (s : Yulang.CommonRoleSettledConstraints.State n) (trace : Yulang.CommonRoleOpenRecursivePass.Trace)
  (final : Yulang.CommonRoleSettledConstraints.State n),
  Eq.{1} (Yulang.CommonRoleOpenRecursivePass.run registry allocate q s) (Prod.mk.{0, 0} trace final) ↔
    Yulang.CommonRoleOpenRecursivePass.Runs registry.declarations allocate q s trace final
@Yulang.MainStatements.declaration_variance_registry_exact : ∀ {Index Formal : Type} [inst : DecidableEq.{1} Index]
  [inst_1 : DecidableEq.{1} Formal] (program : Yulang.CommonDeclarationVarianceSyntax.Program Index Formal)
  (pool : Yulang.CommonDeclarationVarianceOccurrences.Universe Index Formal)
  (headers : List.{0} (Yulang.CommonDeclarationVarianceLowering.Header Formal))
  (result : Yulang.CommonDeclaredNominalInspection.Registry),
  Eq.{1} (Yulang.CommonDeclarationVarianceRegistry.registry program pool headers) result ↔
    Yulang.CommonDeclarationVarianceRegistry.RegistryJudgment program headers result
@Yulang.MainStatements.checked_cast_cost_bound : ∀ {n : Nat} (plan : Yulang.CommonDeclaredCastCostGraph.Plan n)
  (accepted : Eq.{1} (Yulang.CommonDeclaredCastCostGraph.check plan) true) (node : Fin n) (cost : Nat),
  Yulang.CommonDeclaredCastCost.Run plan node cost →
    LE.le.{0} cost (Yulang.CommonDeclaredCastCost.budget plan accepted node)
Yulang.MainStatements.optional_source_x22 : Yulang.Core.PresenceGeneration.Formula.Holds.{0, 0} Yulang.Common.model
    Yulang.CommonSourceOptionalX22.assignment
    (Yulang.CommonSourceArmsSolved.principal List.nil.{0} Yulang.CommonSourceOptionalX22.arms) ∧
  Eq.{1}
      (Yulang.EvaluationTrace.Logged.result.{0, 0, 0}
        (Yulang.ScopedCaseDataProgram.eval Empty.elim.{1} List.nil.{0} Yulang.CommonSourceOptionalX22.absentProgram))
      (Except.ok.{0, 0}
        (some.{0} (Yulang.CaseValues.Value.literal Empty (Yulang.LiteralValues.Literal.int Empty 80)))) ∧
    ∀ (port : Int),
      Eq.{1}
        (Yulang.EvaluationTrace.Logged.result.{0, 0, 0}
          (Yulang.ScopedCaseDataProgram.eval Empty.elim.{1} List.nil.{0}
            (Yulang.CommonSourceOptionalX22.presentProgram port)))
        (Except.ok.{0, 0}
          (some.{0} (Yulang.CaseValues.Value.literal Empty (Yulang.LiteralValues.Literal.int Empty port))))
Yulang.MainStatements.current_core_principal : ∀ (expression : Yulang.Core.Required.Term)
  (result : Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model),
  Yulang.Core.Typing (Yulang.Core.CommonSyntax.model Yulang.Common.model) List.nil.{0} expression result ↔
    Exists.{1} fun scheme =>
      Membership.mem.{0, 0} (Yulang.Core.infer expression) scheme ∧
        Exists.{1} fun parameters =>
          Yulang.Core.PresenceGeneration.Comp.le.{0, 0} Yulang.Common.model (scheme.instantiate parameters) result
Yulang.MainStatements.open_pass_stabilizes : Yulang.MainStatements.OpenPassSemanticStabilization
Yulang.CommonRoleOpenClosureAllocation.table_nonempty : ∀ (registry : Yulang.CommonRoleOpenProducer.Registry)
  (root : Yulang.CommonRoleOpenProducer.Request),
  LT.lt.{0} 0 (List.length.{0} (Yulang.CommonRoleOpenClosureAllocation.table registry root))
Yulang.CommonRoleOpenClosureAllocation.decode_allocate : ∀ (registry : Yulang.CommonRoleOpenProducer.Registry)
  (root : Yulang.CommonRoleOpenProducer.Request) (type : Yulang.CommonRoleSettledSyntax.Ty),
  Membership.mem.{0, 0} (Yulang.CommonRoleOpenClosureAllocation.table registry root) type →
    Eq.{1}
      (Yulang.CommonRoleOpenClosureAllocation.decode registry root
        (Yulang.CommonRoleOpenClosureAllocation.allocate registry root type))
      type
Yulang.CommonRoleOpenClosureAllocation.allocate_injective_on_table : ∀
  (registry : Yulang.CommonRoleOpenProducer.Registry) (root : Yulang.CommonRoleOpenProducer.Request)
  (left right : Yulang.CommonRoleSettledSyntax.Ty),
  Membership.mem.{0, 0} (Yulang.CommonRoleOpenClosureAllocation.table registry root) left →
    Membership.mem.{0, 0} (Yulang.CommonRoleOpenClosureAllocation.table registry root) right →
      Eq.{1} (Yulang.CommonRoleOpenClosureAllocation.allocate registry root left)
          (Yulang.CommonRoleOpenClosureAllocation.allocate registry root right) →
        Eq.{1} left right
Yulang.CommonRoleOpenClosureAllocation.request_types_present : ∀ (registry : Yulang.CommonRoleOpenProducer.Registry)
  (root q : Yulang.CommonRoleOpenProducer.Request),
  Yulang.CommonRoleOpenFiniteClosure.Reach registry root q →
    ∀ (type : Yulang.CommonRoleSettledSyntax.Ty),
      Membership.mem.{0, 0} (Yulang.CommonRoleOpenClosureAllocation.requestTypes registry q) type →
        Membership.mem.{0, 0} (Yulang.CommonRoleOpenClosureAllocation.table registry root) type
Yulang.CommonRoleOpenClosureAllocation.request_endpoints_present : ∀ (registry : Yulang.CommonRoleOpenProducer.Registry)
  (root q : Yulang.CommonRoleOpenProducer.Request),
  Yulang.CommonRoleOpenFiniteClosure.Reach registry root q →
    Membership.mem.{0, 0} (Yulang.CommonRoleOpenClosureAllocation.table registry root) q.lower ∧
      Membership.mem.{0, 0} (Yulang.CommonRoleOpenClosureAllocation.table registry root) q.upper
Yulang.CommonRoleOpenClosureAllocation.production_payloads_present : ∀
  (registry : Yulang.CommonRoleOpenProducer.Registry) (root q : Yulang.CommonRoleOpenProducer.Request),
  Yulang.CommonRoleOpenFiniteClosure.Reach registry root q →
    ∀ (d : Yulang.CommonRoleSettledSyntax.Declaration) (lower upper : Yulang.CommonRoleSettledSyntax.Ty),
      Eq.{1} (Yulang.CommonRoleOpenProducer.production registry.declarations q)
          (some.{0} (Prod.mk.{0, 0} d (Prod.mk.{0, 0} lower upper))) →
        Membership.mem.{0, 0} (Yulang.CommonRoleOpenClosureAllocation.table registry root) lower ∧
          Membership.mem.{0, 0} (Yulang.CommonRoleOpenClosureAllocation.table registry root) upper
Yulang.CommonRoleOpenClosureAllocation.production_payloads_preserved : ∀
  (registry : Yulang.CommonRoleOpenProducer.Registry) (root q : Yulang.CommonRoleOpenProducer.Request),
  Yulang.CommonRoleOpenFiniteClosure.Reach registry root q →
    ∀ (d : Yulang.CommonRoleSettledSyntax.Declaration) (lower upper : Yulang.CommonRoleSettledSyntax.Ty),
      Eq.{1} (Yulang.CommonRoleOpenProducer.production registry.declarations q)
          (some.{0} (Prod.mk.{0, 0} d (Prod.mk.{0, 0} lower upper))) →
        Eq.{1}
            (Yulang.CommonRoleOpenClosureAllocation.decode registry root
              (Yulang.CommonRoleOpenClosureAllocation.allocate registry root lower))
            lower ∧
          Eq.{1}
            (Yulang.CommonRoleOpenClosureAllocation.decode registry root
              (Yulang.CommonRoleOpenClosureAllocation.allocate registry root upper))
            upper
@Yulang.CommonRoleOpenClosureAllocation.assignment_preserved.{u_1} : ∀ {α : Sort u_1}
  (registry : Yulang.CommonRoleOpenProducer.Registry) (root : Yulang.CommonRoleOpenProducer.Request)
  (interpret : Yulang.CommonRoleSettledSyntax.Ty → α) (type : Yulang.CommonRoleSettledSyntax.Ty),
  Membership.mem.{0, 0} (Yulang.CommonRoleOpenClosureAllocation.table registry root) type →
    Eq.{u_1}
      (Yulang.CommonRoleOpenClosureAllocation.assignment.{u_1} registry root interpret
        (Yulang.CommonRoleOpenClosureAllocation.allocate registry root type))
      (interpret type)
Yulang.CommonRoleOpenClosureAllocation.selected_prepare_exact : ∀ (registry : Yulang.CommonRoleOpenProducer.Registry)
  (root q : Yulang.CommonRoleOpenProducer.Request),
  Yulang.CommonRoleOpenFiniteClosure.Reach registry root q →
    ∀ (key : Nat) (cs : List.{0} Yulang.CommonRoleOpenProducer.Request),
      Yulang.CommonRoleOpenProducer.Local registry.declarations q
          (Yulang.CommonRoleOutermostResolver.Frontier.selected.{0} key cs) →
        ∀
          (s :
            Yulang.CommonRoleSettledConstraints.State
              (List.length.{0} (Yulang.CommonRoleOpenClosureAllocation.table registry root)))
          (interpret :
            Yulang.CommonRoleSettledSyntax.Ty → Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model),
          Exists.{1} fun d =>
            Exists.{1} fun lower =>
              Exists.{1} fun upper =>
                Eq.{1} (Yulang.CommonRoleOpenProducer.production registry.declarations q)
                    (some.{0} (Prod.mk.{0, 0} d (Prod.mk.{0, 0} lower upper))) ∧
                  Eq.{1} key d.key ∧
                    Eq.{1} cs (Yulang.CommonRoleOpenProducer.children q d lower upper) ∧
                      (Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model
                          (Yulang.CommonRoleOpenClosureAllocation.assignment.{1} registry root interpret)
                          (Yulang.CommonRoleOpenPropagation.prepare registry.declarations
                              (Yulang.CommonRoleOpenClosureAllocation.allocate registry root) q s).atoms ↔
                        Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model
                            (Yulang.CommonRoleOpenClosureAllocation.assignment.{1} registry root interpret) s.atoms ∧
                          (Eq.{1} d.head.names List.nil.{0} ∨
                            Yulang.Common.Subtype (Prod.fst.{0, 0} (interpret lower))
                              (Prod.fst.{0, 0} (interpret upper))))
Yulang.CommonRoleOpenClosureAllocation.state_children_closed : ∀ (registry : Yulang.CommonRoleOpenProducer.Registry)
  (root q child : Yulang.CommonRoleOpenProducer.Request),
  Yulang.CommonRoleOpenFiniteClosure.Reach registry root q →
    ∀
      (s :
        Yulang.CommonRoleSettledConstraints.State
          (List.length.{0} (Yulang.CommonRoleOpenClosureAllocation.table registry root))),
      Membership.mem.{0, 0}
          (Yulang.CommonRoleOpenPropagation.childList
            (Yulang.CommonRoleOpenPropagation.produce registry.declarations
              (Yulang.CommonRoleOpenClosureAllocation.allocate registry root) q s))
          child →
        Membership.mem.{0, 0} (Yulang.CommonRoleOpenFiniteClosure.closure registry root) child
Yulang.CommonRoleOpenClosureAllocation.run_exact : ∀ (registry : Yulang.CommonRoleOpenProducer.Registry)
  (root : Yulang.CommonRoleOpenProducer.Request)
  (s final :
    Yulang.CommonRoleSettledConstraints.State
      (List.length.{0} (Yulang.CommonRoleOpenClosureAllocation.table registry root)))
  (trace : Yulang.CommonRoleOpenRecursivePass.Trace),
  Eq.{1} (Yulang.CommonRoleOpenClosureAllocation.run registry root s) (Prod.mk.{0, 0} trace final) ↔
    Yulang.CommonRoleOpenRecursivePass.Runs registry.declarations
      (Yulang.CommonRoleOpenClosureAllocation.allocate registry root) root s trace final
Yulang.CommonRoleOpenClosureAllocation.run_models_exact : ∀ (registry : Yulang.CommonRoleOpenProducer.Registry)
  (root : Yulang.CommonRoleOpenProducer.Request)
  (s :
    Yulang.CommonRoleSettledConstraints.State
      (List.length.{0} (Yulang.CommonRoleOpenClosureAllocation.table registry root)))
  (valuation :
    Fin (List.length.{0} (Yulang.CommonRoleOpenClosureAllocation.table registry root)) →
      Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model),
  Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model valuation
      (Prod.snd.{0, 0} (Yulang.CommonRoleOpenClosureAllocation.run registry root s)).atoms ↔
    Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model valuation s.atoms ∧
      Yulang.CommonRoleOpenPassStability.Good registry (Yulang.CommonRoleOpenClosureAllocation.allocate registry root)
        root valuation
Yulang.CommonRoleOpenClosureAllocation.run_semantically_idempotent : ∀
  (registry : Yulang.CommonRoleOpenProducer.Registry) (root : Yulang.CommonRoleOpenProducer.Request)
  (s :
    Yulang.CommonRoleSettledConstraints.State
      (List.length.{0} (Yulang.CommonRoleOpenClosureAllocation.table registry root)))
  (valuation :
    Fin (List.length.{0} (Yulang.CommonRoleOpenClosureAllocation.table registry root)) →
      Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model),
  Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model valuation
      (Prod.snd.{0, 0}
          (Yulang.CommonRoleOpenClosureAllocation.run registry root
            (Prod.snd.{0, 0} (Yulang.CommonRoleOpenClosureAllocation.run registry root s)))).atoms ↔
    Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model valuation
      (Prod.snd.{0, 0} (Yulang.CommonRoleOpenClosureAllocation.run registry root s)).atoms
@Yulang.CommonRoleOrdinaryKnownness.upper_head_exact : ∀ {n : Nat} (slot : Fin n)
  (atom : Yulang.PresenceNormalForm.Atom (Fin n)) (base : Yulang.Inference.Base),
  Eq.{1} (Yulang.CommonRoleOrdinaryKnownness.upperHead slot atom) (some.{0} base) ↔
    Eq.{1} atom
      (Yulang.PresenceNormalForm.Atom.tyLe (Yulang.Core.PresenceGeneration.TyTerm.var slot)
        (Yulang.Core.PresenceGeneration.TyTerm.base base))
@Yulang.CommonRoleOrdinaryKnownness.lower_head_exact : ∀ {n : Nat} (slot : Fin n)
  (atom : Yulang.PresenceNormalForm.Atom (Fin n)) (base : Yulang.Inference.Base),
  Eq.{1} (Yulang.CommonRoleOrdinaryKnownness.lowerHead slot atom) (some.{0} base) ↔
    Eq.{1} atom
      (Yulang.PresenceNormalForm.Atom.tyLe (Yulang.Core.PresenceGeneration.TyTerm.base base)
        (Yulang.Core.PresenceGeneration.TyTerm.var slot))
@Yulang.CommonRoleOrdinaryKnownness.upper_exact : ∀ {n : Nat}
  (atoms : List.{0} (Yulang.PresenceNormalForm.Atom (Fin n))) (slot : Fin n) (base : Yulang.Inference.Base),
  Membership.mem.{0, 0} (Yulang.CommonRoleOrdinaryKnownness.upper atoms slot) base ↔
    Membership.mem.{0, 0} atoms
      (Yulang.PresenceNormalForm.Atom.tyLe (Yulang.Core.PresenceGeneration.TyTerm.var slot)
        (Yulang.Core.PresenceGeneration.TyTerm.base base))
@Yulang.CommonRoleOrdinaryKnownness.lower_exact : ∀ {n : Nat}
  (atoms : List.{0} (Yulang.PresenceNormalForm.Atom (Fin n))) (slot : Fin n) (base : Yulang.Inference.Base),
  Membership.mem.{0, 0} (Yulang.CommonRoleOrdinaryKnownness.lower atoms slot) base ↔
    Membership.mem.{0, 0} atoms
      (Yulang.PresenceNormalForm.Atom.tyLe (Yulang.Core.PresenceGeneration.TyTerm.base base)
        (Yulang.Core.PresenceGeneration.TyTerm.var slot))
@Yulang.CommonRoleOrdinaryKnownness.candidates_exact : ∀ {n : Nat}
  (atoms : List.{0} (Yulang.PresenceNormalForm.Atom (Fin n))) (slot : Fin n) (base : Yulang.Inference.Base),
  Membership.mem.{0, 0} (Yulang.CommonRoleOrdinaryKnownness.candidates atoms slot) base ↔
    Yulang.CommonRoleOrdinaryKnownness.Evidence atoms slot base
@Yulang.CommonRoleOrdinaryKnownness.detect_evidence : ∀ {n : Nat}
  (atoms : List.{0} (Yulang.PresenceNormalForm.Atom (Fin n))) (slot : Fin n) (base : Yulang.Inference.Base),
  Eq.{1} (Yulang.CommonRoleOrdinaryKnownness.detect atoms slot) (some.{0} base) →
    Yulang.CommonRoleOrdinaryKnownness.Evidence atoms slot base
@Yulang.CommonRoleOrdinaryKnownness.evidence_models : ∀ {n : Nat}
  (atoms : List.{0} (Yulang.PresenceNormalForm.Atom (Fin n))) (slot : Fin n) (base : Yulang.Inference.Base),
  Yulang.CommonRoleOrdinaryKnownness.Evidence atoms slot base →
    ∀ (assignment : Fin n → Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model),
      Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model assignment atoms →
        Yulang.Common.Equivalent (Prod.fst.{0, 0} (assignment slot)) (Yulang.CommonSyntax.Layer.base.{0, 0} base)
@Yulang.CommonRoleOrdinaryKnownness.detect_sound : ∀ {n : Nat}
  (atoms : List.{0} (Yulang.PresenceNormalForm.Atom (Fin n))) (slot : Fin n) (base : Yulang.Inference.Base),
  Eq.{1} (Yulang.CommonRoleOrdinaryKnownness.detect atoms slot) (some.{0} base) →
    ∀ (assignment : Fin n → Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model),
      Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model assignment atoms →
        Yulang.Common.Equivalent (Prod.fst.{0, 0} (assignment slot)) (Yulang.CommonSyntax.Layer.base.{0, 0} base)
@Yulang.CommonRoleOrdinaryKnownness.detect_exists : ∀ {n : Nat}
  (atoms : List.{0} (Yulang.PresenceNormalForm.Atom (Fin n))) (slot : Fin n),
  (Exists.{1} fun base => Eq.{1} (Yulang.CommonRoleOrdinaryKnownness.detect atoms slot) (some.{0} base)) ↔
    Exists.{1} fun base => Yulang.CommonRoleOrdinaryKnownness.Evidence atoms slot base
@Yulang.CommonRoleOrdinaryKnownness.evidence_unique : ∀ {n : Nat}
  (atoms : List.{0} (Yulang.PresenceNormalForm.Atom (Fin n))) (slot : Fin n)
  (assignment : Fin n → Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model),
  Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model assignment atoms →
    ∀ (first last : Yulang.Inference.Base),
      Yulang.CommonRoleOrdinaryKnownness.Evidence atoms slot first →
        Yulang.CommonRoleOrdinaryKnownness.Evidence atoms slot last → Eq.{1} first last
Yulang.CommonRoleOrdinaryKnownness.encode_scalar : ∀ (base : Yulang.Inference.Base) (term : Yulang.Roles.Term),
  Eq.{1} (Yulang.CommonRoleOrdinaryKnownness.encode base) (some.{0} term) →
    Eq.{1} (Yulang.CommonRoleAssociatedStateFlow.scalar term) (some.{0} base)
@Yulang.CommonRoleOrdinaryKnownness.materialize_sound : ∀ {n : Nat}
  (atoms : List.{0} (Yulang.PresenceNormalForm.Atom (Fin n))) (slot : Fin n) (term : Yulang.Roles.Term),
  Eq.{1} (Yulang.CommonRoleOrdinaryKnownness.materialize atoms slot) (some.{0} term) →
    ∀ (assignment : Fin n → Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model),
      Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model assignment atoms →
        Exists.{1} fun base =>
          Eq.{1} (Yulang.CommonRoleAssociatedStateFlow.scalar term) (some.{0} base) ∧
            Yulang.Common.Equivalent (Prod.fst.{0, 0} (assignment slot)) (Yulang.CommonSyntax.Layer.base.{0, 0} base)
@Yulang.CommonRoleOrdinaryKnownness.empty_pending : ∀ {n : Nat} (slot : Fin n),
  Eq.{1} (Yulang.CommonRoleOrdinaryKnownness.materialize List.nil.{0} slot) none.{0}
@Yulang.CommonRoleOrdinaryKnownness.explicit_pair_detected : ∀ {n : Nat} (slot : Fin n) (base : Yulang.Inference.Base),
  Eq.{1} (Yulang.CommonRoleOrdinaryKnownness.detect (Yulang.CommonRoleCandidateStateFrontier.equality slot base) slot)
    (some.{0} base)
@Yulang.CommonRoleOrdinaryKnownness.index_from_detected_str : ∀ {n : Nat}
  (s : Yulang.CommonRoleSettledConstraints.State n) (receiver output : Fin n),
  Eq.{1} (Yulang.CommonRoleOrdinaryKnownness.detect s.atoms receiver) (some.{0} Yulang.Inference.Base.str) →
    Eq.{1} (Yulang.CommonRoleOrdinaryKnownness.produceIndex s receiver output)
      (some.{0} (Yulang.CommonRoleCandidateStateFrontier.extend s output Yulang.Inference.Base.str))
@Yulang.CommonRoleOrdinaryKnownness.index_preserves : ∀ {n : Nat} (s out : Yulang.CommonRoleSettledConstraints.State n)
  (receiver output : Fin n),
  Eq.{1} (Yulang.CommonRoleOrdinaryKnownness.produceIndex s receiver output) (some.{0} out) →
    ∀ (assignment : Fin n → Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model),
      Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model assignment out.atoms →
        Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model assignment s.atoms
@Yulang.CommonRoleOrdinaryKnownness.index_empty_pending : ∀ {n : Nat} (receiver output : Fin n),
  Eq.{1}
    (Yulang.CommonRoleOrdinaryKnownness.produceIndex Yulang.CommonRoleSettledConstraints.State.empty receiver output)
    none.{0}
@Yulang.CommonRoleOrdinaryKnownness.recorded_receiver_to_associated : ∀ {n : Nat} (receiver output : Fin n),
  Eq.{1}
    (Yulang.CommonRoleOrdinaryKnownness.produceIndex
      (Yulang.CommonRoleCandidateStateFrontier.extend Yulang.CommonRoleSettledConstraints.State.empty receiver
        Yulang.Inference.Base.str)
      receiver output)
    (some.{0}
      (Yulang.CommonRoleCandidateStateFrontier.extend
        (Yulang.CommonRoleCandidateStateFrontier.extend Yulang.CommonRoleSettledConstraints.State.empty receiver
          Yulang.Inference.Base.str)
        output Yulang.Inference.Base.str))
@Yulang.CommonRoleOrdinaryKnownness.checked_exact : ∀ {n : Nat} (s out : Yulang.CommonRoleSettledConstraints.State n)
  (receiver output : Fin n),
  Eq.{1} (Yulang.CommonRoleOrdinaryKnownness.checkedProduceIndex s receiver output) (some.{0} out) ↔
    Eq.{1} (Yulang.CommonRoleOrdinaryKnownness.produceIndex s receiver output) (some.{0} out) ∧ out.Models
@Yulang.CommonRoleOrdinaryKnownness.checked_models : ∀ {n : Nat} (s out : Yulang.CommonRoleSettledConstraints.State n)
  (receiver output : Fin n),
  Eq.{1} (Yulang.CommonRoleOrdinaryKnownness.checkedProduceIndex s receiver output) (some.{0} out) → out.Models
@Yulang.CommonRoleOrdinaryKnownness.checked_preserves : ∀ {n : Nat}
  (s out : Yulang.CommonRoleSettledConstraints.State n) (receiver output : Fin n),
  Eq.{1} (Yulang.CommonRoleOrdinaryKnownness.checkedProduceIndex s receiver output) (some.{0} out) →
    ∀ (assignment : Fin n → Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model),
      Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model assignment out.atoms →
        Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model assignment s.atoms
@Yulang.CommonRoleOrdinaryKnownness.inconsistent_not_accepted : ∀ {n : Nat}
  (s : Yulang.CommonRoleSettledConstraints.State n) (receiver output : Fin n),
  ¬s.Models → Eq.{1} (Yulang.CommonRoleOrdinaryKnownness.checkedProduceIndex s receiver output) none.{0}
Yulang.CommonRoleAssociatedParentPipeline.run_models : ∀ (s out : Yulang.CommonRoleSettledConstraints.State 1)
  (argument : Yulang.Roles.Term) (answer : Yulang.RoleDictionaries.Answer),
  Eq.{1} (Yulang.CommonRoleAssociatedParentPipeline.run s)
      (some.{0} (Prod.mk.{0, 0} out (Prod.mk.{0, 0} argument answer))) →
    out.Models ∧
      ∀ (valuation : Fin 1 → Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model),
        Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model valuation out.atoms →
          Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model valuation s.atoms ∧
            Yulang.Common.Equivalent (Prod.fst.{0, 0} (valuation 0))
                (Yulang.CommonSyntax.Layer.base.{0, 0} Yulang.Inference.Base.int) ∧
              Exists.{1} fun base =>
                Eq.{1} (Yulang.CommonRoleAssociatedStateFlow.scalar argument) (some.{0} base) ∧
                  Yulang.Common.Equivalent (Prod.fst.{0, 0} (valuation 0)) (Yulang.CommonSyntax.Layer.base.{0, 0} base)
Yulang.CommonRoleAssociatedParentPipeline.produced_state : Eq.{1}
  (Yulang.CommonRoleAssociatedStateFlow.fromSourceStore Yulang.CommonRoleAssociatedParentGround.rightEnvironment
    Yulang.CommonRoleAssociatedParentGround.rightRoles Yulang.CommonRoleAssociatedParentGround.right_wellFormed
    Yulang.CommonRoleAssociatedParentGround.request Yulang.CommonRoleSettledConstraints.State.empty)
  (some.{0} Yulang.CommonRoleAssociatedParentPipeline.resultState)
Yulang.CommonRoleAssociatedParentPipeline.result_consistent : Eq.{1}
  (Yulang.CommonRoleOpenPropagation.consistent Yulang.CommonRoleAssociatedParentPipeline.resultState) true
Yulang.CommonRoleAssociatedParentPipeline.result_materialized : Eq.{1}
  (Yulang.CommonRoleOrdinaryKnownness.materialize Yulang.CommonRoleAssociatedParentPipeline.resultState.atoms 0)
  (some.{0} Yulang.Roles.Examples.int)
Yulang.CommonRoleAssociatedParentPipeline.empty_source_result : Exists.{1} fun plan =>
  Eq.{1} (Yulang.CommonRoleAssociatedParentPipeline.run Yulang.CommonRoleSettledConstraints.State.empty)
      (some.{0}
        (Prod.mk.{0, 0} Yulang.CommonRoleAssociatedParentPipeline.resultState
          (Prod.mk.{0, 0} Yulang.Roles.Examples.int (Yulang.RoleDictionaries.Answer.resolved plan)))) ∧
    (∀ (implementation : Yulang.Roles.Impl),
        Membership.mem.{0, 0} plan.declarations implementation →
          Membership.mem.{0, 0} Yulang.CommonRoleAssociatedParentGround.visible implementation) ∧
      ∀ (valuation : Fin 1 → Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model),
        Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model valuation
            Yulang.CommonRoleAssociatedParentPipeline.resultState.atoms →
          Yulang.Common.Equivalent (Prod.fst.{0, 0} (valuation 0))
            (Yulang.CommonSyntax.Layer.base.{0, 0} Yulang.Inference.Base.int)
Yulang.SpecConformanceIndex.ids_exact : Eq.{1}
  (List.map.{0, 0} Yulang.SpecConformanceIndex.Entry.id Yulang.SpecConformanceIndex.entries) (List.range' 1 24)
Yulang.CommonRoleAssociatedParentSuccess.argument_int : ∀ (s out : Yulang.CommonRoleSettledConstraints.State 1)
  (argument : Yulang.Roles.Term) (answer : Yulang.RoleDictionaries.Answer),
  Eq.{1} (Yulang.CommonRoleAssociatedParentPipeline.run s)
      (some.{0} (Prod.mk.{0, 0} out (Prod.mk.{0, 0} argument answer))) →
    Eq.{1} argument Yulang.Roles.Examples.int
Yulang.CommonRoleAssociatedParentSuccess.answer_elaborate : ∀ (s out : Yulang.CommonRoleSettledConstraints.State 1)
  (argument : Yulang.Roles.Term) (answer : Yulang.RoleDictionaries.Answer),
  Eq.{1} (Yulang.CommonRoleAssociatedParentPipeline.run s)
      (some.{0} (Prod.mk.{0, 0} out (Prod.mk.{0, 0} argument answer))) →
    Eq.{1} answer
      (Yulang.RoleDictionaries.elaborate Yulang.CommonRoleAssociatedParentGround.visible
        Yulang.CommonRoleAssociatedParentGround.declarations_wellFormed
        (Yulang.CommonRoleAssociatedParentGround.parentGoal argument))
Yulang.CommonRoleAssociatedParentSuccess.success_resolved : ∀ (s out : Yulang.CommonRoleSettledConstraints.State 1)
  (argument : Yulang.Roles.Term) (answer : Yulang.RoleDictionaries.Answer),
  Eq.{1} (Yulang.CommonRoleAssociatedParentPipeline.run s)
      (some.{0} (Prod.mk.{0, 0} out (Prod.mk.{0, 0} argument answer))) →
    Eq.{1} argument Yulang.Roles.Examples.int ∧
      Exists.{1} fun plan =>
        Eq.{1} answer (Yulang.RoleDictionaries.Answer.resolved plan) ∧
          ∀ (implementation : Yulang.Roles.Impl),
            Membership.mem.{0, 0} plan.declarations implementation →
              Membership.mem.{0, 0} Yulang.CommonRoleAssociatedParentGround.visible implementation
Yulang.CommonRoleAssociatedParentExact.source_generated : ∀ (s : Yulang.CommonRoleSettledConstraints.State 1),
  Eq.{1}
    (Yulang.CommonRoleAssociatedStateFlow.fromSourceStore Yulang.CommonRoleAssociatedParentGround.rightEnvironment
      Yulang.CommonRoleAssociatedParentGround.rightRoles Yulang.CommonRoleAssociatedParentGround.right_wellFormed
      Yulang.CommonRoleAssociatedParentGround.request s)
    (some.{0} (Yulang.CommonRoleAssociatedParentExact.extended s))
Yulang.CommonRoleAssociatedParentExact.materialized_int : ∀ (s : Yulang.CommonRoleSettledConstraints.State 1),
  (Yulang.CommonRoleAssociatedParentExact.extended s).Models →
    Eq.{1} (Yulang.CommonRoleOrdinaryKnownness.materialize (Yulang.CommonRoleAssociatedParentExact.extended s).atoms 0)
      (some.{0} Yulang.Roles.Examples.int)
Yulang.CommonRoleAssociatedParentExact.run_of_models : ∀ (s : Yulang.CommonRoleSettledConstraints.State 1),
  (Yulang.CommonRoleAssociatedParentExact.extended s).Models →
    Eq.{1} (Yulang.CommonRoleAssociatedParentPipeline.run s)
      (some.{0}
        (Prod.mk.{0, 0} (Yulang.CommonRoleAssociatedParentExact.extended s)
          (Prod.mk.{0, 0} Yulang.Roles.Examples.int
            (Yulang.RoleDictionaries.elaborate Yulang.CommonRoleAssociatedParentGround.visible
              Yulang.CommonRoleAssociatedParentGround.declarations_wellFormed
              (Yulang.CommonRoleAssociatedParentGround.parentGoal Yulang.Roles.Examples.int)))))
Yulang.CommonRoleAssociatedParentExact.success_exact : ∀ (s : Yulang.CommonRoleSettledConstraints.State 1),
  (Exists.{1} fun out =>
      Exists.{1} fun argument =>
        Exists.{1} fun answer =>
          Eq.{1} (Yulang.CommonRoleAssociatedParentPipeline.run s)
            (some.{0} (Prod.mk.{0, 0} out (Prod.mk.{0, 0} argument answer)))) ↔
    Exists.{1} fun valuation =>
      Yulang.PresenceNormalForm.All.{0, 0} Yulang.Common.model valuation s.atoms ∧
        Yulang.Common.Equivalent (Prod.fst.{0, 0} (valuation 0))
          (Yulang.CommonSyntax.Layer.base.{0, 0} Yulang.Inference.Base.int)
Yulang.CommonRoleAssociatedParentExact.successful_state : ∀ (s out : Yulang.CommonRoleSettledConstraints.State 1)
  (argument : Yulang.Roles.Term) (answer : Yulang.RoleDictionaries.Answer),
  Eq.{1} (Yulang.CommonRoleAssociatedParentPipeline.run s)
      (some.{0} (Prod.mk.{0, 0} out (Prod.mk.{0, 0} argument answer))) →
    Eq.{1} out (Yulang.CommonRoleAssociatedParentExact.extended s)

```

## 独立回帰の記録
# cycle 2: independent regression / ParentSuccess review

## 実行

- 一時証明: `/tmp/cycle2-regression.lean`
- 実行ディレクトリ: `yulang-dots-cycle/lean`
- コマンド: `lake env lean /tmp/cycle2-regression.lean`
- 終了コード: **0**
- 経過時間の精密測定は実施していない。初回コマンドが1秒で実行中を返し、次のポーリングで完了を確認。
- main のファイルは変更していない。`.olean` 出力指定なしの一時ファイル検査。

## 3 具体的回帰

1. `Cycle2Regression.empty_resolved`: 空の ordinary 状態で実 pipeline はある出力状態と int と resolved 辞書 plan を返す。既存 `empty_source_result` から導出。
2. `Cycle2Regression.contradictory_str_none`: 旧 slot 0 に str 等式を持つ状態では実 pipeline は **none**。成功を仮定すると `run_models` の実モデルに対し旧 str 等式と生成 int 等式が同時成立して int=str となる矛盾を使い証明。none を言語仕様上の最終 rejected と同一視はしない。
3. `Cycle2Regression.old_int_resolved`: 旧 slot 0 に int 等式がある状態では、実 associated 生成・実整合性検査・materialize・辞書 elaboration を通り、int 等式をもう一度追加した状態と int と resolved plan を返す。整合性は明示した int モデルで証明、materialize は計算、辞書は既存成功定理を用いる。

3 件とも sorry / 新規 axiom / native_decide を使用していない。

### 出力全文

```text
'Cycle2Regression.empty_resolved' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cycle2Regression.contradictory_str_none' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cycle2Regression.old_int_resolved' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## CommonRoleAssociatedParentSuccess の独立読取監査

重大な不備を発見していない。

- `argument_int`: `run_models` のモデル存在証明から実際の valuation を取得して int と materialize の復号 base の一致を証明する。矛盾状態における空虚な全称だけで成功を推定していない。
- private `scalar_int`: 現行 scalar 表現で int の復号に成功する構文 term が実際に `Roles.Examples.int` であることを構造ケース分けで証明。
- `answer_elaborate`: run の分岐を展開し、返された answer が全 visible 宣言を使う実 elaborate の返値であることを示す。成功タグを外部仮定していない。
- `success_resolved`: 任意の開始状態で run が some を返す場合に限り、引数 int と、全宣言が visible に含まれる実 resolved plan の存在を示す。これにより以前の「任意入力で some でも resolved は未証明」という制限はこの具体的 pipeline に関して解消する。
- 残る範囲: arbitrary source program の解析や output-to-parent slot 対応の生成ではない。既知 Right str の固定宣言例であり、未知 Right a を候補一意性から既知化しない。none 分岐の最終分類、一般 narrowing の停止性・完全性、全 B4 の完成は主張していない。
- 回帰はこれら3入力に対する検査で、全体 verify の代替ではない。

### 回帰の再現用Lean全文（リポジトリのコードには追加していない）

```lean
import Yulang.CommonRoleAssociatedParentSuccess
namespace Cycle2Regression
open Yulang
open CommonRoleAssociatedParentPipeline
open CommonRoleAssociatedParentGround
open CommonRoleSettledConstraints (State)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)

def oldStr : State 1 := CommonRoleCandidateStateFrontier.extend State.empty 0 .str
def oldInt : State 1 := CommonRoleCandidateStateFrontier.extend State.empty 0 .int
def twiceInt : State 1 := CommonRoleCandidateStateFrontier.extend oldInt 0 .int

theorem empty_resolved : ∃ out plan, run State.empty =
    some (out, Roles.Examples.int, .resolved plan) := by
  obtain ⟨plan, result, _, _⟩ := empty_source_result
  exact ⟨resultState, plan, result⟩

theorem contradictory_str_none : run oldStr = none := by
  cases result : run oldStr with
  | none => rfl
  | some value =>
    obtain ⟨out, argument, answer⟩ := value
    obtain ⟨⟨valuation, model⟩, sound⟩ := run_models oldStr out argument answer result
    obtain ⟨oldModel, isInt, _⟩ := sound valuation model
    have isStr := ((CommonRoleCandidateStateFrontier.extend_exact ..).mp oldModel).2
    have impossible : Inference.Base.int = .str :=
      (CommonRigidHeadInspection.base_iff _ _).mp
        (Common.equivalent_trans (Common.equivalent_symm isInt) isStr).1
    cases impossible

theorem old_int_resolved : ∃ plan, run oldInt =
    some (twiceInt, Roles.Examples.int, .resolved plan) := by
  have produced : CommonRoleAssociatedStateFlow.fromSourceStore
      rightEnvironment rightRoles right_wellFormed request oldInt = some twiceInt := by
    rw [CommonRoleAssociatedStateFlow.source_store_agrees]
    have value := (CommonRoleAssociatedStateFlow.value_exact ..).mpr equation_from_declaration
    simp only [CommonRoleAssociatedStateFlow.produce, value, Option.map_some]
    rfl
  have consistent : CommonRoleOpenPropagation.consistent twiceInt = true := by
    apply (CommonRoleOpenPropagation.consistent_exact _).mpr
    refine ⟨fun _ => Comp.pure Common.model (.base .int), ?_⟩
    apply (CommonRoleCandidateStateFrontier.extend_exact ..).mpr
    constructor
    · apply (CommonRoleCandidateStateFrontier.extend_exact ..).mpr
      exact ⟨PresenceNormalForm.all_nil _ _, Common.equivalent_refl _⟩
    · exact Common.equivalent_refl _
  have materialized : CommonRoleOrdinaryKnownness.materialize twiceInt.atoms (0 : Fin 1) =
      some Roles.Examples.int := by rfl
  let dictionary := RoleDictionaries.buildResolved visible declarations_wellFormed
    (parentGoal Roles.Examples.int) parent_int_resolved
  have answer := (RoleDictionaries.elaborate_success_iff visible declarations_wellFormed
    (parentGoal Roles.Examples.int) dictionary.erase).mpr ⟨dictionary, rfl⟩
  refine ⟨dictionary.erase, ?_⟩
  simp only [run, produced, consistent, ↓reduceIte, materialized, answer]

#print axioms empty_resolved
#print axioms contradictory_str_none
#print axioms old_int_resolved
end Cycle2Regression

```

## 最終公開対象（本報告を含め32ファイル）

- `lean/Audit.lean`
- `lean/README.md`
- `lean/Yulang.lean`
- `lean/Yulang/CommonRoleAssociatedBatch.lean`
- `lean/Yulang/CommonRoleAssociatedParentExact.lean`
- `lean/Yulang/CommonRoleAssociatedParentGround.lean`
- `lean/Yulang/CommonRoleAssociatedParentPipeline.lean`
- `lean/Yulang/CommonRoleAssociatedParentSuccess.lean`
- `lean/Yulang/CommonRoleAssociatedStateFlow.lean`
- `lean/Yulang/CommonRoleOpenClosureAllocation.lean`
- `lean/Yulang/CommonRoleOpenFiniteClosure.lean`
- `lean/Yulang/CommonRoleOpenPassStability.lean`
- `lean/Yulang/CommonRoleOrdinaryKnownness.lean`
- `lean/Yulang/CommonRoleSourceIdentity.lean`
- `lean/Yulang/MainStatementsDraft.lean`
- `lean/Yulang/SpecConformanceIndex.lean`
- `notes/design/2026-11-08-cycle2-variance-nominal-bridges.md`
- `notes/design/2026-11-08-dots-cycle2-associated-batch.md`
- `notes/design/2026-11-08-dots-cycle2-associated-flow.md`
- `notes/design/2026-11-08-dots-cycle2-closure-allocation.md`
- `notes/design/2026-11-08-dots-cycle2-finite-closure.md`
- `notes/design/2026-11-08-dots-cycle2-ordinary-knownness.md`
- `notes/design/2026-11-08-dots-cycle2-parent-ground.md`
- `notes/design/2026-11-08-dots-cycle2-parent-pipeline.md`
- `notes/design/2026-11-08-dots-cycle2-pass-stability.md`
- `notes/design/2026-11-08-dots-cycle2-source-identity.md`
- `notes/handoff/2026-11-08-dots-cycle-2-reachability.md`
- `notes/handoff/2026-11-08-dots-cycle2-conformance-candidates.md`
- `notes/questions/2026-11-08-cycle2-associated-parent-source.md`
- `notes/questions/2026-11-08-main-statements-placement.md`
- `tools/Reach.lean`
- `notes/handoff/dots-cycle-2.md`

## 凍結後の追加照合

最終コードa3fd16f0dについてread-only到達解析を再度実行し、両方exit0:

```text
REACH: 8 roots; 5373/82828 non-system declarations reachable
REACH: 6368 roots; 40020/82828 non-system declarations reachable
```

全117公開theoremの完全修飾名集合をnamespaceを追って再抽出し、Audit登録漏れ0、
型出力リストとの集合一致、日本語主張リストの記載漏れ0を確認した。
09:52:59の第5公開で、remote `e2de2f646e42b0374dadaa33d04b129e7ed8a1b4` と
local `a3fd16f0d` の全tree一致（git diff exit0）。この時点で31files公開済み。
本報告を追加すると32filesとなる。最終tree照合は会話の結果報告にも記載する。

## 最終完全cold検証の出力全文

```text
verify-lean: . @ a3fd16f0d (base origin/integration/m1-final)
ok: lake build --wfail (Build completed successfully (1147 jobs).)
ok: Audit.lean exit 0
ok: axioms only propext/Classical.choice/Quot.sound over 6216 printed declarations
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended
ok: AXIOM-GATE-PASS: 82606 declarations
verify-lean: PASS

```

## 末尾空行清掃後の最終コード検証全文

`git diff --check` が新規MainStatementsDraft末尾の空行を指摘したため、その1行のみ削除。既存ファイルの行削除はない。清掃後diff-check exit0。別worktreeで全体を再検証、09:55:02.681〜09:55:51.349 UTC、48.668秒、exit0。

```text
verify-lean: . @ 6de46dac0 (base origin/integration/m1-final)
ok: lake build --wfail (Build completed successfully (1147 jobs).)
ok: Audit.lean exit 0
ok: axioms only propext/Classical.choice/Quot.sound over 6216 printed declarations
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended
ok: AXIOM-GATE-PASS: 82606 declarations
verify-lean: PASS

```

## 時間記録

報告確定時刻: 2026-11-08T09:56:27.676966+00:00。開始からここまで 2677.7 秒（44.63 分）。公開・最終tree照合を含む終了時刻と全体所要時間は、この会話の完了報告で追加する。停止・時間切れ・環境再作成は確認されなかった。初回二重buildのFAILとその回復は上に全出力を残した。

## 完了時の公開照合と全体所要時間

報告を含む全32filesをGitHubアプリでwork/dots-mainへ公開。09:57:12 UTC、remote `1b2762170ebde85fbd00645a21b9e17874698b0d` とlocal `c10b44a91` の全tree一致（git diff exit0、working tree clean）を確認した。

同じ報告込みtreeに対して最終verifyを実行し、09:56:43.491〜09:57:29.871 UTC、46.380秒、exit0。全文:

```text
verify-lean: . @ c10b44a91 (base origin/integration/m1-final)
ok: lake build --wfail (Build completed successfully (1147 jobs).)
ok: Audit.lean exit 0
ok: axioms only propext/Classical.choice/Quot.sound over 6216 printed declarations
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended
ok: AXIOM-GATE-PASS: 82606 declarations
verify-lean: PASS

```

完了追記時刻: 2026-11-08T09:57:43.796417+00:00。開始09:11:50からの全体所要時間 **45.90分**（この追記の最後の公開照合にかかる数十秒は含まない）。この追記は文書だけでLeanコードは変わらない。最終公開後、全tree一致を再確認して会話へ報告する。
