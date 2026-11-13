# dots cycle163: finite coverage, ledger settlement, and conditional consumer resumption

## Scope and result

I21 Evidence lane only. I26 actual Settled guard/Step/Stable definitions remain unchanged.
V5 remains **8/14 open**; this is not general progress, completeness, principal typing,
termination, or a complete `evidenceNode`/`generatedChildren` proof.

The additions separate three claims rather than conflating semantic Evidence with
recorded packet settlement:

1. For arbitrary roles, registry, tracked state, root and finite selected dictionary,
   `PacketCoverage` means that each selected descendant has an actual recorded
   packet with the exact selected children. It implies Discharged of the root.
   Parent packet membership plus finite classified child dictionaries and their
   coverage implies PacketSettled. An already trusted input ledger, producer input
   entry and actual output-entry membership then imply a trusted output ledger.
   Reachability and semantic Evidence are not substituted for journal coverage.
2. `AliasCoverage` permits the same certificate at a recorded aliased site, with
   both sites present and actual Alias connectivity. Exact coverage implies alias
   coverage. This is not arbitrary alias rewriting of packet children.
3. Actual I26 reachability and root Stable, ordinary Extension of every historical
   packet context, explicit finite structural/history coverage, and a classified
   finite dictionary imply Evidence in every final model. Historical replay and
   finite syntax derive the selected Joint obligations and generated descendants;
   neither child Evidence nor a conclusion-shaped JointClosure is assumed.
   Coverage and ordinary-growth restrictions remain genuine assumptions. Inconsistent
   final contexts make the all-model claim vacuous; existence is not asserted.
4. A genuinely enabled, novel, guarded terminal child install discharges that child.
   If a recorded producer's other children were already discharged, it settles the
   producer, derives its recorded output trust from the old trusted input ledger,
   and supports actual consumer readback. A two-step theorem then installs the
   consumer only with explicit Generated, ordinary Installable, novelty and old
   packet guard. Those preconditions have not been manufactured from Evidence.

These are useful restricted bridges, not a claim that Stable implies PacketCoverage.
A full concrete nonterminal producer with genuinely fresh output followed by a
previously blocked generated consumer's successful installation remains open.
The reserved terminal output fixture alone is not that example.

## Recovery and authorization

Scheduled start 2026-11-13T10:27:19Z; work started 10:27Z. Hard deadline11:22:19Z.
Fresh integration head: 50a82661793b0a5b3739f0dd7136676826acd75a.
Prior public cycle162 final: 1ac6c0cbc8aeddafe9c94011a66eed71fd483eca.
Standing orders, inbox, AGENTS, previous report and completed heartbeat reread.
Prior writer stopped; no overlapping writer to the same publication branch.
Existing worktree retained; integration already an ancestor. New modules only;
Yulang.lean imports appended. Root Audit/README, existing semantic modules, spec,
notes/plan and Lake configuration are unchanged.

## Verification and resource limits

Lean4.35.0. Initial direct trust0 checks and public axiom audits passed for the
core exact/alias settlement, consumer-resume, and finite-coverage modules.
A focused Lake invocation was interrupted during shared-cache rebuild under
memory pressure; it is NOT reported as PASS. Some new cached oleans disappeared
and subsequent import checks failed until regenerated. Fixture elaboration also
exposed namespace shadowing/implicit finite-index inference mistakes; corrected
source requires final isolated replay below. No interrupted/empty log is a PASS.

A dedicated workspace cache with symlinked unchanged dependencies is used for
final sequential trust0 recompilation of every new source. New output objects
replace their own cache links, never shared cache targets. Public type/axiom checks
and an all-declaration dependency gate are recorded below when complete.
Only propext/Classical.choice/Quot.sound are permitted. Full repository build,
root Audit and full verify-lean are intentionally not run per standing orders;
reviewer must perform whole-repository verification. Diff-only verification is
reported separately from a build.

Yulang2 x-oracle read; no new live Yulang2 CLI test and no assertion that old
Yulang2 implements I26 rules. Usage quota unknown.

## Next bounded work

- Construct and validate the genuinely fresh-output nonterminal producer/terminal
  child/consumer execution prefix, including novelty and Generated certificates.
- Relate current finite syntax/history coverage to a broader actual I26 fragment
  without assuming JointClosure or child Evidence.
- Handle descriptor-changing reobservation explicitly; ordinary packet-context
  Extension does not cover it.

## Publication and final evidence

Only work/dots-main is authorized. All intermediate checkpoints
must be fetched and compared to the fixed local source tree; heartbeat-only
changes are separated from source comparisons.

## Independent review boundaries

Read-only second reviews found no soundness blocker. Consumer resumption remains
a sufficient contract: ExplainedRead explicitly requires current Head and semantic
entailment from the stated fact list. It has not been proved that the new output
alone supplies every consumer read. The theorem permits already-settled producers;
it does not assert a strict before/after change without a prior-not-settled fact.
The exact-recorded positive fixture is terminal; alias coverage has no nontrivial
positive alias fixture this cycle. The recursive finite-coverage application has
an explicit current model and nonempty journal, so its semantic Evidence claim is
nonvacuous, but still does not imply packet settlement.

## 現在の13項目（定義の位置と一般橋の区別は前cycleから不変）

|項目|現定義|残る区別|
|---|---|---|
|Checked|GeneralDeclarations.Checkedとroles一致|front-end adequacyとは別|
|Models|SaturationState.Models(current)|意味論の定義|
|Step|SettledSteps.Step|Astraの実guard使用、一般progress/execution未達|
|Stable|SettledSteps.Stable|旧Value Stableを意味しない|
|Generated|SaturationState.Generated|一般選択子bridge未達|
|RootPending|NominalState.RootPending|現在context既知性|
|RootK2|FeedbackK2.RootK2|K2拒否の優先維持|
|CandidateK2|FeedbackK2.CandidateK2|既存規則|
|InspectionPending|Value pendingまたはSettled SupportPending|選択排除は証明、意味論Evidence否定ではない|
|Survivor|RecursiveCandidates.Survivor|一般Evidence接続未達|
|Evidence|DictionaryRecursiveEvidence.Evidence|final contextのModelsに対する意味論|
|Reorders|RegistryReordering.Reorders|canonicalLocalOrder未達|
|DictionaryEquivalent|DictionaryPayloadOrder.Equivalent|主定理全体ではない|


## 現時点で確定した検証（10:48 UTC）

- 新7moduleの全sourceを独立cacheへ逐次 `lean --trust=0 -o ...` で再compile: EXIT0。
- 公開48定理の型表示と公理監査: EXIT0。
- private/generatedを含む64宣言の依存公理gate: EXIT0。
- `verify-lean.sh . origin/integration/m1-final --no-build`: EXIT0（差分のみ）。
  cache symlinkがuntrackedとして最初の検査を失敗させたため、local excludeへ
  登録して再検査した。gateのrun_cmdは依存公理の収集・失敗判定だけを行い、
  証明宣言を追加しない。コメント行のsyntax/historyもREVIEWに拾われたが構文拡張ではない。
- checkpoint75466826a5f77c8bedee43a12c9df825141ba087をGit再取得し、
  固定local b3ed97374795c5a83a1eac8982490ac7028e75c1との差は意図した心拍だけ。

### 具体例の追加確認

再帰・非空journalの例はactualモデルを明示し、新coverage定理からEvidenceを導出。
terminal予約出力はinstall直後からTrusted/HeadJustifiedだが、install後もequate後も
ReadyAtではなく、actual refresh後に初めて現在headが揃う。この差を3Stepの
実timelineとして証明した。これをnonterminalな消費者の実再開とは呼ばない。

## 追加の具体的阻害（10:52 UTC）

`RecursiveConsumerObstruction`は、実finishで生成済みのdisplayChildについて、
任意のInstallable packetがすでにCommittedであることを既存の具体的closureから
導いた。したがってterminal childのnovel installを要する再開契約には証人がなく、
actual I26 Stableから子の全Atも不可能。actual model・Classify・Unsettled・
Generated・noAtが同時成立する。これはsource inconsistencyでも一般progressの
反例でもなく、この既存fixtureへ再開契約を適用できない正確な理由である。

この追加を含む8moduleの全source逐次trust0 replayとaudit10本がEXIT0。
公開53定理、private/generatedを含む69宣言のgateがPASS。

Checkpoint2 `968e587a558bbb44df6f202f88b603ac20bc4b3c` was fetched.
Its full tree differs from fixed local `ce26e782ec824955850aab15a2a21c794df08a12`
only at the intended heartbeat. Every one of its8 published module sources
matches the inventory SHA256. Final published-source replay is recorded below.

## actual novel terminal-child正例（11:00 UTC）

`SettledTerminalPrefix`は既存のchecked sibling fixtureをI26へ移し、
InitialSourceからparent Pの実install、生成されたContainer子の実installまでを
証明した。子はInstallableかつ未Committed、terminalで、名前つき出力を持つ。
子packetがSettledとなり、その出力を含むTrusted ledgerが存在する。final modelも
存在するので空虚な成功ではない。出力identityは現在の全slotより大きく、
Trustedでも現在のReadyAtはまだ成立しない。

重要な限定: root Pの名前つき出力requestは空である。非空の名前つき出力は
terminal Container子のもの。Pには他の兄弟義務がある。Pの片付け、nonterminalな
名前つき出力producerの完成、consumerの実再開は証明していない。

### 追加主要定理の読み方

- `parent_step`, `container_step`, `actual_prefix`, `reachable`: 固定された
  checked registry/root/startから、実Settledの2StepでafterCに到達する。
- `container_ready`, `container_decision`, `container_guard`: この子の入力headと
  inspectionは暫定出力ではなく元のsourceで正当化される。
- `child_settled`, `child_output_trusted`: 新terminal packetの実記録と子の空リスト、
  実input/output factsから片付けと出力trustを導く。
- `output_above_slots`, `output_not_ready`: 出力identityは元の0,1,2slot外で、
  現在headはまだ存在しない。異なる意味論値を意味しない。
- `inhabited`, `genuine_terminal_prefix`: 独立のcountermodelによるnoveltyを維持し、
  実到達列と最終model存在を伴う正例。

全公開名はmodule-guide、完全な型は検証ログに記載する。

## 固定source最終検証（11:01 UTC）

新9module、公開66定理、private/generatedを含む87宣言。全新sourceの
独立cache逐次trust0再compile、audit11本（型表示とgateを含む）はEXIT0。
TerminalPrefixの別担当read-only reviewもPASS。actual sourceによるguard、
noveltyの具体的countermodel、非空のfinal modelを確認した。

初回のfocused Lake中断とは別に、メモリ余裕を確認し、11:01から9targetだけの
focused Lakeを6分上限で再試行する。結果が下に確定するまでPASSとはしない。

## focused Lake再試行の確定（11:03 UTC）

`LEAN_NUM_THREADS=1 timeout 6m lake --wfail build` に、新9module名だけを
明示したfocused build: **EXIT0,837 dependency jobs**。新9moduleすべてが
Builtと記録され、warningsなし。全体targetを指定したbuildではない。
独立source replayと別にLake経由の組立ても確認できた。
最新diff-only検査もEXIT0。全文は `dots-cycle-163-lake.txt` と
`dots-cycle-163-diff.txt`。初回中断をこの成功で隠してはいない。

## 公開sourceそのものの再検証（11:05 UTC）

checkpoint3 `2b21b5df005516ca66bbf2966d0faabbbe88bb3e`を取得し、
固定local `68597267d`とのfull-tree差は意図した心拍だけと確認した。
公開commitから新9sourceを抽出し、inventory SHA256を全件照合したうえで、
抽出sourceを全件trust0再compileし、同commitの87宣言gateも再実行: EXIT0。
`notes/verification/dots-cycle-163-public-replay.txt`に全文を保存する。
その後も9つのLean sourceは変更していない。説明・検証ログと、下記のaudit-only回帰検査を追加した。

## 通常Lake監査とcross-module回帰検査

9target build後の通常 `lake env lean --trust=0 Audit/Cycle163*.lean` の
11本もすべてEXIT0。独立cacheだけの成功ではない。
さらにaudit-onlyの3検査を追加し、semantic finite coverageからrecorded exact/alias
coverageへの無条件upgradeが、このactual非空journalの例で不可能であること、
actual model・Evidence・Unsettledが共存することをkernelで確認した。EXIT0、
標準3公理のみ。これは新しいlibrary moduleではなく受け入れ回帰検査である。
したがってlibrary公開66定理にaudit-only3検査を別計上し、source9moduleの
private/generatedを含むgate対象は引き続き87宣言。

## 公開ancestryの追加検査と修正

11:10に、公開treeは一致しても、従来のpublic parent chainに今回のintegration
50a82661793b0a5b3739f0dd7136676826acd75aがancestorとして含まれていないことを
確認した。これはGitHub publicationがremote parentのみで鎖を作ったためで、
source内容の不一致ではない。次のpublicationで同integrationをsecond parentに
加え、検証済みtreeを変えずにancestryを修復する。修復後のimmutable commitで
ancestor検査とdiff-only verifyを行い、結果を末尾に記録する。
