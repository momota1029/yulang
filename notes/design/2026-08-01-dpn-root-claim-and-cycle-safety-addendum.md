# DPN 追補: root claim 到達性と評価サイクル安全性

日付: 2026-08-01

状態: **ユーザ承認済み（2026-08-01）**

著者: Claude (Sonnet 5)、Codex `gpt-5.6-sol`（xhigh）の調査・設計提案に基づき統合・記述。

**署名についての注記**: このリポジトリの正本文書は通常 Claude (Fable 5) が起案する
慣習だが、本書の起案時点で Fable 5 はサブスクリプション利用制限のため一時的に
利用できなかった。そのため本書は、Codex Sol XHigh に投資・設計提案の起案を行わせ、
Claude (Sonnet 5、本セッションの監督エージェント) がその内容を検証・統合して
文書化した。他の正本文書と同じ査読基準（決定を下す・棄却案を記録する・
invariant を明示する・pinned test との整合を確認する）を満たすことを狙ったが、
慣例との差分として記録しておく。

本書は `notes/design/2026-08-01-derived-unary-premise-nodes.md`（以下 DPN 文書）の
stop condition 発火（DPN-0 の実測で判明した 2 件のギャップ）を受けた追補設計である。
DPN 文書の中核決定（§2-D2 の `ProofPremise` 3 ソート、premise 解決を登録時から
評価時へ移す方針、既存 invariant）を改廃するものではなく、**root claim への
到達経路**と**評価再帰の停止性保証**の 2 点だけを修正する。

## 0. 本書が下す決定の要約

1. **A: producer 制約から root claim への鏡 index を新設する**。
   `root_claim_by_producer_constraint: ConstraintRecordId -> UpperReplayClaimId`。
   Direct・Reduced 両方の生成元を持つ**共通コンストラクタ**
   `TypeBounds::original_upper_replay_claim`（`mod.rs:1124`）一箇所でのみ維持し、
   呼び出し元ごとの個別 hook にはしない。
2. **B: DPN D3 評価に pass-local な cycle guard を導入する**。
   `StructuralDerivation.parent` の arena ID が常に子より若いという DPN の
   当初の停止性根拠は実測で反証されたため撤回し、tri-color
   （`Visiting` / `Done`）状態による能動的な cycle 検出へ置き換える。
   circular な経路は「空虚な証明」として非投影評価されるが、record・constraint
   全体の判定は他の経路の fail-open 規則が引き続き保護する（MPC D3 の
   record cycle 規則をそのまま constraint ノードへ拡張するだけである）。
3. どちらの修正も `ProofPremise` の型・登録規則（DPN §2-D2）や claim 層
   （MPC D1 / CDM D1）には触れない。

## 1. 背景（DPN-0 で確定した事実）

DPN-0（2026-08-01 実行）は 3 項目のうち 2 項目で合格し、1 項目で
stop condition が発火した。

- **合格**: 証拠源分布。12,580 occurrence / 4,426 unique constraint で
  「解決不能」ゼロ。100% が「(a) linked lower record なし」——DPN §1.3 の
  「map miss が通常」を強く裏付けた。
- **合格（ただし根拠に誤りあり）**: 連鎖深さ分布。最大 6 hop、cycle 0 件、
  bounded。ただし DPN が述べた停止性の根拠（「`StructuralDerivation.parent`
  は常に子より若い arena ID を持つ」）は、実測で 88 件の反例が見つかり反証された。
  観測された DAG 自体は acyclic だったが、**書かれていた理由づけは成立しない**。
- **不合格（stop condition）**: root claim アクセス経路。
  - 通常の Direct root には scan-free 経路がある:
    `ConstraintRecordId -> 制約 key の canonical upper BoundRecordId ->
    original_claim_by_record_and_producer[(record, producer)]`。
  - URR **Reduced root** にはこの経路が効かない。Reduced claim は
    materialization に伴って `current_record` が移動するため、元制約の
    upper key から得られる record ではもう pair index を引けない
    （局所 fixture で 0/1 hit）。
  - repository-std の実データで、関連 premise の root producer のうち
    **34 件が Reduced-only**——理論上の edge case ではなく実在の production
    occurrence である。
  - root claim の生成 site 自体が **2 箇所**ある: Direct 用の no-parent
    fallback（`machine/bounds.rs:742` 付近）と、Reduced 用の URR 登録
    （`row_effect.rs:475` 付近）。DPN §8 が代替条件として置いた
    「fallback が単一生成 site であること」も、字義どおりには成立しない。

DPN-0 は自身の decision fork に従い、正しく「実装せずレビューへ戻す」を選択した
（DPN §12.1-2 準拠）。working tree は clean のまま保たれている。

## 2. 決定

### A1: producer-keyed な root claim 鏡 index

```text
root_claim_by_producer_constraint: ConstraintRecordId -> UpperReplayClaimId
```

**維持箇所**: `TypeBounds::original_upper_replay_claim`（`mod.rs:1124`）一箇所。

この関数は `UpperReplayClaimLineage::Original` の共通コンストラクタであり、
Direct（no-parent fallback、`machine/bounds.rs:742` 付近から呼ばれる）と
Reduced（URR 登録、`row_effect.rs:475` 付近から呼ばれる）の**両方の生成元が
最終的にここを通る**。個別の呼び出し元 2 箇所にそれぞれ hook を置く案
（DPN-0 の finding が最初に示唆した形）よりも、この共通コンストラクタ 1 箇所で
維持する方が強い——将来この関数を呼ぶ新しい経路が増えても自動的に鏡へ入るし、
維持義務が 1 箇所に集約される。

維持規則:

1. 新規 claim 生成時、および冪等な既存 claim 返却時のどちらでも挿入する。
2. `move_upper_replay_claim`（`current_record` の移動）では**一切変更しない**
   ——claim ID と producer identity は record の移動と独立に安定である。
3. 保存するのは安定な original claim/root handle であり、評価時は引き続き
   canonical-root `find` を通す。
4. 既存 entry と異なる claim が同じ producer に紐付こうとした場合は
   assert で検出し、黙って上書きしない（後述 A2）。
5. lazy に保つ——claim を持たない workload には index entry を作らない
   （no-claim passthrough、CDM D3 と同じ index 哲学）。
6. append-only 入力の鏡として扱う。判定結果の memo ではないため、
   MPC §6.3 の「恒久的な判定 cache は要求しない」方針と衝突しない。

DPN §2-D3 の評価規則 (c)（root claim による base case）は次のようになる。

```text
eval(Constraint(c)) の source (c):
    root_claim_by_producer_constraint.get(c)
        -> find(root claim の coverage root)
        -> NOT live(canonical root)
```

### A2: producer→root の単射性を明示的 invariant にする

```text
すべての Original claim について:
    root_claim_by_producer_constraint[claim.producer_constraint] == claim.id
    claim.coverage_root == claim.id （生成時点）
```

一つの producer が二つの異なる Original claim に対応することがあってはならない。
これは現行の production 制御フローでは成立するはずの性質（一つの canonical
制約は一度だけ処理され、終端の upper admission が Direct か Reduced かを
選ぶのであって両方を生成しない）だが、**census / assertion として明示的に
確認する**。もし一つの producer が二つの claim を持つ実例が見つかった場合は、
どちらかを黙って選ばず、その時点で実装を止めて設計レビューへ戻す
（複数 exact index と OR 規則が必要になる可能性があり、それは新たな設計判断を要する）。

### B1: arena 順序を停止性の根拠から除外する

DPN が述べていた「`StructuralDerivation.parent` は常に子より若い ID を持つ」は
削除・撤回する。

反証の機構: `enqueue_derived_subtype`（`machine/entry.rs:1288` 付近）には
vacant 分岐（新規 child を親の後に割り当てる——この場合のみ `parent < child`
が成立する）と occupied 分岐（既存の canonical child へ新しい親を後から
接続する——この child が親より若い ID を持ちうる）がある。
`merge_structural_derivation`（`entry.rs:1351` 付近）は意図的に既存 child へ
追加の親を接続するため、この非単調性は canonical coalescing の正常な帰結で
あり、arena の破損ではない。

**いかなる正しさ・停止性の判断も `ConstraintRecordId` の大小比較に依拠しない。**

### B2: 評価は構築によって cycle-safe にする

DPN D3 の評価（`eval`）に pass-local な tri-color 状態を導入する。

```text
EvalState = Visiting | Done(projectable: bool)

eval(node):
    Done(v)   -> v
    Visiting  -> false （この経路の証拠源だけを false とする）
    absent:
        Visiting としてマーク
        該当する証拠源／節をすべて評価する
        Done(result) へ置き換える
        result を返す
```

対象ノードは少なくとも `Record` と `Constraint`。`RootCoverage` は leaf なので
対象外でよい。

意味論:

- `Visiting` な `Constraint(c)` へ再入した場合、**その circular な経路だけ**が
  false になる。
- constraint の他の証拠源（(a)/(b)/(c) の他の腕）は引き続き評価される。
- ReplayConjunction で premise が circular なら、その conjunction は false。
- 他に有効な節・証拠源を持つ record / constraint は、それを通じて
  projectable になり得る。
- 純粋に自己循環する導出だけは証明として受理されない
  （「これが証明されるならこれは証明される」という空虚な主張の拒否——
  MPC D3 の record cycle 規則をそのまま constraint ノードへ拡張しただけである）。
- metadata 破損・参照不能は DPN の既存 fail-open（projectable 側）のまま。
  能動的なノードへの再入は「lookup 失敗」ではなく「circular な証明」として
  区別して扱う。

**性能への影響**: DPN の文言を「memo 付き DAG walk」から
「memo 付き reachable-proof-graph walk（active-path cycle cutting 付き）」へ
改めるが、性能契約自体は変わらない。時間計算量は評価 pass あたり O(V + E) の
まま、状態は評価 pass 内に限定された O(V)、各ノードは
absent → Visiting → Done の遷移をたかだか一度しか経ない。恒久的な判定 memo
も新たな invalidation 義務も発生しない。fixpoint も SCC 構築も導入しない。
DPN D5 の登録時 chain walk は既に visited set を持っているため、D5 側の
アルゴリズム変更は不要である。

DPN-0 が確認した「confirmed workload では cycle 0 件」というbaselineは、
このguardを入れても結果は変わらない（安全網が今のところ発火しないことを
意味するだけである）。将来 confirmed path 上でこの guard が実際に発火する
workload が見つかった場合は、その topology を個別に調査してから landing の
可否を判断する——fixpoint 等で黙って迂回しない。

## 3. 必須 invariant（DPN 既存 invariant への追加分のみ）

DPN §3 の 8 項目はすべて継続して有効。本書が追加するのは次の 2 点。

9. **producer→root 単射性**: すべての Original claim について、
   producer から鏡 index を引いた結果が自分自身の claim ID と一致する
   （A2）。違反は fail-open で吸収せず、stop condition として扱う。
10. **評価の cycle 安全性**: `eval` の再帰は pass-local な `Visiting`/`Done`
    状態により、いかなる circular な経路でも有限回で終了する。circular な
    経路は非投影として扱われるが、record/constraint 全体の判定は他の
    独立した証拠源による fail-open で保護される。

## 4. pinned tests との整合

DPN §4 の整合性（MPC pinned 5、CDM anchor、`mpc_a_9_8` の walkthrough）は
本書の変更対象外であり、すべて期待値無変更で成立し続ける。

- A（root claim 鏡 index）は評価規則 (c) の**アクセス経路**だけを変更する。
  DPN §4.5 の walkthrough で使われた `Constraint(1)`（replay result）は
  そもそも root claim を持たないケースであり、(c) は最初から不成立
  （walkthrough の結論は不変）。
- B（cycle guard）は DPN-0 が確認した「confirmed workload で cycle 0 件」
  という事実により、既存の pinned test・DPN §9 で新設予定の regression spec
  のいずれの結果も変えない。guard は安全網であり、発火しない限り観測不能である。

## 5. 採らない案

### 5.1 A: claim の既存フィールドを直接使う

採らない。`UpperReplayClaim.producer_constraint`、
`reduction_claim_by_state`、`UnweightedRowReductionRecord.producer_constraint`
はいずれも安定して producer を保持しているが、**方向性の問題**がある——
これらへ到達するには先に claim または state を知っている必要があり、
「producer からclaim を引く」という求められているアクセス方向を提供しない。
既存 entry を鏡 index の**検証**には使えるが、鏡 index の代替にはならない。

### 5.2 A: reduction record をスキャンして producer と照合する

採らない。`unweighted_row_reductions_by_source[source]` は vector を返し、
producer 比較のための線形走査が要る。DPN の scan-free アクセス契約への違反。

### 5.3 A: row provenance を辿って state / 移動後 record を再発見する

採らない。これは MPC §12.1-7 が既に棄却した post-hoc graph traversal と
同じ種類であり、名前を変えて再導入しない。claim 生成時点で既に分かっている
metadata を重複して持つだけである。

### 5.4 A: 2 箇所の呼び出し元だけに個別 hook を置く

共通コンストラクタでの一箇所維持を採る（決定 A1 のとおり）。
呼び出し元ごとの hook は現時点では完全かもしれないが、二重の維持義務を生み、
将来 `original_upper_replay_claim` を呼ぶ新しい経路が増えた場合に
黙って鏡から漏れるリスクを持つ。

### 5.5 A: `ConstraintRecord` 自体に root_claim を直接持たせる

採らない。no-claim workload を含むすべての `ConstraintRecord` を拡張し、
`ConstraintMachine` / `TypeBounds` の所有権境界を越えて claim 層への書き込みを
強制することになる。lazy な claim 側の鏡 index の方が blast radius が小さい。

### 5.6 B: 構造的な rank（サイズ順序）を再構築して停止性を証明する

停止性の機構としては採らない。通常の分解規則の大半はカバーできるが、
row/record の集約や `derive_nominal_record_fields` が外部から instantiate
された projection receiver/result endpoint を使う経路など、すべての
structural admission surface を「child は親の構文的部分項である」という
尺度だけで覆えるかは確認できていない。維持義務を追加してまで証明を
完成させるより、cycle guard の方が確実である。

### 5.7 B: SCC 構築や fixpoint を導入する

採らない。DPN-0 は cycle を 1 件も観測していない。停止性に必要なのは
能動経路の guard だけであり、SCC・fixpoint は DPN の「一回走査」「不動点禁止」
invariant への違反になる。

### 5.8 B: circular な経路を projectable として扱う

採らない。循環する前提は肯定的な証拠ではない。circular を true とすると
leak 側の false positive を再導入し、MPC の record cycle 規則
（circular な節は非投影）と矛盾する。

## 6. blast radius

### 6.1 触る範囲

**DPN-A（登録層）**:

- 新規 lazy map 一つ（既存の claim 系 index の隣）。
- `original_upper_replay_claim` 内での冪等な鏡更新一箇所。
- DPN D3 評価規則 (c) の読み取り経路。
- test/debug 用の完全性 census（producer→claim の単射性、Direct/Reduced
  両方が共通コンストラクタを通ることの確認）。
- `move_upper_replay_claim` は変更しない。

**DPN-B（評価層）**:

- 評価器の memo/visited 管理を tri-color pass-local 状態へ置き換える。
- arena 順序の主張をDPN文書・コメントから除去する。
- DPN D3/D5 の「有限 DAG」という文言を「cycle cutting 付きの有限
  reachable proof graph」へ精密化する（DPN 文書は編集しないので、
  この精密化は DPN-B 実装時のコメント・§13 相当の追記として反映する）。
- 合成 cycle test と cycle counter を追加する。

### 6.2 触らない範囲

`ProofPremise` の型・登録規則（DPN §2-D2）、`scheme_projection_lower_record_by_constraint`
自体、claim 層全体（生成・継承・coalescing・coverage・liveness・`Qualified` payload）、
CDM の記帳・差分機構、raw bounds、URR lifecycle、consumer contract、
portable provenance、既存 test の期待値。

## 7. DPN 文書との関係

本書は DPN 文書（承認済み）を編集しない。置き換える箇所:

- DPN §2-D3 の source (c)（root claim base case）のアクセス経路
  → 本書 A1。
- DPN の「`StructuralDerivation.parent` は常に子より若い」という
  停止性の根拠 → 撤回（本書 B1）。
- DPN §2-D3/D5 の「memo 付き DAG 一回走査」という評価機構の記述
  → cycle guard 付きへ精密化（本書 B2）。
- DPN §8 の stop condition 2 件（root-claim access、chain-depth の
  根拠）→ 本書の承認をもって解除される。

それ以外の DPN の決定（`ProofPremise` の 3 ソート、登録規則、D1・D4・D6、
pinned tests、§9 regression specs、§10 slice 構成）はすべて有効なまま残る。

## 8. 実装スライスへの反映

DPN §10 の DPN-A / DPN-B の中身へ、本書の決定を織り込む。

- **DPN-A（登録層。判定は不変）**: 本書 A1/A2 の鏡 index 実装と census を
  DPN-A の変更範囲に追加する。gate は DPN §10 のまま
  （全既存 test green、線形性 census、confirmed path 上の帰属完全性）に加え、
  producer→root 単射性 census を追加する。
- **DPN-B（評価拡張・invalidation。MPC-C と同時 landing）**: 本書 B1/B2の
  cycle guard 実装を DPN-B の変更範囲に追加する。gate は DPN §10 のままに、
  合成 cycle test（本書 §9 相当の regression spec を DPN §9 の枠組みに
  追加する形で用意する）を加える。

DPN-0 の合格 2 項目（証拠源分布・連鎖深さ）は再実行不要——実測値はそのまま
baseline として有効である。本書が要求する追加検証は、A2 の単射性と
B2 の cycle guard が正しく機能することを確認する新規テストのみであり、
DPN-0 のような別建ての事前検証ラウンドは不要と判断する
（両修正とも append-only な追加、または pass-local な評価機構の変更であり、
DPN-0 が検証した「大域的な形状」自体は変えないため）。

## 9. stop / rollback conditions

### 9.1 stop conditions

次のいずれかが判明した時点で実装を止め、本書のレビューへ戻る。

1. `original_upper_replay_claim` を経由しない Original claim の生成経路が
   見つかる。
2. 鏡 index の完全性が、実際の Original claim 集合と一致しない。
3. 一つの producer が二つの異なる Original claim に対応する実例が見つかる
   （A2 違反）。
4. 鏡 index を追加した後もなお、root claim の取得に scan が必要になる。
5. confirmed path 上で、SCC・fixpoint が無ければ結果を保てない cycle が
   見つかる。
6. cycle の評価結果が探索順序・挿入順序に依存する。
7. 評価が O(V + E) を超える、または恒久的な判定 cache・新たな invalidation
   義務が発生する。
8. 既存 pinned test の期待値変更が必要になる。
9. no-claim workload が鏡 index・cycle guard 状態を新たに allocate する。
10. DPN §12.1 の他の条項（本書で解除された root-claim access と
    chain-depth 根拠を除く）のいずれかが発火する。

### 9.2 rollback units

- 鏡 index（A1/A2）は独立に revert 可能な形で commit する。
  producer→root 単射性が成立しなければ、部分的な鏡を残さず slice ごと戻す。
- cycle guard（B1/B2）は DPN-B・MPC-C と一体で landing / rollback する
  （DPN §12.2・MPC §12.2 の「判定切替と invalidation を分割して landing
  しない」規律を継承）。
- いかなる rollback でも、DerivedUnary の Standalone fallback（MPC 旧 D2-4）
  へは戻さない。

## 10. 波及する文書（本書 landing 後に更新。本書では編集しない）

- `notes/architecture/claim-propagation-architecture.md`: 投影判定の
  premise ノード評価の説明に、root claim 鏡 index と cycle guard の存在を
  追記する。
- `notes/design/2026-08-01-derived-unary-premise-nodes.md`（DPN 文書）は
  承認済みのため編集しない。§2-D3 の source (c) と停止性根拠の後継が
  本書であることは、本書 §7 が記録する。

---

著者: Claude (Sonnet 5)（Codex `gpt-5.6-sol` xhigh の調査・設計提案を統合）

ユーザ承認済み（2026-08-01）。本書は設計判断の正本として扱う。
実装は DPN §10 の DPN-A / DPN-B スライス（本書 §8 の反映を含む）に従って
着手してよい。
