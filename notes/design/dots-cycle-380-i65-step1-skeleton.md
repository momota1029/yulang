# I-65 step 1: `dictionary_sound` の証明骨組み（C380 / I-66）

正本: `momota1029/yulang@a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6` (`integration/m1-final`), inbox blob `b99fbb19f8c0c8c05abcd09f4cf3f44cfd4de26e`。下記の既存の証拠はすべてこの integration のファイルから読んだ。比較対象の作業ブランチは `820e4f2bb26aa02e6a1933d141a2b877900c328b`。該当 I-65 ファイルが両方にあることと、任意の状態の結論が証明済みであることは別。

## 固定文と最上段

C365 の固定文をそのまま使う。以下は実装済みの Lean ファイルではなく、補題の命題と接続の設計である。

```lean
theorem dictionary_sound
    (s : State) (q : Request) (d : Dictionary)
    (selected : Classifies s q (.selected d))
    (m : Model) (fit : Fits s m) :
    DictionaryEvidence s m q d
```

上段の証明本体は次の形（S01・S11・S12・S13 の下にある依存を本文で展開する）。全補題が揃えば未接続の追加前提はない。

```lean
  obtain ⟨t, tree, trace, summary⟩ := classifies_unpacks_actual_source selected  -- S01
  obtain ⟨written, lowered, literal, replay⟩ := lower_selected_general_tree
    (selected_frontier_to_general_node (s := s)) t tree trace summary         -- S10, S11
  exact general_meaning_to_dictionary literal replay
    (general_tree_sound lowered m fit)                                   -- S12, S13
```

### 記号と境界

- 実在する型は `State`, `Request`, `Model`, `Fits`, `children`, `visible`（`GeneralDeclarativeI65State365.lean`）、`Tree`, `Frontier`, `Dictionary`, `Resolves`, `Summarizes`, `All₂`（`CommonRoleOutermostResolver.lean`）。C365 の `State` は `current, modes, origins, routes` を持つ。全称の型の識別子は固定文を変えない。C365 の表現が仕様の全形を本当に表せるかも S01/S04/S07/S09/S13 で確認し、追加の不変条件が必要なら既存の宣言的導出から示す（定理の仮定に追加しない）。`Fits` はモデル解釈であり、候補の選択や release を表さない。
- 下記の `LocalSource s` は **これから実現する独立な規則**。`Classifies` の固定 API と一緒に S01 で具現化する。旧 `Local` の別名でも、checker の成功判定でもない。読んだ integration の I-65 モジュールでは全称の `Classifies` / `DictionaryEvidence` は見つからなかった。S13 が後者の実 API を具現化する。これらは仮定や無償の別名にしない。
- `SelectedSource s q key kids` は S02 の中間データ。実 root 構文、選択されたソース宣言の出現、元の順序付き候補判断（成功・不一致・保留の理由）、その規則の body 導出と子リストを持つ。比較の意味、受理証明、`SourceReceipt` はフィールドにしない。
- `OrdinaryRoot`, `ActualCandidateVisit` はそれぞれ実 root と、独立候補判断で実際に入った検査位置の指標。位置には候補出現、引数番号、親からの検査経路、型/行、元端点の別を保持する。 `CurrentCycle` は実グラフのその位置への非空閉路で、未完了出力の等式も含め、nominal の引数は通るが body は開かない。 `AuthorizedLower` は別の元データによる支持。possible port を visited としない。
- `GeneralHead`, `GeneralCapture`, `OrdinaryReceipt`, `TypedReceipt`, `GeneralNode`, `GeneralTree`, `GeneralTreeMeaning` は下記の穴を明示する作業名。既存 `SourceHead` と `ReceiptTree` にない形を既存名で潰さない。特に C368 の `Write.typed` の意味は unary 値引数で、任意の宣言モード・引数ベクトルの出力意味とはまだ同じではない。新たな型の扱いは仕様に既にあるものだけ。`NodeFrom event n` と `LiteralTreeFrom trace n` は同じ原始導出から来た記録を比較する関係（単なる key の等式や存在否定のための動作条件ではない）。標準化して等価な他の body の出力に取り替えない。Lean の `Prop` の証明同一性から選択イベントを読み取らない。ソースの候補/作者/配列イベントは明示のデータまたは独立な関係の添字に置く。S01 の `Tree` の key 列だけで同じ body event とみなさず、S02 と S11 が同じ実イベントの添字を運ぶ。出力記録 `OrderedReceipt` は出現付きの literal な順序列で、固定 target と実作者・版・ordinal をすり替えない。出力受け口が複数の要求で共有される場合も、元要求での出力名/ordinal/target を記録してから、承認された需要合流の整合性を別に扱う。

## 1. 出発点: 独立な導出から、実際に選ばれた一回の出現へ

### S01 · 未証明 — `classifies_unpacks_actual_source`

```lean
theorem classifies_unpacks_actual_source {s : State} {q : Request} {d : Dictionary}
    (h : Classifies s q (.selected d)) :
    ∃ t : Tree, ∃ tree : Resolves (LocalSource s) q t,
      ∃ trace : SourceTreeTrace s q t tree, Summarizes t (.selected d)
```

選択分だけの仮定は足さない。独立な有限導出を正規診断に投影する API を実装し、その具体的な導入則が扱う全ての形から導く。`SourceTreeTrace` は各ルールが観測した宣言出現、順序付き候補判断、原始 body/author イベントを記録する型で、結果の source receipt や semantic evidence は保持しない。証拠の個体を区別するのは計算可能な trace の側の値と対応関係。既存の汎用 resolver に未充足の `Protocol.Local` を与えるだけでは終わらない。integration の `GeneralDeclarativeWitnessClassifyVariance357.dictionary_sound` も `SourceChecked`、`Coverage`、`Declared` を別に要求し、`Rule` は旧 ordinary と限定 unary join の場合分けなので S01/S13 の固定 API ではない。

### S02 · 一部 — `selected_source_inversion`

```lean
theorem selected_source_inversion {s : State} {q : Request} {key : Nat} {kids : List Request}
    (h : LocalSource s q (.selected key kids)) (event : SourceLocalTrace s q key kids h) :
    ∃ sel : SelectedSource s q key kids,
      sel.row.id = key ∧ sel.row ∈ visible s q ∧ sel.orderedRows = visible s q ∧ SelectionFrom event sel
```

既存: `State365.visible_exact` と `Tape367.live_readback` はフィルタの所属と既にある tape の選択候補を復元するが、全形の独立判断の反転で同じ出現と元順序を得るところは未証明。C357 の別前提 `SourceChecked` は ID 列の `Nodup` を含むが、これを固定文へ持ち込まず、actual declaration table の原始導出で必要な一意性を示す。

### S03 · 一部 — `selected_mixed_k2_priority`

```lean
theorem selected_mixed_k2_priority (sel : SelectedSource s q key kids) :
    (∀ v : OrdinaryRoot s q, ¬ CurrentCycle s v.site) ∧
    VisitExactlyNeeded sel ∧
    (∀ v : ActualCandidateVisit sel, AuthorizedLower s v ∧ ¬ CurrentCycle s v.site) ∧
    (∀ row ∈ visible s q, ¬ SourcePending sel row) ∧
    (∀ row ∈ visible s q, SourceMatch sel row → SourceOccurrence sel row = sel.occurrence)
```

既存: `Selection367.root_recurrence_vetoes_tape`, `NormalizedPrefix368.normalized_actual_prefix_k2`, `ReturnRankCore370.local_return_rank_iff_no_cycle`, C377–379 の後記アンカーは実普通位置・一部 native 入口を扱うが、全ての実訪問と同一候補順の根拠は未証明。候補の衝突/同一性は、選択規則が使う authored identity と照合する。もし規則が一意なキーしか与えないなら、同じキーが同じ出現を指すことを台帳の導出から示す（任意の `State` に新しい全域一意性仮定を足さない）。

**優先順位の監査:** I-59 の root K2 は lower がまだ展開できない場合も先行する。候補内の K2 は独立に支持された lower から本当に調べる必要のある非変数位置に限る。`VisitExactlyNeeded` の両方向（出力された位置が本物か、必要な訪問の取り落としがないか）を確かめる。retained release が 1 つ読めるだけではこの coverage は出ない。無支持なら正の保留理由を保持し、単なる未対応・`none` を不一致とも K2 ともしない。保留で等式を捨てない。調べるべき候補のいずれかで K2 が分かれば、安全な候補が一つでも複数でも先に拒否する。候補リスト順に早抜けして選ばない。候補で見ていない off-trace の循環から選択を否定しない。先行 native 入口に両端完成済みの `ModeWindow` を要求しない。相反する値を一つの論理名で同一視しない。

### S04 · 一部 — `elected_occurrence_has_general_head`

```lean
theorem elected_occurrence_has_general_head
    (sel : SelectedSource s q key kids) (guard : SelectedPriority sel) :
    ∃ head : GeneralHead s q sel.row,
      SameAuthoredOccurrence sel head ∧ SameOrderedObservation sel head
```

`SelectedPriority sel` は S03 の結論全体の略記。既存: `Heads367.source_head_sound`, `WrittenHead365.actual_written_application_use`, `AuthoredDispatchMode379.actual_dispatch_uses_same_authored_value_variance` は既に観測した範囲で正しい。任意の同じ宣言の引数に、正本の種類・分散、実元端点、文脈を選択導出から付与する producer は未証明。nullary と不在、外側からの invariant、反変の逆向き、unused の構文確認を区別する。

### S05 · 一部 — `selected_actual_ordered_capture`

```lean
theorem selected_actual_ordered_capture (sel : SelectedSource s q key kids)
    (head : GeneralHead s q sel.row) (same : SameAuthoredOccurrence sel head)
    (observed : SameOrderedObservation sel head) :
    ∃ capture : GeneralCapture s q sel.row head,
      SameOrderedSpans sel capture ∧ SelectedTieRows sel capture
```

既存: `Capture366.selected_centers_sound` と `PostselectionTies368.receipt_repeated_centers` は与えられた正確な捕捉と保持等式の意味を示すが、選択された実出現の全ての端点・残余・順序・中心等式を一つの producer で得ていない。

I-61 に従い、独立端点から可視 field と open/closed 残余を作る場合に中心の行の支持を要求しない。I-58 は選択後に実中心の等式を足す。端点の等値から実中心を同一としない。合流した payload は承認された位置で丸ごと捕捉し、型の同値から分割を復元しない。

## 2. 同じ出現の where と実際の書き込み

### S06 · 一部 — `selected_ordinary_literal_receipt`

```lean
theorem selected_ordinary_literal_receipt (sel : SelectedSource s q key kids)
    (capture : GeneralCapture s q sel.row head)
    (spans : SameOrderedSpans sel capture) (ties : SelectedTieRows sel capture)
    (branch : SourceBodyCase sel .ordinary) :
    ∃ r : OrdinaryReceipt s q sel.row kids, ExactSelectedReceipt sel capture r
```

既存: `SourceBodyProduction371.ordinary_fixed_inputs_produce_body`, `DirectDeclaredTarget371.direct_output_target_uses_declaring_equation`, `RetainedEvent372.retained_body_facts_at_same_current` は実コンパイラ・割当・保持を結ぶ限定定理。任意の選択からその同じ allocator、実 where、固定出力、保持等式、子の宣言を回収する部分は未証明。

### S07 · 一部 — `selected_typed_actual_owner_and_retention`

```lean
theorem selected_typed_actual_owner_and_retention (sel : SelectedSource s q key kids)
    (capture : GeneralCapture s q sel.row head)
    (spans : SameOrderedSpans sel capture) (ties : SelectedTieRows sel capture)
    (branch : SourceBodyCase sel .typedOrMixed) :
    ∃ r : TypedReceipt s q sel.row kids,
      ExactSelectedReceipt sel capture r ∧ ExactTypedOwners s sel r ∧
      RetainedCurrentWrites s r ∧ ExactIndependentReleaseUse s sel r
```

既存: `PreparedOwnBody376.same_prepared_author_in_finished_and_typed_body`, `CurrentRelease376.checked_install_opens_iff_granted`, `JoinBody368.current_typed_write_exact` は実 prepared・現在同じ write の配列・独立 grant を結ぶが、一般の選択からその writer occurrence/role/declaration/version/sourceOrdinal/outputOrdinal/output name/fixed target/source equation と同じ現在盤面を回収できていない。C376 の `one_authored_preparation_keeps_ordered_and_typed_meaning` の追加観測 `observes` は一般の `Fits s m` からの射影がまだ無い。その仮定を固定文に追加せず、S07 の保持と S09 の解釈を接続して初めて使う。

`ExactIndependentReleaseUse` は **実際に出力を支持として読んだ箇所**の独立 grant だけを求める。全ての書き込みに release 済みを要求したり、下流の fit・同名/同値・install 成功から grant を作ったりしない。`ExactSelectedReceipt` は、選択の where が返す literal `kids = children q demands`、全子の実宣言、同じ捕捉からの固定出力、ordinal と target の逐一一致を含む。S06/07 の `SourceBodyCase` は S02 で反転した実 body 規則のどちらかであり、対応できない入力を排除する条件ではない。

### S08 · 一部 — `ordinary_or_typed_node_assembly`

```lean
theorem ordinary_or_typed_node_assembly (sel : SelectedSource s q key kids)
    (head : GeneralHead s q sel.row) (capture : GeneralCapture s q sel.row head)
    (same : SameAuthoredOccurrence sel head) (spans : SameOrderedSpans sel capture)
    (ties : SelectedTieRows sel capture)
    (body : ExactReceiptFor sel capture) :
    ∃ n : GeneralNode s q sel.row kids, NodeFromSelected sel n
```

`ExactReceiptFor` は S06 又は S07 の結論（証拠はこの出現に固定）。既存: `Body367.authored_node` と `UnionReceipts368.SourceReceipt` の二つの導入形は、普通・限定 mixed の組立を与える。宣言表の全ての出力種別/引数を保つ一般 node は未実装。

### S09 · 一部 — `general_local_meaning`

```lean
theorem general_local_meaning (n : GeneralNode s q row kids)
    (m : Model) (fit : Fits s m) : GeneralNodeMeaning n m
```

既存: `UnionReceipts368.source_receipt_in_one_model` は ordinary と既存 typed carrier に対し、head・子順・全子宣言・targets・普通等式・unary native 観測を同じモデルで得る。C360 の `Code` も recursive unary spine であり、nested には使えても任意の型/行ベクトルを表したとは言わない。広い carrier で型/行と文脈を同じ `m` で意味づける部分は未証明。固定出力を自由な値にしたり、別モデルへの付け替えで閉じたりしない。

### S10 · 未証明 — `selected_frontier_to_general_node`

```lean
theorem selected_frontier_to_general_node (s : State) :
    ∀ q key kids (h : LocalSource s q (.selected key kids))
      (event : SourceLocalTrace s q key kids h),
      ∃ row : Declaration, ∃ n : GeneralNode s q row kids, row.id = key ∧ NodeFrom event n
```

S02 の反転は `SelectedSource` が同じ独立導出の `event` に由来する事実（`SelectionFrom h sel`）を返す。これと S08 の `NodeFromSelected` を結んで `NodeFrom` を得る。S02→S03→S04→S05 で選ばれた同じ出現を保持し、S02 の実 body 導出の型で S06/S07 に分けて S08 に渡す。外部入力として選択・receipt・grant・モデルを要求しない。S09 はここで使わない。

## 3. 有限順序木の組立と同一モデル

### S11 · 一部 — `lower_selected_general_tree` / forest

```lean
def ProvidesGeneralNode (s : State) : Prop :=
  ∀ q key kids (h : LocalSource s q (.selected key kids))
      (event : SourceLocalTrace s q key kids h),
    ∃ row : Declaration, ∃ n : GeneralNode s q row kids, row.id = key ∧ NodeFrom event n

theorem lower_selected_general_tree (lower : ProvidesGeneralNode s)
    (t : Tree) (tree : Resolves (LocalSource s) q t)
    (trace : SourceTreeTrace s q t tree) (summary : Summarizes t (.selected d)) :
    ∃ written : List OrderedReceipt, ∃ lowered : GeneralTree s q d written,
      t = dictionaryTree d ∧ LiteralTreeFrom trace lowered

theorem lower_selected_general_forest (lower : ProvidesGeneralNode s)
    (trees : List Tree) (ds : List Dictionary)
    (tree : All₂ (Resolves (LocalSource s)) qs trees)
    (trace : SourceForestTrace s qs trees tree) (summary : All₂ Summarizes trees (ds.map Result.selected)) :
    ∃ written : List OrderedReceipt, ∃ lowered : GeneralForest s qs ds written,
      trees = dictionaryForest ds ∧ LiteralForestFrom trace lowered
```

一つの相互帰納ブロックとして 1 件。既存: `Lowering365.lower_tree` / `lower_forest` は普通 `SourceTree`・`FixedReceipt` に対して完全。一般 node を順序木に積み、ルートの記録を先頭へ、兄弟を元順で連結する版は未証明。S01 の source trace を子ごとに反転する際には、順序付きの relation とその添字を同時に消去する。元からある有限の導出に対する帰納であり、実行器の停止性や `Acc` を求めない。

### S12 · 一部 — `general_tree_sound`

```lean
theorem general_tree_sound (tree : GeneralTree s q d written)
    (m : Model) (fit : Fits s m) : GeneralTreeMeaning s m q d written
```

既存: P03 の `emitted_receipt_tree_sound` は既存の普通/unary typed の混在順序木に対して完全。一般化した各 node に S09 を使う相互帰納版は未証明。親・全子・全固定出力は一つの `s,m,fit` を共有する。出現または fixed target の類似から別の記録を代入しない。

### S13 · 未証明 — `general_meaning_to_dictionary`

```lean
theorem general_meaning_to_dictionary
    (literal : t = dictionaryTree d) (replay : LiteralTreeFrom tree t lowered)
    (meaning : GeneralTreeMeaning s m q d written) :
    DictionaryEvidence s m q d
```

`lowered : GeneralTree s q d written` は `replay` の暗黙の添字。固定結論の実 API を設け、正確な `d`、全 occurrence、literal な子順と固定出力順、全型/行 carrier の意味を保って包む。独立意味が満たされることを仮定する別名でも、`written` を消して意味を弱める projection でもない。最上段を閉じるため独立の未証明行に数える。

## 4. 証明済みの部品と固定アンカー

下記 P 行は証明済み **として使う命題の全範囲**。狭い定理を広い S 行の証明済みへ数え替えない。パスはすべて `lean/Yulang/`、参照は冒頭の immutable integration commit。表の prefix `GeneralDeclarativeI65` はファイル名のみ省略。特記のない定理の namespace は `Yulang.GeneralDeclarativeI65` 又は同ファイル内の子 namespace。

### P01 · 証明済み — `visible_exact`

```lean
theorem visible_exact (s : State) (q : Request) (d : Declaration) :
  d ∈ visible s q ↔ d ∈ (authoredRegistry s.current).declarations ∧ d.role = q.demand.role
```

`GeneralDeclarativeI65State365.lean`。S02 のフィルタ、S03 の実順の基礎（所属定理自体は順序定理ではない）。

### P02 · 証明済み — `source_receipt_in_one_model`

```lean
theorem source_receipt_in_one_model {s : State} {q : Request} {row : Declaration}
    {pick : AuthoredCandidate s q row} {kids : List Request}
    (receipt : SourceReceipt pick kids) (m : Model) (fit : Fits s m) :
    ReceiptMeaning receipt m
```

`GeneralDeclarativeI65UnionReceipts368.lean`。S08/09。receipt は独立選択から既に得た場合に限る。

### P03 · 証明済み — `emitted_receipt_tree_sound`

```lean
theorem emitted_receipt_tree_sound {s : State} {q : Request} {d : Dictionary}
    {written : List OrderedWriteReceipt} (tree : ReceiptTree s q d written)
    (m : Model) (fit : Fits s m) : ReceiptTreeMeaning s m q d written
```

`GeneralDeclarativeI65MixedReceiptTree368.lean`。S12 の相互帰納の骨格。ここでの型は S11/12 の一般型と同一とは主張しない。`ModeWindow` や型付きの完了した比較があるから native の早い訪問がある、という逆向きは使わない。

### P04 · 証明済み — `every_written_receipt_in_one_model`

```lean
theorem every_written_receipt_in_one_model {s : State} {m : Model} {q : Request}
    {d : Dictionary} {written : List OrderedWriteReceipt}
    (evidence : ReceiptTreeMeaning s m q d written) :
    ∀ w ∈ written, WrittenIn m w
```

`GeneralDeclarativeI65MixedReceiptTree368.lean`。S13 用の分配定理。ただしリストの順序そのものは membership からでなく構成子で保持する。

### 既存部品の割当（S 行の再確認先・追加の本数にはしない）

| 行 | integration の実ファイルと引用する定理 |
|---|---|
| S01/S11 | `GeneralDeclarativeI65Lowering365.lean`: `lower_tree`, `lower_forest`, `classified_source_assembly`; ordinary scoped conditional のみ |
| S02 | `GeneralDeclarativeI65Tape367.lean`: `live_readback`, `tape_waiting_origin`, `every_nonlive_unblocked_row_is_a_real_miss`; `GeneralDeclarativeI65Selection367.lean`: `actual_matched_row` |
| S03 | `GeneralDeclarativeI65NormalSupport368.lean`: `supported_entry_origin`; `GeneralDeclarativeI65NormalizedPrefix368.lean`: `normalized_actual_prefix_k2`, `normalized_pending_row_changes_k2_without_support`; `GeneralDeclarativeI65ReturnRankCore370.lean`: `local_return_rank_iff_no_cycle`; `GeneralDeclarativeI65EarlyPorts369.lean`: `endpoint_port_from_one_original`, `endpoint_port_agrees_with_job`; `GeneralDeclarativeI65NativePrefixCore377.lean`: `native_value_port_at_literal_job`; `GeneralDeclarativeI65OrdinaryCrossingRoot378.lean`: `some_ordinary_visit_iff_inspects`; `GeneralDeclarativeI65EnteredOrdinaryRoot379.lean`: `entered_ordinary_root_keeps_pending_equations_for_k2`; `GeneralDeclarativeI65ScopedNativeCalls379.lean`: `second_position_requires_positive_first` |
| S04 | `GeneralDeclarativeI65State365.lean`: `mode_window_sound`; `GeneralDeclarativeI65Comparison365.lean`: `in_same_model`; `GeneralDeclarativeI65Heads367.lean`: `source_head_sound`; `GeneralDeclarativeI65RouteTag368.lean`: `distinct_route_excludes_match`; `GeneralDeclarativeI65AuthoredDispatchMode379.lean`: `actual_dispatch_uses_same_authored_value_variance` |
| S05 | `GeneralDeclarativeI65Capture366.lean`: `value_binding_sound`, `row_binding_sound`, `selected_centers_sound`; `GeneralDeclarativeI65Deep366.lean`: `deep_reads_retain_all_sources`; `GeneralDeclarativeI65Compiler367.lean`: `actual_port_center`; `GeneralDeclarativeI65PostselectionTies368.lean`: `receipt_repeated_centers` |
| S06 | `GeneralDeclarativeI65SourceBodyProduction371.lean`: `ordinary_fixed_inputs_produce_body`, `fixed_root_targets_do_not_erase_literal_child_allocation`; `GeneralDeclarativeI65DirectDeclaredTarget371.lean`: `direct_output_target_uses_declaring_equation`; `GeneralDeclarativeI65RetainedEvent372.lean`: `retained_body_facts_at_same_current`; `GeneralDeclarativeI65IndependentlySelectedWhere379.lean`: `selected_native_root_keeps_literal_child_occurrence`（独立に選択済み、親の固定出力は空） |
| S07 | `GeneralDeclarativeI65NativePrefix369.lean`: `current_release_actual_at_origin`, `original_from_installed_and_retained_author`; `GeneralDeclarativeI65CurrentRelease376.lean`: `checked_install_opens_iff_granted`, `same_target_different_source_address_not_open`; `GeneralDeclarativeI65PreparedOwnBody376.lean`: `one_authored_preparation_keeps_ordered_and_typed_meaning`; `GeneralDeclarativeI65JoinBody368.lean`: `current_typed_write_exact` |
| S08/S09 | `GeneralDeclarativeI65Body367.lean`: `authored_node`, `attached_source_sound`; `GeneralDeclarativeI65UnionReceipts368.lean`: `source_receipt_in_one_model`; `GeneralDeclarativeI65JoinBody368.lean`: `chosen_typed_literal_body_sound` |
| S12/S13 | `GeneralDeclarativeI65MixedReceiptTree368.lean`: P03/P04; `GeneralDeclarativeI65SourceTree365.lean`: `source_tree_sound`, `every_fixed_row_comes_from_the_same_model` |

| S02/S03 | `GeneralDeclarativeI65Origins367.lean`: `actual_route_iff`, `physical_origin_is_not_logical_equality`; `GeneralDeclarativeI65Rivals367.lean`: `rigid_candidate_excludes_a_source_head`; `GeneralDeclarativeI65AuthoredPrefix368.lean`: `ordinary_prefix_veto_independent_of_choice`; `GeneralDeclarativeI65ActualUnaryDispatch379.lean`: `authored_prefix_and_unary_dispatch_agree`; `GeneralDeclarativeI65ActualCandidateOrder379.lean`: `first_authored_unary_entry_before_second_candidate`（実 unary の継続であり全候補の優先順位ではない） |
| S04/S05 | `GeneralDeclarativeI65WrittenHead365.lean`: `actual_written_application_use`; `GeneralDeclarativeI65OriginArity365.lean`: `same_mode_vector_at_both_origins`; `GeneralDeclarativeI65Obligations365.lean`: `context_arguments_of_needs`; `GeneralDeclarativeI65Reflection365.lean`: `reflects_existing_compiler`; `GeneralDeclarativeCompoundHeads338.lean`: `record_seen`（既存の独立 source に結ばれた普通側） |
| S08/S09 | `GeneralDeclarativeI65ExistingCases365.lean`: `ordinary_and_joined_share_model`; `GeneralDeclarativeI65SourceNode365.lean`: `source_node_sound`; `GeneralDeclarativeI65LiteralTypedBody368.lean`: `typed_written_all_models`; `GeneralDeclarativeI65TypedOutputs365.lean`: `typed_fixed_route_sound`; `GeneralDeclarativeWitnessFullIntervals357.lean`: `in_current_full_model`; `CommonRecursiveNominalIntervalContextAdmission.lean`: `compile_in_context_exact` |

## 5. 依存とカウントの監査

```text
独立宣言 API  S01 ────────────────────────────────────────┐
局所 producer S02 → S03 → S04 → S05 → S06 or S07 → S08 → S10
                                                              ↓
有限導出に帰納して literal tree/forest を得る                S11
                                                              ↓
各 node の同一モデル意味 S09 ─────────────────────────────→ S12
                                                              ↓
固定した公開結論の実 interface                              S13
```

矢印は証明の依存（S10 が S02〜S08 全部を、S11 が S01/S10 を、S12 が S09/S11 を使用）。P01–P04 の見出しは狭い再利用定理。S 行は一回ずつ数え、forest は S11 と同一の相互帰納単位。S01 の `Resolves` は同じ `s` を参照する。途中で子が付け足した等式や native write は、実導出が現在の `s` に保持したという S06/S07 の対応を通す。証拠のないスナップショットの固定化、兄弟の交換、可換な意味を利用した順序消去では補わない。I-60 どおり、その位置を判断するための支持付き読みや原始的な author/発行規則を宣言的導出の材料にできる。S01 の本物の規則を実装する際、S02–S07 の**複合結論**を証明済みフィールドとして詰めない。特に S03 の実検査位置・優先順位は proof of acceptance でなく、その独立導出からの保存/反転の目標。S01/S02 の source event は原始規則で成立したものを指し、成功チェッカや派生 `ReceiptTreeMeaning`を backwards に使わない。S09 以外の source → receipt 側では `Fits`、モデル選定、checker を使わない。新しい行を足す場合はその理由と依存の入れ替えをこの節へ 1 行で記録する。


### 最初に行う S01 の確認点

1. 正本で監査するのは `Classifies` の限定実装を呼ぶかどうかでなく、`State` と実原始導出から `LocalSource` の入力が揃うか。宣言の順番・実出現・kind/mode の出どころを現台帳から読む。 `Fits` の同じ syntax/値だけでは異なる source route の区別を証明できない（S02/S04）。
2. 診断木は root/候補検査規則と where 子の要約を別の段に置く。K2 は S03 の root/候補検査であり、子リストやモデルの fold から逆算しない。辞書全体を再帰して既に選択したかを判定する循環を作らない（S01 と S11 の分離）。
3. 実 carrier の負の監査として既存の `ReleaseErasure368.no_erasure_of_ready_authority`（`GeneralDeclarativeI65ReleaseErasure368.lean`）と `CurrentRelease376.same_target_different_source_address_not_open` を使う。同じ普通状態、同じ target だけを入力とする producer は authority を復元できない。C365 の `State.current` の `Current` には `environment, ordinary, visible` のみがあり、C360 の `Board.active/writes` と `ReleaseAuthority.grants` はそこからの射影として定義されていない。原始 source fact の同じ状態への attachment は調べるが、任意の新規 grant を許す存在量化にはしない。S01 で正当な原始根拠が現在の `State` に足りない場合、それを S01 の表現課題として報告する。閉じないケースを無断で保留や拒否へ寄せない。
4. `ReceiptMeaning` が exact local order と typed write を型に持っていても、その後の `WrittenIn` は各要素の意味の投影でしかない。S13 を P04 の集合化だけで閉じず、辞書の木構造に固定した全列を保持する。

次は S01（独立規則と正規診断 API）。その行で全形を確認し、先に他の行を閉じたことにしない。I-65 step 2/3 は未着手。C は後回し。S1/S2 の全体は閉じない。停止性・旧 `Local`・旧 C334 への橋・追加 fixture はこの一覧に含めない。

**未解決 13 件 = 未証明 3 件（S01・S10・S13） + 一部 10 件（S02–S09・S11–S12）。証明済みの再利用 4 件（P01–P04）は除外。**
