# I-65 step 1: `dictionary_sound` の証明骨組み（C380 / I-66）

正本: `momota1029/yulang@a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6` (`integration/m1-final`), inbox blob `b99fbb19f8c0c8c05abcd09f4cf3f44cfd4de26e`。下記の既存の証拠はすべてこの integration のファイルから読んだ。比較対象の作業ブランチは `820e4f2bb26aa02e6a1933d141a2b877900c328b`。該当 I-65 ファイルが両方にあることと、任意の状態の結論が証明済みであることは別。

## I-67 での層の訂正（C383）

- 正本は `momota1029/yulang@d24d654817367e7a565b1ee97c1306931332d19d` の `notes/plan/dots-inbox.md`（blob `a87744968aacd0c51cf7f82e263009a914ed48c6`）。宣言側に solver の作者・版・physical write/release・manifest/grant を持たせない。C381/C382 の「消した権限は復元できない」は検査器側で役立つが、S01 の不足項目ではない。
- 宣言側で出力の支持となる「完了」は **同じ状態における実 producer の有限 `.selected d` 導出**。source の出力位置と、その位置から独立な宣言的規則が導いた等式を区別する。出力 target の等しさだけではその producer の等式にならない。
- S01–S03 を下記のとおり訂正。固定文・行数・状態ラベルは据え置き。S04 以降の旧 draft に物理作者/版/grant を要求する記述が残る箇所は、I-67 により **step 2/3 に留保**。step 1 の追加前提として読み替えない。S07 等を閉じたとはみなさない。

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
  obtain ⟨written, lowered, literal, replay⟩ :=
    (lower_selected_general (selected_frontier_to_general_node (s := s))).tree
      t tree trace summary                                                 -- S10, S11
  exact general_meaning_to_dictionary literal replay
    (general_tree_sound lowered m fit)                                   -- S12, S13
```

### 記号と境界

- 実在する型は `State`, `Request`, `Model`, `Fits`, `children`, `visible`（`GeneralDeclarativeI65State365.lean`）、`Tree`, `Frontier`, `Dictionary`, `Resolves`, `Summarizes`, `All₂`（`CommonRoleOutermostResolver.lean`）。C365 の `State` は `current, modes, origins, routes` を持つ。全称の型の識別子は固定文を変えない。C365 の表現が仕様の全形を本当に表せるかも S01/S04/S07/S09/S13 で確認し、追加の不変条件が必要なら既存の宣言的導出から示す（定理の仮定に追加しない）。`Fits` はモデル解釈であり、候補の選択や release を表さない。
- 下記の `LocalSource s` は **これから実現する独立な規則**。`Classifies` の固定 API と一緒に S01 で具現化する。旧 `Local` の別名でも、checker の成功判定でもない。読んだ integration の I-65 モジュールでは全称の `Classifies` / `DictionaryEvidence` は見つからなかった。S13 が後者の実 API を具現化する。これらは仮定や無償の別名にしない。
- `SelectedSource s q key kids` は S02 の中間データ。実 root 構文、選択されたソース宣言の出現、元の順序付き候補判断（成功・不一致・保留の理由）、その規則の body 導出と子リストを持つ。比較の意味、受理証明、`SourceReceipt` はフィールドにしない。
- `OrdinaryRoot`, `ActualCandidateVisit` はそれぞれ実 root と、独立候補判断で実際に入った検査位置の指標。位置には候補出現、引数番号、親からの検査経路、型/行、元端点の別を保持する。 `CurrentCycle` は実グラフのその位置への非空閉路で、未完了出力の等式も含め、nominal の引数は通るが body は開かない。 `DeclarativeLower` は直接の source 制約又は同じ状態で有限に選択された logical producer による支持で、manifest/grant ではない。possible port を visited としない。
- `GeneralHead`, `GeneralCapture`, `OrdinaryReceipt`, `TypedReceipt`, `GeneralNode`, `GeneralTree`, `GeneralTreeMeaning` は下記の穴を明示する作業名。既存 `SourceHead` と `ReceiptTree` にない形を既存名で潰さない。特に C368 の `Write.typed` の意味は unary 値引数で、任意の宣言モード・引数ベクトルの出力意味とはまだ同じではない。新たな型の扱いは仕様に既にあるものだけ。`NodeFrom event n` と `LiteralTreeFrom trace n` は同じ原始導出から来た記録を比較する関係（単なる key の等式や存在否定のための動作条件ではない）。標準化して等価な他の body の出力に取り替えない。Lean の `Prop` の証明同一性から選択イベントを読み取らない。ソースの候補/作者/配列イベントは明示のデータまたは独立な関係の添字に置く。S01 の `Tree` の key 列だけで同じ body event とみなさず、S02 と S11 が同じ実イベントの添字を運ぶ。出力記録 `OrderedReceipt` は出現付きの literal な順序列で、固定 target と実作者・版・ordinal をすり替えない。出力受け口が複数の要求で共有される場合も、元要求での出力名/ordinal/target を記録してから、承認された需要合流の整合性を別に扱う。

## 1. 出発点: 独立な導出から、実際に選ばれた一回の出現へ

### S01 · 未証明 — `classifies_unpacks_actual_source`

```lean
theorem classifies_unpacks_actual_source {s : State} {q : Request} {d : Dictionary}
    (h : Classifies s q (.selected d)) :
    ∃ t : Tree, ∃ tree : Resolves (LocalSource s) q t,
      ∃ trace : SourceTreeTrace s q t tree, Summarizes t (.selected d)
```

選択分だけの仮定は足さない。候補照合で一意になっただけの状態を最終の `.selected d` にしない。実 where・選択後の等式・固定出力の診断を保持する。`SourceTreeTrace` には実宣言出現・順序付き候補判断・論理的出力発生の導出を記録し、**読むための producer の選択導出**と **辞書に入る where 子**を別の辺とする。前者を辞書の子に混ぜない。どちらも同じ `s` を参照する。有限導出の子に producer 証拠を置き、各段で循環を使って自分自身を正当化しない。存在するある producer 導出の深さを実行順や一様 bound とは解釈しない。`Fits`、物理作者、版、grant、checker 受理、source receipt の意味のどれも入口に使わない。

C383 の [`FiniteCompletion383`](../../lean/Yulang/GeneralDeclarativeI65FiniteCompletion383.lean) は独立な **正の実局所規則がすでに与えられる場合**について、同じ状態での有限 `.selected` 支持、閉じた循環族の排除、where 側だけの `Resolves/Summarizes` 投影を Lean で検証した。さらに [`CompletionExact383`](../../lean/Yulang/GeneralDeclarativeI65CompletionExact383.lean) で、この正の規則インターフェース上の有限証明と、同じ辞書を返す `.selected` 投影の同値を両方向に示した。これは実規則の供給でも、四種すべての診断でもない。最終 snapshot の候補判定を局所の証人が自分に都合のよい完了集合に絞ることはしない。証拠を増やすと別候補も見える可能性があり、「正の読み根拠の増加」と「一意選択の保存」は別。実 source 規則で、全可視候補と実際に必要な検査を同じ安定状態で判断するところは S01–S03 に残す。

### S02 · 一部 — `selected_source_inversion`

```lean
theorem selected_source_inversion {s : State} {q : Request} {key : Nat} {kids : List Request}
    (h : LocalSource s q (.selected key kids)) (event : SourceLocalTrace s q key kids h) :
    ∃ sel : SelectedSource s q key kids,
      sel.row.id = key ∧ sel.row ∈ visible s q ∧ sel.orderedRows = visible s q ∧
      LogicalInputSupports s sel ∧ SelectionFrom event sel
```

既存: `State365.visible_exact` と `Tape367.live_readback` はフィルタの所属と既にある tape の選択候補を復元するが、全形の独立判断の反転で同じ出現・元順序・`LogicalInputSupports`（直接の制約、又は実論理出力位置と同じ状態の有限選択導出を持つ支持）を得るところは未証明。`visible` は現在台帳を role で filter するだけなので、台帳が [呼出し側の実可視集合](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/spec/06-roles.md#L70-L75) を表すことも示す。全 where 子で同じ根の可視範囲を使い、重複 import は同じ宣言、別ファイルの別宣言は異なる出現として扱う。グローバル coherence や孤児規則は要求しない。[`LogicalOrdinaryOutput383`](../../lean/Yulang/GeneralDeclarativeI65LogicalOrdinaryOutput383.lean) は、**実選択・捕捉を別途保持した** ordinary 出力について、実宣言の等式から元の出力 ordinal を得て、同じ状態の有限の producer 選択と結ぶ。[`LogicalNominalOutput383`](../../lean/Yulang/GeneralDeclarativeI65LogicalNominalOutput383.lean) は同じ境界から、明示された unary covariant tagged 出力に限り、元 ordinal・target・実 binder の中心と同じ適合モデルでの値を結ぶ。任意の typed 出力、既存 `NativeSyntax` への接続、実選択の供給は対象外。 [`OrdinarySupportGraph383`](../../lean/Yulang/GeneralDeclarativeI65OrdinarySupportGraph383.lean) は、普通下界の constructor 行だけでなく明示的な alias の各辺を同じ状態の支持付き読みで正当化することと、支持行だけの ordinary view 上の既存 `Knows` が同値であると証明した。通常の bounds と元グラフを変えず、K2 にはこの view を使わない。混合・native の候補全体の観測は残る。C357 の別前提 `SourceChecked` は ID 列の `Nodup` を含むが、これを固定文へ持ち込まず、actual declaration table の原始導出で必要な一意性を示す。

### S03 · 一部 — `selected_mixed_k2_priority`

```lean
theorem selected_mixed_k2_priority (sel : SelectedSource s q key kids) :
    (∀ v : OrdinaryRoot s q, ¬ CurrentCycle s v.site) ∧
    VisitExactlyNeeded sel ∧
    (∀ v : ActualCandidateVisit sel, DeclarativeLower s v ∧ ¬ CurrentCycle s v.site) ∧
    (∀ row ∈ visible s q, ¬ SourcePending sel row) ∧
    (∀ row ∈ visible s q, SourceMatch sel row → SourceOccurrence sel row = sel.occurrence)
```

既存: `Selection367.root_recurrence_vetoes_tape`, `NormalizedPrefix368.normalized_actual_prefix_k2`, `ReturnRankCore370.local_return_rank_iff_no_cycle`, C377–379 の後記アンカーは実普通位置・一部 native 入口を扱うが、全ての実訪問と同一候補順の根拠は未証明。候補の衝突/同一性は、選択規則が使う authored identity と照合する。もし規則が一意なキーしか与えないなら、同じキーが同じ出現を指すことを台帳の導出から示す（任意の `State` に新しい全域一意性仮定を足さない）。

**優先順位の監査** ([現 spec の保留](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/spec/06-roles.md#L182-L213)、[K2 の検査位置](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/spec/06-roles.md#L498-L500)): I-59 の root K2 は lower がまだ展開できない場合も先行する。候補内の K2 は独立に支持された lower から本当に調べる必要のある非変数位置に限る。`VisitExactlyNeeded` の両方向（出力された位置が本物か、必要な訪問の取り落としがないか）を確かめる。出力が等式一覧に在る、又は一つの producer が完了するだけでは全候補の coverage は出ない。C383 [`CompletionRead383`](../../lean/Yulang/GeneralDeclarativeI65CompletionRead383.lean) は循環族だけでは読みが成立しないこと、root cycle が元の普通グラフにあるなら読みの未完了にかかわらず root K2 が優先することを、入口に限って検証した。[`CompletionRootCycle383`](../../lean/Yulang/GeneralDeclarativeI65CompletionRootCycle383.lean) は、循環族からしか支持を得られない実 ordinary 名付き自己参照等式を元グラフから直接読んで root K2 を示し、同じ等式の支持付き read の不成立と両立することを示す。無支持なら正の保留理由を保持し、単なる未対応・`none` を不一致とも K2 ともしない。保留で等式を捨てない。調べるべき候補のいずれかで K2 が分かれば、安全な候補が一つでも複数でも先に拒否する。候補リスト順に早抜けして選ばない。候補で見ていない off-trace の循環から選択を否定しない。先行 native 入口に両端完成済みの `ModeWindow` を要求しない。相反する値を一つの論理名で同一視しない。

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

[I-61 の端点規則](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/spec/06-roles.md#L395) に従い、独立端点から可視 field と open/closed 残余を作る場合に中心の行の支持を要求しない。I-58 は選択後に実中心の等式を足す。端点の等値から実中心を同一としない。合流した payload は承認された位置で丸ごと捕捉し、型の同値から分割を復元しない。

## 2. 同じ出現の where と実際の書き込み

### S06 · 一部 — `selected_ordinary_literal_receipt`

```lean
theorem selected_ordinary_literal_receipt (sel : SelectedSource s q key kids)
    (capture : GeneralCapture s q sel.row head)
    (spans : SameOrderedSpans sel capture) (ties : SelectedTieRows sel capture)
    (branch : SourceBodyCase sel .ordinary) :
    ∃ r : OrdinaryReceipt s q sel.row kids, ExactSelectedReceipt sel capture r
```

既存: `SourceBodyProduction371.ordinary_fixed_inputs_produce_body`, `DirectDeclaredTarget371.direct_output_target_uses_declaring_equation`, `RetainedEvent372.retained_body_facts_at_same_current` は実コンパイラ・割当・保持を結ぶ限定定理。任意の選択からその同じ allocator、実 where、固定出力、保持等式、子の宣言を回収する部分は未証明。固定出力 target が同じでも local allocator が違えば子の実番号が変わる（C371）。source clause の literal 順序、割当消費数と開始番号、fallback/default を authored 側と突き合わせる。

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

既存: `PreparedOwnBody376.same_prepared_author_in_finished_and_typed_body`, `CurrentRelease376.checked_install_opens_iff_granted`, `JoinBody368.current_typed_write_exact` は実 prepared・現在同じ write の配列・独立 grant を結ぶが、一般の選択からその writer occurrence/role/declaration/version/sourceOrdinal/outputOrdinal/output name/fixed target/source equation と同じ現在盤面を回収できていない。C376 の `one_authored_preparation_keeps_ordered_and_typed_meaning` の追加観測 `observes` は一般の `Fits s m` からの射影がまだ無い。その仮定を固定文に追加せず、S07 の保持と S09 の解釈を接続して初めて使う。C360 の新規 install が `fresh` を要することと、仕様が需要の合流で同じ出力名を共有できることも別。既存 target/同じ作者の再利用を新規 install の証拠で済ませず、合流の各要求の元記録と実 retained row が揃うかを示す。合流を拒否する条件は足さない。

`ExactIndependentReleaseUse` は **実際に出力を支持として読んだ箇所**の独立 grant だけを求める。全ての書き込みに release 済みを要求したり、下流の fit・同名/同値・install 成功から grant を作ったりしない。`ExactSelectedReceipt` は、選択の where が返す literal `kids = children q demands`、全子の実宣言、同じ捕捉からの固定出力、ordinal と target の逐一一致を含む。S06/07 の `SourceBodyCase` は S02 で反転した実 body 規則のどちらかであり、対応できない入力を排除する条件ではない。型付きの**入力**から通常の等式だけを出す body は普通の書込み側に入れられる（C379 の where 部品）。全ての**出力**は実際の枝が選んだ表現のまま、mixed なら元の順序のまま一列で保持する。

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

### S11 · 一部 — `lower_selected_general`（tree/forest を返す一補題）

```lean
def ProvidesGeneralNode (s : State) : Prop :=
  ∀ q key kids (h : LocalSource s q (.selected key kids))
      (event : SourceLocalTrace s q key kids h),
    ∃ row : Declaration, ∃ n : GeneralNode s q row kids, row.id = key ∧ NodeFrom event n

structure LoweringPair (s : State) : Prop where
  tree : ∀ {q d} (t : Tree) (derived : Resolves (LocalSource s) q t),
    ∀ (trace : SourceTreeTrace s q t derived), Summarizes t (.selected d) →
      ∃ written : List OrderedReceipt, ∃ lowered : GeneralTree s q d written,
        t = dictionaryTree d ∧ LiteralTreeFrom trace lowered
  forest : ∀ {qs} (trees : List Tree) (ds : List Dictionary)
    (derived : All₂ (Resolves (LocalSource s)) qs trees)
    (trace : SourceForestTrace s qs trees derived),
    All₂ Summarizes trees (ds.map Result.selected) →
      ∃ written : List OrderedReceipt, ∃ lowered : GeneralForest s qs ds written,
        trees = dictionaryForest ds ∧ LiteralForestFrom trace lowered

theorem lower_selected_general (lower : ProvidesGeneralNode s) : LoweringPair s
```

順序木と forest の相互帰納を束ねた一補題なので 1 件。既存: `Lowering365.lower_tree` / `lower_forest` は普通 `SourceTree`・`FixedReceipt` に対して完全。一般 node を順序木に積み、ルートの記録を先頭へ、兄弟を元順で連結する版は未証明。S01 の source trace を子ごとに反転する際には、順序付きの relation とその添字を同時に消去する。`CommonRoleOutermostResolver.Combine.selected` の逆転は `results = ds.map Result.selected` を返し、`All₂` によって子リストの本数・順序が自動的に保たれる。元からある有限の導出に対する帰納であり、実行器の停止性や `Acc` を求めない。S11 で検査する分岐は (i) 非選択 leaf は `Summarizes` の constructor 不一致で消去、(ii) 選択 node は `Combine.selected` の反転と S10、(iii) forest の nil/cons は `All₂` の反転を trace の nil/cons と同時に行い、`writtenHead ++ writtenTail` をそのまま返す。

### S12 · 一部 — `general_tree_sound`

```lean
theorem general_tree_sound (tree : GeneralTree s q d written)
    (m : Model) (fit : Fits s m) : GeneralTreeMeaning s m q d written
```

既存: P03 の `emitted_receipt_tree_sound` は既存の普通/unary typed の混在順序木に対して完全。一般化した各 node に S09 を使う相互帰納版は未証明。親・全子・全固定出力は一つの `s,m,fit` を共有する。出現または fixed target の類似から別の記録を代入しない。

### S13 · 分割（親、件数外） — `general_meaning_to_dictionary`

```lean
theorem general_meaning_to_dictionary
    (literal : t = dictionaryTree d) (replay : LiteralTreeFrom tree t lowered)
    (meaning : GeneralTreeMeaning s m q d written) :
    DictionaryEvidence s m q d
```

`lowered : GeneralTree s q d written` は `replay` の暗黙の添字。固定結論の実 API を設け、正確な `d`、全 occurrence、literal な子順と固定出力順、全型/行 carrier の意味を保って包む。独立意味が満たされることを仮定する別名でも、`written` を消して意味を弱める projection でもない。最上段を閉じるため独立の未証明行に数える。

#### S13a · 証明済み（C386 検証済み、integration 未取込） — `general_literal_replay_alignment`

```lean
variable [ReplayJudgment] {s : State} {q : Request} {d : Dictionary}
  {written : List OrderedReceipt} {t : Tree}
  {tree : Resolves (LocalSource s) q t}
  {lowered : GeneralTree s q d written}

structure CanonicalDictionaryReplay
    (replay : LiteralTreeFrom tree t lowered) : Prop where
  ledger : ∃ events : LiteralEventTree,
    ExactReplayEvents replay events ∧
    ExactOrderedOccurrences (dictionaryTree d) events ∧
    orderedLiteralReceipts events = written

theorem general_literal_replay_alignment
    (literal : t = dictionaryTree d) (replay : LiteralTreeFrom tree t lowered) :
    CanonicalDictionaryReplay replay
```

`lowered : GeneralTree s q d written`、`tree` と他の添字は上の S13 と同じ。`LiteralEventTree` は選択された各論理出現と同じ source event、元順の where 子、元 ordinal/target を持つ literal receipt 列の木。`ExactReplayEvents` は渡された **その replay** の全 event と枝を同順に一対一対応させる（`Prop` の証明同一性から event データを復元しない）。`ExactOrderedOccurrences` は canonical tree の key **および各子の位置・本数**を一致させる tree/forest の構造対応。`orderedLiteralReceipts` は親の列を先に置き、子の列を元順で連結する。空出力の出現も落とさない。この行はモデルや意味を使わず、既存の限定 `ReceiptTree` への置換はしない。

S13a の再利用先（いずれもこの行の証明済み扱いではない）: [C349 の `dictionaryTree` と `dictionaryForest`](https://github.com/momota1029/yulang/blob/ac5ad01366d274d521c54a75d372d6d0cc1831aa/lean/Yulang/GeneralDeclarativeWitnessTree349.lean#L39) で canonical 子順を固定し、[C381 の `SourceEventTrace381`](https://github.com/momota1029/yulang/blob/ac5ad01366d274d521c54a75d372d6d0cc1831aa/lean/Yulang/GeneralDeclarativeI65SourceEventTrace381.lean#L19) のように実 event は data で持つ。[C368 の `ReceiptTree/Forest`](https://github.com/momota1029/yulang/blob/ac5ad01366d274d521c54a75d372d6d0cc1831aa/lean/Yulang/GeneralDeclarativeI65MixedReceiptTree368.lean#L24) は親 receipt、次に元順の forest を連結する既存の限定例。証明は渡された replay の tree/forest を同時に反転する。根を `literal` で置き換え、選択 key と子リストの構成子を消去し、forest の nil/cons の同じ位置で再帰する。各 event をそのまま一回記録し、子ごとの列の等式を連結する。読むためだけの producer subproof は where 子に加えない。S11 の lowering や S12 の意味に戻って元 event を作り直さない。

C386 の exact 証明: [`GeneralDeclarativeI65CanonicalReplay386.lean` · `general_literal_replay_alignment`](https://github.com/momota1029/yulang/blob/d9c995bc155d07ac0144b494f0302aaa1f62f7d8/lean/Yulang/GeneralDeclarativeI65CanonicalReplay386.lean) と [実データ carrier](https://github.com/momota1029/yulang/blob/d9c995bc155d07ac0144b494f0302aaa1f62f7d8/lean/Yulang/GeneralDeclarativeI65LiteralReplay386.lean)。`ReplayJudgment` は既存の作業名 `LocalSource` とその独立 event 関係を束ねる一般 interface で、この補題はすべての judgment に対して成立する。元の二つの明示前提から、別のモデル・局所健全性・新たな source 許可を要求しない。S01 の一般の判定規則を実装した意味ではない。

source trace と lowered tree を同じ局所 event で対にする導出から、元 event を一度ずつ取り出す。元 where の clause ordinal と実要求順、元 output ordinal/name/target、全宣言 value/row の引数ベクトルと literal 型構文を残す。両側から独立に ledger を突合して、与えられた canonical tree の key／子束と exact receipt 列を相互帰納で得る。対象は任意の有限の literal tree/forest。Lean 4.35.0 trust 0 / 警告をエラー扱い、Git exact bytes の再構築と独立監査 PASS。定理の依存公理は `propext` と `Quot.sound`。

#### S13b · 分割（親、件数外） — `aligned_general_meaning_to_dictionary`

元の文をそのまま残す。

```lean
theorem aligned_general_meaning_to_dictionary
    {replay : LiteralTreeFrom tree t lowered}
    (alignment : CanonicalDictionaryReplay replay)
    (meaning : GeneralTreeMeaning s m q d written) :
    DictionaryEvidence s m q d
```

**分割理由（C387 / I-68）:** 意味を同一の実 event ledger へ移す相互帰納と、各型付き出力の一般の評価・固定先の保持を辞書証拠として実現する義務は別である。前者は任意の独立局所意味で成立する。後者は `d/q/written` の一致・構文の保持・同じ `Fits` だけでは成立しない。親・最上段の文は変えない。

##### S13ba · 証明済み（C388 検証済み、integration 未取込） — `aligned_same_event_semantics`

```lean
theorem aligned_same_event_semantics
    {P : LiteralEvent s → Prop}
    {replay : LiteralTreeFrom tree t lowered}
    (alignment : CanonicalDictionaryReplay replay)
    (meaning : TreeMeaningOver P lowered) :
    ∃ events : LiteralEventTree (s := s),
      ExactReplayEvents replay events ∧
      ExactOrderedOccurrences (dictionaryTree d) events ∧
      orderedLiteralReceipts events = written ∧ LedgerMeaning P events
```

`TreeMeaningOver P` は具体的な lowered 木を添字に取る tree/forest の fold。 `LedgerMeaning P` は別の ledger 上で各 occurrence の `P` を問う。C386 の exact `LoweredEventLedger` に沿う相互帰納で、両方に現れる同じ event を使用する。空出力の節も消さない。[C388 の exact 定理](https://github.com/momota1029/yulang/blob/c9d7b2a82f6620b2fcb42878eb19b199c85cb88e/lean/Yulang/GeneralDeclarativeI65SameEventSemantics388.lean) と [独立 audit](https://github.com/momota1029/yulang/blob/c9d7b2a82f6620b2fcb42878eb19b199c85cb88e/lean/Audit/Cycle388SameEventSemantics.lean) で、上の文をすべての `P`・同じ lowered 木に対して検証済み。Lean 4.35.0 trust 0・警告をエラー扱い。Git exact bytes の再ビルドと独立 audit も PASS、公理は `[propext, Quot.sound]`。新たな等式・順序・モデル仮定は置かない。この文は局所意味を移すもので、一般の型付き意味を生成した扱いではない。

##### S13bb · 分割（親、件数外） — `exact_semantic_ledger_to_dictionary`

```lean
theorem exact_semantic_ledger_to_dictionary
    {replay : LiteralTreeFrom tree t lowered}
    {events : LiteralEventTree (s := s)}
    (eventMatch : ExactReplayEvents replay events)
    (canonical : ExactOrderedOccurrences (dictionaryTree d) events)
    (outputs : orderedLiteralReceipts events = written)
    (semantic : LedgerMeaning (GeneralLocalMeaning s m) events) :
    DictionaryEvidence s m q d
```

`GeneralLocalMeaning s m` は **具体的** な局所の head/capture および literal body の意味。普通の等式は `Holds m.assignment`。型付き出力は exact source/capture から導いた同じ ordinal/target で、任意長の元の value/row ベクタ、入れ子、非点区間の評価が同じモデルの固定先に成立することを示す。 `GeneralTreeMeaning s m q d written` は S12 が **その lowered** に対して作るこの意味の fold（lowered は既存の実引数で、bare の metavariable にはしない。元の表示なら、その引数を束縛した local notation で展開できることを Lean で確認）。新しい明示前提、 `Fits` の選び直し、または canonical ledger を最初から意味の仮定に置く方法は不可。 `DictionaryEvidence` は canonical tree の全出現と順、exact receipt 列と固定先の実モデル意味を保持する出力 interface。単なる存在／有限 membership や `GeneralTreeMeaning` の別名にはしない。

[C365 の `Model / Fits`](https://github.com/momota1029/yulang/blob/1b5b4c3d1a1c3809e49eaa266dd5d4b18b4eff71/lean/Yulang/GeneralDeclarativeI65State365.lean#L47) と [C357 の `Seen / ModelsCurrent`](https://github.com/momota1029/yulang/blob/1b5b4c3d1a1c3809e49eaa266dd5d4b18b4eff71/lean/Yulang/GeneralDeclarativeWitnessDeclaredState357.lean#L39) は別の観測を解釈する。C386 の `.declared` は `target/Pattern/List (Argument Nat)` を落とさないが、そこから当該 target の retained `AuthoredNominal` 又は exact native origin は作らない。[C368 の `typed_written_all_models`](https://github.com/momota1029/yulang/blob/1b5b4c3d1a1c3809e49eaa266dd5d4b18b4eff71/lean/Yulang/GeneralDeclarativeI65LiteralTypedBody368.lean#L114) は明示された `fixedTyped` を用いる一個の value 点。文脈内の端点比較は既に与えた端点どうしの意味で、元の出力の評価・固定先への保持は与えない。どの観測を使うかや新しい受理条件をここで決めない。


**分割理由（C389 / I-68）:** replay と canonical shape から実要求・実辞書・子の対応を作ることと、同じ出現の具体的な型付き固定先を辞書意味として読むことは独立。まず、モデルを使わずに実辞書へ住所を付ける。型付き出力は `receiptAt` の source/ordinal/target が合っても、その引数が実 capture の RHS だとは限らない。親の文は変更しない。

###### S13bba · 証明済み（C390 検証済み、integration 未取込） — `exact_replay_ledger_addresses`

```lean
theorem exact_replay_ledger_addresses
    {replay : LiteralTreeFrom tree t lowered}
    {events : LiteralEventTree (s := s)}
    (eventMatch : ExactReplayEvents replay events) :
    AddressedDictionaryEvents s q d events
```

`AddressedDictionaryEvents` は `GeneralTree` の actual `Request` と `Dictionary.node` を ledger の同じイベントに対応させる。子辞書の各位置を、その同じ event の `kids` と guard から保つ。 `addressed_replay_has_canonical_order` で canonical 順を戻せるため、key-only の診断木も失わない。[C389 strict 検証と exact proof](https://github.com/momota1029/yulang/blob/2edef5d492f40cced77cdddd80d6ec0e224d8459/notes/design/dots-cycle-389-s13bb-addresses.md)。 [C390 の exact 定理](https://github.com/momota1029/yulang/blob/698dce6805076109f40f9d60e08cec4c7989a88b/lean/Yulang/GeneralDeclarativeI65AddressedReplay390.lean) と [独立 audit](https://github.com/momota1029/yulang/blob/698dce6805076109f40f9d60e08cec4c7989a88b/lean/Audit/Cycle390AddressedReplay.lean)。Lean 4.35.0 trust 0、警告をエラー扱い。定理の型と canonical 順の補助定理を別ファイルから import して検証した。Git exact bytes 再ビルドと別 audit も PASS。main 補題の公理は `[propext]`、canonical 順は `[propext, Quot.sound]`。別の same-event/同一モデル仮定は追加しない。

###### S13bbb · 未証明 — `addressed_semantic_ledger_to_dictionary`

```lean
theorem addressed_semantic_ledger_to_dictionary
    {events : LiteralEventTree (s := s)}
    (addressed : AddressedDictionaryEvents s q d events)
    (outputs : orderedLiteralReceipts events = written)
    (semantic : LedgerMeaning (GeneralLocalMeaning s m) events) :
    DictionaryEvidence s m q d
```

住所証明を model 仮定とせず、意味のある同じ event の本来の ordinal と固定先を使う。普通の行は原 source/capture と `Holds`。型付き行は source/capture から exact declared RHS の arbitrary value/row・点/非点・入れ子の関係を先に示し、同じ状態の元 retained row/origin から同一 model 内の固定先を示す。他の event の projection を足さず、`Fits` だけ、既に結果を仮定した interface、旧 solver/release、または受理連動の選択ルールでは埋めない。局所意味は S12、結果の `DictionaryEvidence` は独立の木の意味を持つ。

元の S13bb の証明本体（その元の四前提と結論はそのまま）:

```lean
  exact addressed_semantic_ledger_to_dictionary
    (exact_replay_ledger_addresses eventMatch) outputs semantic
```

元の `canonical` は住所の強い形からも得られる（`addressed_replay_has_canonical_order`）。仮定から削除はしない。

元の S13b は、元の二前提から次の組み立てで得る。

```lean
  obtain ⟨events, matchEvent, order, rows, sem⟩ :=
    aligned_same_event_semantics
      (P := GeneralLocalMeaning s m) alignment meaning
  exact exact_semantic_ledger_to_dictionary matchEvent order rows sem
```

両行が閉じれば、元の S13 は固定の前提のまま次の形になる（文も最上段も変更なし）。

```lean
  exact aligned_general_meaning_to_dictionary
    (general_literal_replay_alignment literal replay) meaning
```

## 4. 証明済みの部品と固定アンカー

下記 P 行は証明済み **として使う命題の全範囲**。狭い定理を広い S 行の証明済みへ数え替えない。パスはすべて `lean/Yulang/`、参照は冒頭の immutable integration commit。表の prefix `GeneralDeclarativeI65` はファイル名のみ省略。特記のない定理の namespace は `Yulang.GeneralDeclarativeI65` 又は同ファイル内の子 namespace。

### P01 · 証明済み — `visible_exact`

```lean
theorem visible_exact (s : State) (q : Request) (d : Declaration) :
  d ∈ visible s q ↔ d ∈ (authoredRegistry s.current).declarations ∧ d.role = q.demand.role
```

[`GeneralDeclarativeI65State365.lean` · `visible_exact`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65State365.lean#L64)。S02 のフィルタ、S03 の実順の基礎（所属定理自体は順序定理ではない）。

### P02 · 証明済み — `source_receipt_in_one_model`

```lean
theorem source_receipt_in_one_model {s : State} {q : Request} {row : Declaration}
    {pick : AuthoredCandidate s q row} {kids : List Request}
    (receipt : SourceReceipt pick kids) (m : Model) (fit : Fits s m) :
    ReceiptMeaning receipt m
```

[`GeneralDeclarativeI65UnionReceipts368.lean` · `source_receipt_in_one_model`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65UnionReceipts368.lean#L57)。S08/09。receipt は独立選択から既に得た場合に限る。

### P03 · 証明済み — `emitted_receipt_tree_sound`

```lean
theorem emitted_receipt_tree_sound {s : State} {q : Request} {d : Dictionary}
    {written : List OrderedWriteReceipt} (tree : ReceiptTree s q d written)
    (m : Model) (fit : Fits s m) : ReceiptTreeMeaning s m q d written
```

[`GeneralDeclarativeI65MixedReceiptTree368.lean` · `emitted_receipt_tree_sound`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65MixedReceiptTree368.lean#L53)。S12 の相互帰納の骨格。ここでの型は S11/12 の一般型と同一とは主張しない。`ModeWindow` や型付きの完了した比較があるから native の早い訪問がある、という逆向きは使わない。

### P04 · 証明済み — `every_written_receipt_in_one_model`

```lean
theorem every_written_receipt_in_one_model {s : State} {m : Model} {q : Request}
    {d : Dictionary} {written : List OrderedWriteReceipt}
    (evidence : ReceiptTreeMeaning s m q d written) :
    ∀ w ∈ written, WrittenIn m w
```

[`GeneralDeclarativeI65MixedReceiptTree368.lean` · `every_written_receipt_in_one_model`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65MixedReceiptTree368.lean#L70)。S13 用の分配定理。ただしリストの順序そのものは membership からでなく構成子で保持する。

### 既存部品の割当（S 行の再確認先・追加の本数にはしない）

| 行 | integration の実ファイルと引用する定理 |
|---|---|
| S01/S11 | `GeneralDeclarativeI65Lowering365.lean`: [`lower_tree`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65Lowering365.lean#L20), [`lower_forest`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65Lowering365.lean#L38), [`classified_source_assembly`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65Lowering365.lean#L60); ordinary scoped conditional のみ |
| S02 | `GeneralDeclarativeI65Tape367.lean`: [`live_readback`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65Tape367.lean#L80), [`tape_waiting_origin`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65Tape367.lean#L100), [`every_nonlive_unblocked_row_is_a_real_miss`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65Tape367.lean#L119); `GeneralDeclarativeI65Selection367.lean`: [`actual_matched_row`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65Selection367.lean#L27) |
| S03 | `GeneralDeclarativeI65NormalSupport368.lean`: [`supported_entry_origin`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65NormalSupport368.lean#L35); `GeneralDeclarativeI65NormalizedPrefix368.lean`: [`normalized_actual_prefix_k2`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65NormalizedPrefix368.lean#L40), [`normalized_pending_row_changes_k2_without_support`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65NormalizedPrefix368.lean#L46); `GeneralDeclarativeI65ReturnRankCore370.lean`: [`local_return_rank_iff_no_cycle`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65ReturnRankCore370.lean#L54); `GeneralDeclarativeI65EarlyPorts369.lean`: [`endpoint_port_from_one_original`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65EarlyPorts369.lean#L84), [`endpoint_port_agrees_with_job`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65EarlyPorts369.lean#L70); `GeneralDeclarativeI65NativePrefixCore377.lean`: [`native_value_port_at_literal_job`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65NativePrefixCore377.lean#L93); `GeneralDeclarativeI65OrdinaryCrossingRoot378.lean`: [`some_ordinary_visit_iff_inspects`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65OrdinaryCrossingRoot378.lean#L17); `GeneralDeclarativeI65EnteredOrdinaryRoot379.lean`: [`entered_ordinary_root_keeps_pending_equations_for_k2`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65EnteredOrdinaryRoot379.lean#L57); `GeneralDeclarativeI65ScopedNativeCalls379.lean`: [`second_position_requires_positive_first`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65ScopedNativeCalls379.lean#L53) |
| S04 | `GeneralDeclarativeI65State365.lean`: [`mode_window_sound`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65State365.lean#L98); `GeneralDeclarativeI65Comparison365.lean`: [`in_same_model`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65Comparison365.lean#L90); `GeneralDeclarativeI65Heads367.lean`: [`source_head_sound`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65Heads367.lean#L76); `GeneralDeclarativeI65RouteTag368.lean`: [`distinct_route_excludes_match`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65RouteTag368.lean#L58); `GeneralDeclarativeI65AuthoredDispatchMode379.lean`: [`actual_dispatch_uses_same_authored_value_variance`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65AuthoredDispatchMode379.lean#L31) |
| S05 | `GeneralDeclarativeI65Capture366.lean`: [`value_binding_sound`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65Capture366.lean#L31), [`row_binding_sound`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65Capture366.lean#L38), [`selected_centers_sound`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65Capture366.lean#L53); `GeneralDeclarativeI65Deep366.lean`: [`deep_reads_retain_all_sources`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65Deep366.lean#L94); `GeneralDeclarativeI65Compiler367.lean`: [`actual_port_center`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65Compiler367.lean#L52); `GeneralDeclarativeI65PostselectionTies368.lean`: [`receipt_repeated_centers`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65PostselectionTies368.lean#L59) |
| S06 | `GeneralDeclarativeI65SourceBodyProduction371.lean`: [`ordinary_fixed_inputs_produce_body`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65SourceBodyProduction371.lean#L24), [`fixed_root_targets_do_not_erase_literal_child_allocation`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65SourceBodyProduction371.lean#L113); `GeneralDeclarativeI65DirectDeclaredTarget371.lean`: [`direct_output_target_uses_declaring_equation`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65DirectDeclaredTarget371.lean#L28); `GeneralDeclarativeI65RetainedEvent372.lean`: [`retained_body_facts_at_same_current`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65RetainedEvent372.lean#L48); `GeneralDeclarativeI65IndependentlySelectedWhere379.lean`: [`selected_native_root_keeps_literal_child_occurrence`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65IndependentlySelectedWhere379.lean#L33)（独立に選択済み、親の固定出力は空） |
| S07 | `GeneralDeclarativeI65NativePrefix369.lean`: [`current_release_actual_at_origin`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65NativePrefix369.lean#L44), [`original_from_installed_and_retained_author`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65NativePrefix369.lean#L99); `GeneralDeclarativeI65CurrentRelease376.lean`: [`checked_install_opens_iff_granted`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65CurrentRelease376.lean#L60), [`same_target_different_source_address_not_open`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65CurrentRelease376.lean#L68); `GeneralDeclarativeI65PreparedOwnBody376.lean`: [`one_authored_preparation_keeps_ordered_and_typed_meaning`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65PreparedOwnBody376.lean#L47); `GeneralDeclarativeI65JoinBody368.lean`: [`current_typed_write_exact`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65JoinBody368.lean#L41) |
| S08/S09 | `GeneralDeclarativeI65Body367.lean`: [`authored_node`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65Body367.lean#L67), [`attached_source_sound`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65Body367.lean#L77); `GeneralDeclarativeI65UnionReceipts368.lean`: [`source_receipt_in_one_model`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65UnionReceipts368.lean#L57); `GeneralDeclarativeI65JoinBody368.lean`: [`chosen_typed_literal_body_sound`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65JoinBody368.lean#L99) |
| S12/S13 | `GeneralDeclarativeI65MixedReceiptTree368.lean`: P03/P04; `GeneralDeclarativeI65SourceTree365.lean`: [`source_tree_sound`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65SourceTree365.lean#L48), [`every_fixed_row_comes_from_the_same_model`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65SourceTree365.lean#L61) |

| S02/S03 | `GeneralDeclarativeI65Origins367.lean`: [`actual_route_iff`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65Origins367.lean#L21), [`physical_origin_is_not_logical_equality`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65Origins367.lean#L54); `GeneralDeclarativeI65Rivals367.lean`: [`rigid_candidate_excludes_a_source_head`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65Rivals367.lean#L60); `GeneralDeclarativeI65AuthoredPrefix368.lean`: [`ordinary_prefix_veto_independent_of_choice`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65AuthoredPrefix368.lean#L99); `GeneralDeclarativeI65ActualUnaryDispatch379.lean`: [`authored_prefix_and_unary_dispatch_agree`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65ActualUnaryDispatch379.lean#L90); `GeneralDeclarativeI65ActualCandidateOrder379.lean`: [`first_authored_unary_entry_before_second_candidate`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65ActualCandidateOrder379.lean#L84)（実 unary の継続であり全候補の優先順位ではない） |
| S04/S05 | `GeneralDeclarativeI65WrittenHead365.lean`: [`actual_written_application_use`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65WrittenHead365.lean#L26); `GeneralDeclarativeI65OriginArity365.lean`: [`same_mode_vector_at_both_origins`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65OriginArity365.lean#L37); `GeneralDeclarativeI65Obligations365.lean`: [`context_arguments_of_needs`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65Obligations365.lean#L42); `GeneralDeclarativeI65Reflection365.lean`: [`reflects_existing_compiler`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65Reflection365.lean#L89); `GeneralDeclarativeCompoundHeads338.lean`: [`record_seen`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeCompoundHeads338.lean#L95)（既存の独立 source に結ばれた普通側） |
| S08/S09 | `GeneralDeclarativeI65ExistingCases365.lean`: [`ordinary_and_joined_share_model`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65ExistingCases365.lean#L48); `GeneralDeclarativeI65SourceNode365.lean`: [`source_node_sound`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65SourceNode365.lean#L90); `GeneralDeclarativeI65LiteralTypedBody368.lean`: [`typed_written_all_models`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65LiteralTypedBody368.lean#L114); `GeneralDeclarativeI65TypedOutputs365.lean`: [`typed_fixed_route_sound`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeI65TypedOutputs365.lean#L20); `GeneralDeclarativeWitnessFullIntervals357.lean`: [`in_current_full_model`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/GeneralDeclarativeWitnessFullIntervals357.lean#L271); `CommonRecursiveNominalIntervalContextAdmission.lean`: [`compile_in_context_exact`](https://github.com/momota1029/yulang/blob/a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6/lean/Yulang/CommonRecursiveNominalIntervalContextAdmission.lean#L214) |

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

矢印は証明の依存（S10 が S02〜S08 全部を、S11 が S01/S10 を、S12 が S09/S11 を使用）。P01–P04 の見出しは狭い再利用定理。S 行は一回ずつ数え、forest は S11 と同一の相互帰納単位。S01 の `Resolves` は同じ `s` を参照する。途中で子が付け足した等式や native write は、実導出が現在の `s` に保持したという S06/S07 の対応を通す。証拠のないスナップショットの固定化、兄弟の交換、可換な意味を利用した順序消去では補わない。I-60 どおり、その位置を判断するための支持付き読みや宣言的な source/等式生成規則を宣言的導出の材料にできる。S01 の本物の規則を実装する際、S02–S07 の**複合結論**を証明済みフィールドとして詰めない。特に S03 の実検査位置・優先順位は proof of acceptance でなく、その独立導出からの保存/反転の目標。S01/S02 の source event は原始規則で成立したものを指し、成功チェッカや派生 `ReceiptTreeMeaning`を backwards に使わない。S09 以外の source → receipt 側では `Fits`、モデル選定、checker を使わない。新しい行を足す場合はその理由と依存の入れ替えをこの節へ 1 行で記録する。


- C380 初版→監査版: S01/S02/S10/S11/S13 に源イベントの明示添字を通した。同じ key 列・同値・`Prop` の証明同一性で別出現を同一視しないため。行数・状態・固定文は変更なし。
- C380 初版→監査版: S11 は `LoweringPair` を返す一補題に明記した。相互帰納を 2 件と誤読しないため。

- C383/I-67: S01–S03 を同じ状態の有限完了・独立論理出力・無フィルタ K2 に改めた。solver の権限表を宣言側へ逆輸入しないため。状態ラベル・本数・固定文は変更なし。

### I-68: 一周一補題の作業順

現在の分解が明示的に呼ぶ未解決補題を記録し、順位は証明本体で使う補題を先に置く。独立な入口が複数あれば、構造と証拠の受け口を先に扱う。右端は最上段に組み込むときの前提の供給元であり、その前提を既に引数で受ける証明の呼出し依存とは区別する。共有 carrier の実定義は「補題を呼ばない」としても必要。

| 順 | 行 | 証明で呼ぶ未解決 S 行 | 前提を組立で供給する行 |
|---:|---|---|---|
| 1 | S13a（済） | なし。与えられた replay 自体の構造。 | S11 の literal と replay。S11 の再証明は不要。 |
| 2a | S13ba（済） | なし。渡された alignment に沿う相互帰納。 | S13a の alignment、S12 の意味。 |
| 2b-a | S13bba（済） | なし。引数の replay の相互帰納。 | S13ba の exact ledger。親 S13bb は S13bba と S13bbb を呼ぶ。 |
| 2b-b | S13bbb | なし。実住所と同じ ledger の concrete 局所意味を引数にする。 | S13bba の住所、S12 の局所意味。 |
| 3 | S01 | なし。独立の source と診断 API 自体を作る。 | なし。 |
| 4 | S02 | なし。独立導出を反転。 | S01 が供給する event。 |
| 5 | S03 | なし。同じ選択導出の priority を反転。 | S02 の `SelectedSource`。 |
| 6 | S04 | なし。引数の出現と guard を使う。 | S02 の選択出現、S03 の優先 guard。 |
| 7 | S05 | なし。受け取った head と source 記録を結ぶ。 | S02 の source 記録、S04 の一般 head。 |
| 8 | S06 | なし。ordinary の実分岐と捕捉を反転。 | S02 の実 ordinary body 分岐、S04 の head、S05 の捕捉。 |
| 9 | S07 | なし。typed/mixed の実分岐と捕捉を反転。 | S02 の実 typed/mixed body 分岐、S04 の head、S05 の捕捉。 |
| 10 | S08 | なし。受け取った exact receipt から node。 | S04/S05 と、実分岐に応じて S06 または S07。 |
| 11 | S09 | なし。渡された一般 node の意味を与える。 | S08 の一般 node。 |
| 12 | S10 | S02–S08。S09 は使わない。 | S01 の独立導出・event。 |
| 13 | S11 | なし。自分の tree/forest 相互帰納のみ。 | S01 の source trace、S10 の `ProvidesGeneralNode`。 |
| 14 | S12 | S09 を各 node に使う。 | S11 が tree を供給。S12 本体では tree は引数。 |

- C385 / I-68: S13 → S13a・S13b。canonical replay の構造と辞書証拠で保持する同一モデル意味は別の未解決義務だから分けた。親 S13 は件数外で、定理文・最上段はそのまま。S12 は S09 を実際に使うため先頭にしない。この周に他の行の文・状態は変えない。

### 将来の S01 の確認点

1. 正本で監査するのは `Classifies` の限定実装を呼ぶかどうかでなく、`State` と実原始導出から `LocalSource` の入力が揃うか。宣言の順番・実出現・kind/mode の出どころを現台帳から読む。 `Fits` の同じ syntax/値だけでは異なる source route の区別を証明できない（S02/S04）。
2. 診断木は root/候補検査規則と where 子の要約を別の段に置く。K2 は S03 の root/候補検査であり、子リストやモデルの fold から逆算しない。辞書全体を再帰して既に選択したかを判定する循環を作らない（S01 と S11 の分離）。
3. I-67: 実 carrier は宣言的な完了を保持する。C381/C382 の release 非消去は検査器の責務で、S01 で求めない。正の完了根拠の有限性と、同じ安定状態での保留・全可視候補の実判断を分けて検査する。途中の一意性や一時的な保留を最終判定に読み替えない。順序によって受理が変わる **仕様上の** 場合が見つかったときは、遅延案を先にして質問ノートに記録する。今回は該当する承認済み source 例は確認していない。
4. `ReceiptMeaning` が exact local order と typed write を型に持っていても、その後の `WrittenIn` は各要素の意味の投影でしかない。S13 を P04 の集合化だけで閉じず、辞書の木構造に固定した全列を保持する。

次の周は S13bbb（実住所と具体的な同一モデル意味から固定先をもつ辞書証拠を作る）。S13bba の完了を元の S13bb の完了とは数えない。I-65 step 2/3 は未着手。C は後回し。S1/S2 の全体は閉じない。停止性・旧 `Local`・旧 C334 への橋・追加 fixture はこの一覧に含めない。

**未解決 13 件 = 未証明 3 件（S01・S10・S13bbb） + 一部 10 件（S02–S09・S11–S12）。親 S13・S13b・S13bb、証明済み S13a・S13ba・S13bba、再利用 P01–P04 は除外。**
