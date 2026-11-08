# Cycle 2 — 適合例の追加候補（未登録・未証明を区別）

2026-11-08。比較対象は `notes/handoff/2026-11-08-m1-spec-examples-conformance.md`
の X1〜X24。以下はそこに独立した行のない確定事項から取った**候補**であり、
X25 以降を正式採番したものではない。spec、既存表、既存定理は変更していない。
新しい Lean 証明や全 source 入口での実行を今回行ったとは主張しない。

仕様の参照行は cycle 2 の取得版 `5fd6ffa2c` の
`spec/06-roles.md`。行番号より引用した見出しと規則を優先する。

## A. impl が唯一でも、未知の弱い型を決めない

- 根拠：6.3、行96付近「ファイルの終わりまで型変数が決まらなかった場合は、
  見える impl が一つしかなくてもその型に決めない」（確定、2026-11-05）。
- source 例（仕様の例）：`my z = default ()` の弱い `'a: Default` が、同じファイルの
  利用箇所でも未確定。可視 impl が1件でも、最終化は型未確定のエラー。
  明示注釈で型が決まる場合とは分ける。
- 既存の証拠：`EOFNoDefaulting.Examples.unique_visible_impl_does_not_complete`、
  `annotation_determined_slot_is_accepted`、`import_cannot_complete_slot`。
- gap：これらは `finishFile` と用意した interface/assignment を通る実例。
  元の `default ()` から弱い変数・qualified interface を生成し、宣言と利用箇所を
  含む一つの source ファイルの公開入口で同じ結果へ到達する橋は、この調査では確認していない。
- 注意：`EOFRoleInference` は過去の defaulting 実験として明示されており、
  その成功を現在の言語の受理として使わない。

## B. 関連型の等式は、先に積まれた通常制約と衝突すれば拒否

- 根拠：6.3、行88〜95「関連型は、新しい型変数と等式で表す」および
  「等式は先に束縛しない」（確定、2026-11-05）。
- source 例：仕様の `first : 'c -> 'v where 'c: Index(int, value = 'v)`。
  `first xs` の利用で先に `'v` の期待型制約を積み、その後 receiver が決まって
  `type value = ...` の等式が入り、両者が両立しなければ型エラー。
- 期待は「後から得た associated RHS を勝手に優先して前の制約を捨てない」。
  具体的な非互換型対は既存 Common の disjointness 証明を使って選ぶ。
- 既存の証拠：`Roles.assoc_explicit_eq` は宣言の RHS を実 `assocOf` から回収する。
  cycle 2 の `CommonRoleAssociatedStateFlow` / Parent 系はこの接続を作業中。
- gap：この調査はその最終 source 適合例を証明していない。任意の ordinary atoms を
  手入力した反例だけで、この候補が外側 source 入口を通ったとはしない。
- X7 は「宣言時に RHS が head から決まらない」という別問題。この利用時衝突は重複しない。

## C. SCC で固定した role 選択を、呼出し時に field へ切り替えない

- 根拠：6.4、行174〜175（確定、2026-11-05）。未知 receiver なら role を先にし、
  同じ SCC 内で型が判明すれば field 優先。SCC 完了後の解釈は呼出側で変更しない。
- source 例（仕様の例）：`f(x) = x.size` が `where 'a: Size` になった後、
  `box` の field `size` だけを持つ値へ適用しても、`Size box` の impl がなければ拒否。
  同じ SCC 内で receiver が box と判明してから field 選択する場合と対にする。
- 既存の証拠：`FrozenMethodExamples.generated_frozen_principal_rejects_box`、
  `generated_same_scc_known_principal_accepts_box`、`fixed_selection_changes_acceptance`。
- gap：`FrozenMethods` は最終 SCC knowledge snapshot と method table の対応を外部境界とする。
  snapshot を完全な source SCC から作る橋、および全 source 宣言から role/method table を
  作る橋を、この例が不要にしたとはいえない。局所入口の証明は再利用できる。

## D. ref の method lookup は、中身へ暗黙委譲しない

- 根拠：6.4、行153〜160（確定、2026-11-05）。`ref 'e 'a` で調べるのは ref だけ。
- source 例（仕様そのまま）：

  ```yulang
  my $n = 0
  &n.get
  $n.add 1
  &n.add 1
  ```

  ref 専用 add がない前提で、最後だけ「ref に add は無い」。
  `ref _ int` に特化した add を明示定義した場合は別ケース。
- 既存の証拠と gap：`MethodResolution` の先頭 doc は nominal/inherent/effect lookup を
  未実装と明記している。`CommonBoundRef*` は名前だけでこの lookup 規則の証拠にしない。
  この調査範囲で、この source 例を外側入口から通す定理は確認できなかった。

## E. union の method owner が一つなら全 union を cast、複数なら曖昧

- 根拠：6.4、行163〜169（確定、2026-11-05）。
- source 例（仕様の例）：`int | user_id` の `x.add 2` は Add を持つ int を選び、
  user_id 部分にも int への cast が必要。`x.show` が両方にあれば曖昧。
- 既存の証拠：`CastExamples.method_unique_member_casts_the_whole_union`、
  `method_missing_conversion_is_rejected`、`method_multiple_owners_are_ambiguous`。
- gap：そのファイルの実例は ordinary compatibility に equality を与える ground kernel。
  Common の構造的部分型判定・元 source の method 宣言 lookup・cast body の実行や効果まで
  同時に扱う公開 source 入口の適合を示したものではない。
- 追加時は3結果を別 theorem にし、宣言順で一方を選ぶ例にはしない。

## F. 分岐の合流では cast せず、後の期待型境界で全 member を検査

- 根拠：6.5、行199〜217。分岐は union（確定、2026-11-04）、一つでも cast が
  見つからなければ静的エラー（確定、2026-11-05）。期待型がなければ警告であって拒否ではない。
- source 例（仕様の例）：`my y = if c: 1 else: "text"; use_int y` は str→int の
  規則がない場合に境界で拒否。裸の union を作る段階で拒否する例にはしない。
- 既存の証拠：`CastExamples.source_union_all_members_convert`、
  `source_union_missing_member_is_rejected`、`whole_union_lookup_cannot_hide_missing_member`。
- gap：これらは ground cast routing の境界検査。source の分岐推論から union を保持し、
  後続期待型で cast 境界を作り、診断の warning/error を分ける外側入口の証明は別。

## 優先順位の提案

1. A と C：既存の最外側局所入口・具体定理があるため、まず状態表へその入口名と
   source 統合境界を正確に載せやすい。
2. B：現在の T1c の要求に直結する。declared RHS の生成から solver の衝突までを一体にする。
3. D/E/F：method/cast の source 接続が進んだ時に追加。部品の存在だけで PROVED に昇格しない。

これは読み取り調査の提案であり、意味論の選択、新しい全体 theorem の承認、
既存 X1〜X24 の完了判定変更はいずれも行っていない。

## 同サイクルの後続確認

Bに関連して、固定Right-strのParentPipelineについて、実宣言のvalue=intと
旧slot=strの衝突でrun=noneになるLean回帰を独立に検査し、exit0を確認した。
ParentSuccessは任意の開始状態のsome成功ならint＋実resolved可視辞書と証明する。
ただしfirstのsource構文から期待型制約を生成する橋ではなく、上のBの最終source
適合判定は未完のまま。noneをlanguage-visible rejectedと同一視しない。
