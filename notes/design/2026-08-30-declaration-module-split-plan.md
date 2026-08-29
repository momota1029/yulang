# `declaration.rs` production code のモジュール分割計画

Status: Authoritative（ユーザ承認済み、2026-08-30）。open question 1〜3・5はユーザ選択によりそれぞれ
「全family `_decl`統一」「impl_decl.rsへ同居」「variant_core.rs」「提案どおり17 commit粒度」で確定。
open question 4(follow-upの可否)は本計画のscope外のまま、着手可否は別途判断する。

著者: Claude (Fable 5)

## 0. この文書の位置づけ

この文書は **リファクタリング／モジュール構成の計画** であり、grammar design addendum ではない。
`notes/design/2026-08-20-yu-syntax-chasa-architecture.md` の `FOO-G/J/T/R` 構造（BNF・judge・
worked example・recovery matrix）は新しい文法構築物のためのものであり、この計画には適用しない。
この計画は **文法・CST・AST・recovery・diagnostics のいかなる挙動も変えない**。変えるのは
`crates/yu-syntax/src/grammar/declaration.rs` 内のコードの置き場所と、それに伴う可視性記述だけである。

したがって、この文書の authority scope は「どのコードをどのファイルへ、どの順で、どの可視性で
動かすか」に限られる。文法上の意味論の正本は引き続き architecture 文書とその addendum 群である。
両者が矛盾して見える場合（ありえないはずだが）、architecture 文書が勝つ。

先行 precedent:

- テスト分割（commit `dfc213f9`）: `declaration.rs` の inline `#[cfg(test)] mod tests`（33,686 行、
  当時のファイルの 59.6%）を `declaration/tests.rs` へ verbatim move した。rustfmt が 12.4GB
  allocation failure で再現的に crash する file-size limitation が直接の動機。
- モジュール構造 precedent: `type_expr.rs` + `type_expr/polymorphic_variant.rs`。private child
  module、子は `use super::*;`、親へ返す surface だけ `pub(super)`（3 item のみ）という narrow
  visibility discipline。

本計画はこの続きとして、テスト分割後も残る **production code 約 22,800 行** を分割する。

## 1. 動機とゴール

### 動機

- `declaration.rs` は 6 つの standalone declaration/statement family（role・act・enum・cast・error・
  for）と複数の addendum（Act-derives・Type-attached impl）を 1 ファイルに実装順で積んできた
  結果、22,812 行（2026-08-30、commit `dfc213f9` 時点）に達している。
- 各 family のコードが**時系列で interleave** している。たとえば Role の実装は
  intro recognizer（987 行付近）、episode spec（2479）、parse/commit（3629）、emit 群（15417）の
  4 領域に分散し、間に他 family のコードが挟まる。1 family を読むのにファイル全域のジャンプが要る。
- AGENTS.md の「ファイルは責務ごとに分ける」「1 ファイルが複数の責務（orchestration・構文別処理・
  …）を抱え始めたら module へ分ける」に既に大きく反している。
- テスト分割で rustfmt crash は解消したが、production 側も family 追加のたびに伸び続ける。
  `with:` companion・Type role-like body・where 節など deferred addendum が控えており、
  今分割しないと同じ限界に再接近する。

### ゴール

1. family ごと・共有 core ごとの child module へ分割し、`declaration.rs` を「中央 wiring +
   共有 vocabulary + 共有 plumbing」だけの hub（約 2,000 行前後）へ縮める。
2. **ゼロ挙動変更**。全 phase を通じて `cargo test -p yu-syntax` は 568 passed / 0 failed のまま。
   fixture・snapshot・diagnostics・byte range は 1 バイトも変わらない。
3. **`declaration/tests.rs` を 1 行も変更しない**（§3 の可視性設計により保証する）。
4. `expression.rs`・`header.rs`・`parse.rs`・`pattern.rs`・`type_expr.rs` の既存 import path
   （`crate::grammar::declaration::X`）を facade re-export で不変に保ち、declaration の外を
   一切触らない。
5. 各 phase は独立に commit 可能・独立に test 検証可能で、途中状態でも壊れない。

## 2. 現状分析（2026-08-30、commit `dfc213f9` 後の実測ライン。以後の phase で当然ずれる）

行番号はすべて現ファイルの grep 実測値。テスト分割前の調査（Codex Terra、pre-split）の行番号は
すべて失効しているため引用しない。

### 2.1 領域マップ

| 行範囲 | 内容 | 分類 |
|---|---|---|
| 1–68 | doc header・`use` 群 | hub |
| 69–290 | `Declaration`/`HeaderDeclaration`/`HeaderStatementIntro`/`StatementIntro` enum、per-family `*StatementIntro` struct 群 | hub vocabulary（intro struct は family へ） |
| 291–356 | `ParsedBindingDeclaration`/`ParsedBindingDefinition`/`ParsedBindingBody` | Binding family |
| 310–316 | `Recovered<T>` | hub（pattern.rs / type_expr.rs が import） |
| 357–532 | `DirectRootCandidateOutput`・`parse_direct_root_candidate(_with_local)` | hub（root direct dispatch） |
| 533–658 | `emit_root_error`・root expectation 群 | hub |
| 659–767 | `VisibilityPrefix`・`commit_header_statement`・`parse_direct_header_declaration` | hub |
| 768–890 | `recognize_statement_intro`（中央 dispatcher） | hub |
| 891–1283 | per-family intro recognizer（struct 891 / type 939 / role 987 / act 1036 / enum 1119 / error 1202） | 各 family へ |
| 1284–2173 | **For 文一式**（intro・label probe・pattern/in/iterable slot・body・recovery・emit）— 完全に連続 | For family |
| 2174–2264 | impl / cast intro recognizer | Impl / Cast family へ |
| 2265–2478 | **Impl tail 共有 core**（`ImplTailOwnerSpec`・episode spec・tail type-expression slot、`#[cfg(test)]` isolated adapter 2 件含む） | Impl family（§5.3） |
| 2479–2596 | Role head episode spec | Role family |
| 2597–3628 | Act episode・source clause・parse/commit・body 群 | Act family |
| 3629–4171 | Role parse/commit・body 群 | Role family |
| 4172–5724 | **Cast 一式**（episode・prefix/pattern/target phase・signature・form・body・retry）— ほぼ連続 | Cast family |
| 5725–6553 | Impl（`ParsedImplTail`・parse/commit・`parse_impl_tail_ast`/`commit_impl_tail`・type-attached adapter・body 群） | Impl family |
| 6554–6617 | `scan_declaration_type_parameter_list/parameter` | hub（enum/error/type の 3 owner 共有） |
| 6618–6933 | Enum header | Enum family |
| 6934–7241 | Error header | Error family |
| 7242–9641 | **variant sequence/payload 共有 core**（driver・separator・payload episode・field AST/commit・`VariantDeclarationOwnerSpec`・両 context 実装） | variant core（§5.2） |
| 9642–9708 / 9709–9772 | `parse_enum_declaration_isolated` / `parse_error_declaration_isolated` | Enum / Error family |
| 9773–9833 | `declaration_type_parameter_end`・`enum_body_range_end`・`variant_declaration_sequence_spec` | hub / variant core |
| 9834–10262 | Enum body 4 形態 AST・Error body 4 形態 AST・boundary | Enum / Error family |
| 10264–10622 / 10623–10931 | Enum commit 群 / Error commit 群 | Enum / Error family |
| 10932–12227 | Type declaration（header slot・rhs・derives 連携・recovery。12166–12189 の `declaration_exact_equals/impl_pending` は共有） | Type family（共有 2 件は hub） |
| 12228–13268 | **derives 共有 driver**（owner・classifier・`drive_derives_clauses`・isolated adapter・via） | derives core |
| 13269–13543 | Type post-header decision（TAI 分岐）・form 分類。13352–13491 の `DeclarationBracedNewlineOwner` 群は cast/derives/type 共有 | Type family（newline-owner 群は hub） |
| 13544–13650 | mod intro・`binding_statement_selected`・`visibility_prefix`・inline trivia scanner 群 | Mod family / hub |
| 13702–13718 | `emit_visibility` | hub（12 call site、ほぼ全 family） |
| 13719–14030 | Binding intro・`commit_binding_declaration`・`commit_mod_declaration` | Binding / Mod family |
| 14031–14790 | `commit_struct_declaration` + struct 直接 body 群・mod colon body 群 | Struct / Mod family |
| 14791–14933 | **binding-style body layout 共有 core**（`classify_binding_style_body_layout`/`parse_binding_style_body`/`commit_binding_style_body`） | binding-style core |
| 14934–15161 | `commit_binding_body`・`emit_layout_missing`・`commit_word_candidate`・`direct_expression_error_retry` 系 | Binding family / hub plumbing |
| 15162–16177 | emit/retry 群（binding/mod 15162・impl 15280・role 15417・act 15553・struct 15686・mod 15952） | 各 family へ |
| 16178–16324 | import（use）emit 群 | Use family |
| 16325–17093 | operator header commit 群（17039–17093 の `commit_optional_inline_trivia`/`commit_character` は共有） | Operator family / hub |
| 17094–18453 | Use 直接 commit 一式（18341–18432 の `commit_trivia`/`commit_word` 系は共有） | Use family / hub |
| 18455–19539 | **中央 AST vocabulary**（全 family の AST 型 + use projection 関数） | 各 family へ（§4） |
| 19540–19575 | `parse_declaration`（root AST dispatch） | hub |
| 19576–21527 | Struct AST parse 一式（20404–21324 に variant 共有 field/scan 機構が interleave） | Struct family / variant core |
| 21528–21695 | `parse_header_declaration`・operator header AST parse | hub / Operator family |
| 21696–22108 | Binding / Mod AST parse | Binding / Mod family |
| 22109–22149 | `scan_declaration_exact_equals`・`declaration_operator_character` | hub（act/cast/enum/error/type/derives/binding の 21 call site） |
| 22150–22810 | Use AST parse 一式（micro helper `parse_open_brace` 等は Use 専用と call-site 実測で確認済み） | Use family |
| 22811–22812 | `#[cfg(test)] mod tests;` | hub 末尾に維持 |

### 2.2 共有 core の実測依存グラフ

計画の前提とした「shared core first」の instinct を call site の grep で検証した。結論は
**確認**（訂正なし）で、さらに 1 件の追加発見がある。

- **derives driver**（`recognize_derives_attachment_start` 等）: Act(2954–3340)・Enum(9657–10310)・
  Error(9724–10667)・Type(11552–11760)・Struct(14099–19643) の 5 owner から呼ばれる。正真の共有 core。
- **impl tail core**（`parse_impl_tail_ast`/`commit_impl_tail`）: standalone Impl(5749, 6011) と
  Type-attached adapter(5820, 6095) の 2 owner。TAI adapter（`parse/commit_type_attached_impl_isolated`）
  自体は Type 領域(11568, 11702)から呼ばれる。
- **binding-style body layout**: 消費者は Cast(5251, 5427) と Binding(14946, 22077) のちょうど 2 つ。
  core 自体（14791–14933）は自己完結。
- **variant sequence/payload core**: driver 系は Enum/Error の body 関数群（9834–10931 の 16+ call
  site）から owner spec 越しに呼ばれる。
- **追加発見 — struct field/scan 機構は第 3 の共有層**: `scan_struct_field_invalid_run`(8370, 9258)、
  `scan_struct_comma`(8594–9391 の 8 箇所)、`push/pop_struct_layout`(8584, 9223, 9318)、
  `consume_struct_field_name/type_trivia`(8366, 8387)、`struct_outer_owned_mismatched_close_pending`
  (8591, 9231)、`parse_variant_named_field_ast`(8599 と Struct 20149)、`commit_variant_named_field`
  (9256 と Struct 20724) など、Struct 領域生まれの field/list 走査層が variant core から大量に
  呼ばれている（Enum Gate 6 の「Struct field-loop 抽出込み」の帰結）。Enum/Error を Struct と独立に
  切り出すには、この層の置き場所を明示的に決める必要がある（§5.2）。
- **hub 級の細粒度共有 plumbing**: `scan_declaration_exact_equals`（act/cast/enum/error/type/derives/
  binding の 21 call site）、`declaration_exact_equals_pending`（enum/error/type/derives の 9 箇所）、
  `struct_trivia_has_newline`（derives 12377–13056・type 13299・struct・variant の 15 箇所 — 名前に
  反して汎用）、`DeclarationBracedNewlineOwner` 群（cast 4217/4258・derives 12540/12814・type
  13303–13463）、`emit_visibility`（12 call site）、`commit_word`/`commit_character`/
  `committed_position`/trivia scanner 群（全域）。これらは family へ動かせない。hub 残留が正しい。

### 2.3 外部依存面（分割で守るべき import surface）

`grammar/declaration` の外から `declaration::` を参照するのは以下で**全部**（crate 全域 grep 済み。
yu-syntax の外に declaration internals への参照は無い）:

- `expression.rs`（13–28 行の use block）: family AST 型 14 種（`ActDeclaration`〜`UseDeclaration`）、
  `Recovered`・`StatementIntro`、per-family の `parse_*`/`commit_*` 24 関数、
  `recognize_statement_intro`。ほかに test 内 5 箇所から `parse_direct_root_candidate`。
- `header.rs`: `HeaderDeclaration`・`parse_header_declaration`。
- `parse.rs`: `parse_direct_root_candidate`。
- `pattern.rs` / `type_expr.rs`: `Recovered`（+ pattern.rs の test 1 箇所から
  `parse_direct_root_candidate`）。

hub 残留分（`Recovered`・`StatementIntro`・`recognize_statement_intro`・`parse_direct_root_candidate`・
`HeaderDeclaration`・`parse_header_declaration`）は path 不変。family へ移る名前だけ facade
re-export（§3.3）が要る。この enumerable な小ささが、今回の分割の安全性の根拠のひとつ。

## 3. 分割の基本方式

### 3.1 hub-and-spoke + 双方向 glob mesh

polymorphic_variant precedent（private child、子は `use super::*;`）を土台に、子が多数・相互参照が
密という declaration 特有の条件に合わせて次の形にする。

- `declaration.rs` は module root のまま（`declaration/mod.rs` へは変換しない。`declaration/`
  directory は tests.rs で既存）。各子 module を private で宣言する:

  ```rust
  mod act_decl;
  mod binding_decl;
  // ...
  ```

- 各子 module の冒頭は `use super::*;` の 1 行だけ。親の private `use` 束縛（chasa・session・
  scan 系）と hub 残留 item がすべて見える。子 module 側に独自の import block は書かない
  （polymorphic_variant と同一方式）。
- hub 側に各子の private glob re-import を置く:

  ```rust
  use act_decl::*;
  use binding_decl::*;
  // ...
  ```

  これで (a) hub に残る dispatch code が子の item を無修飾で参照でき、(b) 兄弟 module 同士も
  `use super::*;` 経由で互いの `pub(super)` item を解決でき、(c) `tests.rs` の `use super::*;` が
  今までどおり全 item を解決する。**tests.rs 無変更はこの機構の帰結**であり、各 phase の検証項目
  でもある（tests.rs に手を入れたくなったらどこかが間違っている）。

### 3.2 可視性は一律・機械的に

- 移動する item のうち、現在 private のものは **一律 `pub(super)`** にする。item ごとの選別は
  しない。これは意味的に分割前と同値（分割前の「declaration module 内 private」= 可視範囲は
  declaration とその子孫。分割後の「子 module 内 `pub(super)` + hub glob」も同じ範囲）で、
  可視性の leak を一切増やさない。選別を後回しにできるのが phased 実行での最大の安全材料。
- 現在 `pub(crate)` のものは `pub(crate)` のまま動かす。
- polymorphic_variant の「narrow surface（3 item だけ pub(super)）」との relation: あちらは
  1 子・1 親・相互参照なしだから narrow にできた。declaration は 15 子・相互参照密で、初手から
  narrow にすると phase ごとに可視性エラーの手当てが発生し、リスクとレビュー負荷が増える。
  **narrow 化は全 phase 完了後の任意 follow-up**（§8 open question 4）とし、本計画では deviate を
  明示的に選ぶ。理由: この refactor の唯一の必達目標は「挙動不変のまま置き場所を直す」ことで、
  可視性の最小化はそれと直交する別作業だから。

### 3.3 外部 facade

家 family へ移る externally-referenced 名（§2.3 の enumerable list）は、子 module 側で
`pub(crate)` のまま宣言し、hub に **明示的な named re-export block** を置く:

```rust
pub(crate) use act_decl::{
    ActDeclaration, commit_act_declaration_isolated, parse_act_declaration_isolated,
};
pub(crate) use use_decl::{UseDeclaration, commit_use_declaration, parse_use_declaration};
// ... family ごとに 1 エントリ
```

- glob の `pub(crate) use x::*;` は使わない。何が外へ出ているかをこの block が一覧として
  文書化する（AGENTS.md の「子 module の役割が分かる最小限の re-export」に一致）。
- `pub(crate) use` の対象は子側で `pub(crate)` 宣言されている item に限る（`pub(super)` item の
  re-export による E0365 系エラーを構造的に回避）。
- private glob（§3.1）と named re-export が同名を二重 import する形になるが、explicit が glob に
  優先する Rust の規則どおりで問題ない。

### 3.4 この方式の重要な帰結: 「置き場所」に compile リスクがない

hub glob mesh の下では、**どの item をどの子に置いても名前解決は成立する**。つまり分割境界の
判断ミスは compile エラーにならず、可読性の問題にしかならない。逆に言うと、compile が守って
くれるのは可視性記述と facade の完全性だけなので、境界の質は本計画（§4–5）とレビューで担保する。

### 3.5 機械的移動の規律

- **rename は一切しない**。`scan_struct_comma` が variant core に住む、といった名前と置き場所の
  ずれは承知の上で持ち越し、任意の follow-up（§8）とする。move + rename を混ぜると diff が
  検証不能になる。
- item は doc comment・`#[cfg(test)]`・`#[allow(...)]` ごと verbatim move。順序は移動先で
  AGENTS.md の「主役を先頭に」（family module は AST 型 → entrypoint → 補助）へ並べ替えてよいが、
  中身は触らない。
- 各 phase の commit は `refactor(yu-syntax): ...` 系で、テスト分割 commit `dfc213f9` の message
  流儀（pure mechanical move / zero behavior change の明記）を踏襲する。
- rustfmt は host toolchain で phase ごとに通す。Codex sandbox と host の rustfmt version drift が
  既知（tasks/current.md 記載）なので、format-only 差分が出る場合は従来どおり behavioral commit と
  分離する。

## 4. 中央 AST vocabulary の裁定: family-colocated を採る

18455–19539 の中央 AST block（全 family の AST 型が一括で並ぶ領域）について、**family-colocated
（各 family の AST 型はその family module の先頭へ移す）を推奨する**。shared facade
（`declaration/ast.rs` に全型を残す）は採らない。

理由:

1. **中央 block は設計ではなく時系列の産物**。各 family の AST は当該 family の parse/commit しか
   構築せず、型として他 family と絡むのは hub の `Declaration` enum の variant としてだけ。
   「全 AST が一箇所」は chronological append の結果であり、守るべき責務境界ではない。
2. **AGENTS.md「主役を先頭に」との整合**。family module の主役はその family の AST 型と
   entrypoint。colocate すると各ファイルが「型 → parse → commit → recovery」の自己完結した
   読み物になる。`ast.rs` facade 案では、family の編集が常に 2 ファイルへ跨り、`ast.rs` 自体は
   主役のない grab-bag になる（AGENTS.md が避ける形）。
3. **外部依存面は facade が吸収する**。`expression.rs` が import する 14 型は §3.3 の
   `pub(crate) use` で path 不変。re-export chain は hub の 1 段だけで、深い chain は生じない。
4. **precedent との整合**。polymorphic_variant が親に AST を残したのは、出力型が親所有
   （`TypePrimary` の variant）だから。declaration では逆に、family AST は family 所有で、
   親所有なのは dispatch enum 側。同じ原則（型は所有者に置く）が family-colocated を導く。

hub に残す vocabulary は「複数 family を跨いで初めて意味を持つ型」に限る:
`Declaration`・`HeaderDeclaration`・`HeaderStatementIntro`・`StatementIntro`・`Recovered`・
`VisibilityPrefix`・`DeclarationTypeParameter`・`DirectRootCandidateOutput`・
`DeclarationBracedNewlineOwner`。per-family の `*StatementIntro` struct は family へ移す
（hub の `StatementIntro` enum からは glob 経由で見える）。

共有 core の AST も同じ原則で core module に置く: `EnumBody`/`EnumBracedBody`/
`EnumEqualsVariantBody`/`EnumIndentedVariantBody`/`EnumVariant`/`EnumVariantPayload` は
Error が Enum の型をそのまま再利用する共有 vocabulary なので variant core へ、
`DerivesAttachment`/`DerivesClause`/`DerivesVia`/`DerivesAttachmentPosition` は derives core へ。
`EnumDeclaration`/`ErrorDeclaration` の宣言型そのものは各 family へ。

## 5. 提案モジュールレイアウト

### 5.1 ファイルツリー

命名について: family 名の大半（`enum`・`struct`・`type`・`mod`・`impl`・`for`・`use`）は Rust の
予約語で module 名にできない。yulang2 oracle に `act_decl.rs` の precedent があるため、
**全 family へ `_decl` suffix を統一適用**し（予約語でない role/act/cast/error も揃える）、
唯一 statement である For は AST 名 `ForStatement` に合わせて `for_statement.rs` とする。

```text
crates/yu-syntax/src/grammar/
  declaration.rs                 # hub（§6）
  declaration/
    tests.rs                     # 既存・無変更
    # --- 共有 core（family に属さない） ---
    derives.rs                   # derives driver + isolated adapters + via     (~1,050 行)
    variant_core.rs              # variant sequence/payload driver + 共有 field/scan 層
                                 #                                              (~3,000 行)
    binding_style_body.rs        # classify/parse/commit_binding_style_body     (~150 行)
    # --- family module ---
    use_decl.rs                  # Use 一式 + projection + micro helpers        (~2,500 行)
    struct_decl.rs               # Struct 一式（field/scan 共有層は variant_core へ）(~2,300 行)
    cast_decl.rs                 # Cast 一式                                    (~1,600 行)
    type_decl.rs                 # Type 一式 + TAI post-header decision         (~1,600 行)
    act_decl.rs                  # Act 一式                                     (~1,250 行)
    impl_decl.rs                 # standalone Impl + impl tail 共有 core + TAI adapter (~1,250 行)
    enum_decl.rs                 # Enum header/body/commit/entrypoint           (~1,100 行)
    operator_header.rs           # operator header 宣言一式                     (~1,000 行)
    error_decl.rs                # Error header/body/commit/entrypoint          (~950 行)
    mod_decl.rs                  # Mod 一式                                     (~900 行)
    for_statement.rs             # For 文一式（1284–2173 の連続領域）           (~900 行)
    role_decl.rs                 # Role 一式                                    (~850 行)
    binding_decl.rs              # Binding 一式 + ParsedBinding* carrier        (~500 行)
```

行数は §2.1 の領域実測からの見積り（±2 割程度のブレは想定内）。合計 ≈ 20,900 行が子へ移り、
hub は約 1,900–2,400 行に落ちる。

### 5.2 variant core と struct field/scan 層の裁定

§2.2 の追加発見のとおり、Struct 生まれの field/list 走査層（`scan_struct_field_invalid_run`・
`scan_struct_comma`・`push/pop_struct_layout`・`consume_struct_field_name/type_trivia`・
`struct_outer_owned_mismatched_close_pending` とその下請け、named/tuple field の parse/commit・
`variant_field_recovery_role`・`emit_variant_field_missing/error`）は Struct と Enum/Error variant
payload の両方が使う。置き場所は 3 択:

- (a) **variant_core.rs に置く（推奨）**: 「family は共有 core に依存する」という一方向の依存だけが
  残る。歴史的にも Enum Gate 6 が「Struct field-loop 抽出込み」でこの層を共有化した経緯と一致する。
  variant_core は「variant 列 + payload + それを支える field/list 走査」という 1 責務として
  読める。名前が `struct_` prefix のまま variant_core に住む違和感は rename follow-up まで許容する。
- (b) struct_decl.rs に置いて variant_core から参照: 共有 core が特定 family に依存する逆向きの
  edge ができ、「Error を読むには struct_decl を開く」構造になる。非推奨。
- (c) 第 4 の共有 module（`field_scan.rs` 等）: 依存方向は正しいが module がもう 1 枚増え、
  variant_core との境界（field loop はどちら？）が新たな判断問題になる。variant_core が
  ~3,000 行に収まる見込みなので、分ける必然がない。

なお `struct_trivia_has_newline` と `DeclarationBracedNewlineOwner` 群は derives/type/cast まで
使う汎用 plumbing なので、この層ではなく hub に置く（§2.2）。

### 5.3 impl tail core の裁定

impl tail 共有 core（`ImplTailOwnerSpec`・`parse_impl_tail_ast`・`commit_impl_tail`・episode spec）と
TAI adapter（`parse/commit_type_attached_impl_isolated`）は **impl_decl.rs に同居させる**。
独立 module（`impl_tail.rs`）にはしない。

理由: standalone Impl は文法上ほぼ「intro + tail」そのもので、tail を別 module にすると
impl_decl.rs が intro recognizer と emit だけの殻になる。TAI adapter は「Type が消費する 2 関数」
という narrow surface で、type_decl.rs からは hub mesh 経由でその 2 関数だけを呼ぶ。
「どちらの family にも独立には動かせない」という先行調査の警告は、**両方の consumer を持つ単一の
所有 module を作る**ことで解消しており、derives（5 owner・完全中立）とは共有の形が違うので
対称に扱う必要はない。ユーザが「共有 core はすべて sibling core module」という一貫性を優先する
なら `impl_tail.rs` 分離も成立する（open question 2）。

### 5.4 各 family module の中身（共通パターン）

各 family module は次の並びで構成する（AGENTS.md「主役を先頭に」準拠）:

1. family AST 型（`XxxDeclaration`・body 型・`XxxStatementIntro`）
2. `pub(crate)` entrypoint（`parse_xxx_declaration_isolated` / `commit_xxx_declaration_isolated` 等）
3. intro recognizer（`recognize_xxx_statement_intro`）
4. episode spec・body 補助・boundary/pending 述語
5. emit / retry 群（現在 15162–16324 に分散しているものを回収）

Use のみ追加で projection 関数（`project_use_route`・`expand_use_tree` 等）と micro parse helper
（`parse_open_brace`〜`parse_use_separator`。call-site 実測で Use 専用と確認済み）を含む。

## 6. 分割後の `declaration.rs`（hub）

残るもの:

- doc header・`use` 群（当面現状維持。子が `use super::*;` で共有するため削れない）
- `mod` 宣言 15 本・private glob 15 本・facade `pub(crate) use` block（§3.3、~60 行）
- 共有 vocabulary: `Declaration`・`HeaderDeclaration`・`HeaderStatementIntro`・`StatementIntro`・
  `Recovered`・`VisibilityPrefix`・`DeclarationTypeParameter`・`DirectRootCandidateOutput`・
  `DeclarationBracedNewlineOwner`
- root direct dispatch: `parse_direct_root_candidate(_with_local)`・`emit_root_error` 系
- header mode wiring: `commit_header_statement`・`parse_direct_header_declaration`・
  `parse_header_declaration`
- 中央 dispatcher: `recognize_statement_intro`・`binding_statement_selected`
- root AST dispatch: `parse_declaration`
- 共有 plumbing（§2.2 実測で複数 family 横断のもの）: inline trivia scanner 4 種・
  `visibility_prefix`/`emit_visibility`・`commit_word`/`commit_character`/`commit_trivia`/
  `committed_position`/`committed_at_eof`/`commit_word_candidate`/`commit_maybe_character` 系・
  `direct_expression_error_retry`/`emit_expression_missing_with_role`/`direct_expression_candidate`・
  `emit_layout_missing`・`consume_source_range`・`scan_declaration_type_parameter_list/parameter` +
  range/kind/end accessor・`scan_declaration_exact_equals`/`declaration_operator_character`・
  `declaration_exact_equals_pending`/`declaration_exact_impl_pending`・`struct_trivia_has_newline`・
  `declaration_braced_newline_owner` 3 兄弟
- 末尾に `#[cfg(test)] mod tests;`

見積り約 1,900–2,400 行。「入口（root dispatch と statement intro）を開けば全 family への導線が
見える」という AGENTS.md の親 module 要件をこのファイルが担う。

## 7. Phase 計画

各 phase は「verbatim move + 可視性付替え + hub glob/facade 追記 → `cargo check -p yu-syntax`
warning なし → `cargo test -p yu-syntax`（568 passed / 0 failed、件数一致まで確認）→
`cargo fmt` → 1 commit」。**tests.rs の diff が空であることを毎 phase 確認する。**
yu-syntax のテストは軽量（infer crate のような memory 制約は無関係）なので毎 phase 全件流す。

順序は「共有 core → 自己完結 family → core 依存 family → hub 整理」。§3.4 のとおり mechanical
には任意順で compile するが、この順が (i) 小さい pilot で機構を検証してから大物に進む、
(ii) 各 phase の切り出し境界を「前 phase で共有 core が抜けた残り全部」にできて cut が単純、
という 2 点で最も安全。

| Phase | 内容 | 規模 | リスク | 順序制約 |
|---|---|---|---|---|
| P1 | `binding_style_body.rs`（pilot） | ~150 行 | 最小。mod 宣言・`use super::*`・`pub(super)` 一律・hub glob の機構をここで実証 | 最初 |
| P2 | `derives.rs` | ~1,050 行 | 小。12228–13268 のほぼ連続領域。5 owner の call site は hub glob で無修正 | P1 後 |
| P3 | `for_statement.rs` | ~900 行 | 小。1284–2173 完全連続 + intro struct。**最初の facade エントリ**（`ForStatement`・parse/commit 2 関数）をここで実証 | P1 後 |
| P4 | `use_decl.rs` | ~2,500 行 | 中。4 領域（emit 16178–16324 / commit 17094–18340 / AST 型 19176–19539 / AST parse 22150–22810）からの回収。共有 plumbing（`commit_trivia` 系）を誤って持ち出さないこと | P3 後 |
| P5 | `operator_header.rs` | ~1,000 行 | 小〜中。17039–17093 の共有 plumbing を hub に残す境界に注意 | P4 後 |
| P6 | `cast_decl.rs` | ~1,600 行 | 小〜中。4172–5724 ほぼ連続 + intro。binding_style_body(P1)・newline-owner 群(hub) への参照は mesh で解決 | P1 後 |
| P7 | `role_decl.rs`・`act_decl.rs`（2 commit） | ~850 + ~1,250 行 | 中。episode spec(2479–3628)・parse/commit・emit(15417–15685) の 3 領域回収。Role/Act の境界が 2596/2597 で接するので cut 位置を丁寧に | P2 後 |
| P8 | `impl_decl.rs`（tail core + TAI adapter 込み） | ~1,250 行 | 中。`#[cfg(test)]` isolated adapter 2 件（2451–2478）も verbatim move。TAI adapter への Type 側 call site(11568, 11702) は mesh で無修正 | P1 後 |
| P9 | `variant_core.rs` | ~3,000 行 | **最大**。7242–9641 に加え、Struct 領域内 interleave 分（20404–20713 の field 機構・20929–21324 の scan/pending 述語のうち variant 側 call site を持つもの）を §5.2 の closure で回収。境界判断が最も多い phase | P2 後、P10–P12 の前 |
| P10 | `enum_decl.rs`・`error_decl.rs`（2 commit） | ~1,100 + ~950 行 | 中。header・entrypoint・body 4 形態・commit・emit の回収。owner spec constructor は各 family 側 | P9 後 |
| P11 | `type_decl.rs` | ~1,600 行 | 中。10932–12227 + 13269–13543。`declaration_exact_*_pending`・newline-owner 群を hub に残す境界に注意 | P2・P8 後 |
| P12 | `struct_decl.rs` | ~2,300 行 | 中。P9 で variant 共有層が抜けた後の「struct 残り全部」なので cut は単純化されている | P9 後 |
| P13 | `mod_decl.rs`・`binding_decl.rs`（2 commit） | ~900 + ~500 行 | 小〜中。13719–14030・14688–14790・15952–16177・21696–22108 の混在領域を仕分ける最後の family phase | P1 後 |
| P14 | hub 整理 | diff 小 | 小。残留 item を「主役を先頭に」へ並べ替え、facade block と module doc を確定。unused import があれば削除 | 最後 |

P4–P5、P6–P8、P11–P13 は相互依存がないので、必要なら順序を入れ替えてよい。硬い制約は
「P1 が最初」「P9 → P10/P12」「P14 が最後」だけ。全体で 17 commit 程度、1 phase あたりの
review 対象は最大 3,000 行の pure move に収まる。

## 8. リスク評価

| リスク | 内容 | 緩和 |
|---|---|---|
| 可視性エラー | `pub(super)` 付け忘れ／facade 対象を子で `pub(crate)` にし忘れ → E0603/E0365 系 | 一律 `pub(super)` 規則（§3.2）で判断を排除。compile が即検出。facade は §2.3 の閉じたリストと突き合わせ |
| glob 曖昧性 | 2 つの子が同名 item を持つと use site で ambiguity エラー | 現状は単一 module 由来なので衝突ゼロ。将来の family 追加時に compile が loud に検出する（silent 破壊はない） |
| 境界判断ミス | 共有 plumbing を family へ持ち出す／family 固有物を hub に残す | §3.4 のとおり compile リスクはゼロ。可読性の問題として review で拾う。§2.2 の call-site 実測リストを review の checklist にする |
| P9 の切り出し漏れ | variant/field 共有層の closure 判定を誤る | 誤ってもどちらかの module に置かれるだけで compile/挙動は無傷。P12 レビュー時に「struct_decl に variant 側 call site 持ちの item が残っていないか」を再走査 |
| rustfmt | 中間状態での再 crash | 全 phase でファイルは縮む一方（最大の新規ファイルでも ~3,000 行）。リスク実質ゼロ。sandbox/host の version drift による format-only 差分は従来どおり分離 commit |
| doc comment 内 intra-doc link | `[commit_header_statement]` 等の相対リンクが module 移動で unresolved warning になりうる | phase ごとの `cargo check`/`cargo doc` warning を確認し、パス修飾を足す（挙動影響なし） |
| unused import warning | 領域が抜けた後の hub の `use` 群に unused が出る可能性（子の glob 経由使用が lint にどう数えられるかは rustc の版に依る） | phase ごとに warning ゼロを確認し、出たものだけ削る。先回りの import 整理はしない |
| git blame の断絶 | 大規模 move で行単位 blame が切れる | `git log --follow` / `-M` で追跡可能。commit message に move 元領域（行範囲）を明記する |
| テスト側の隠れ結合 | tests.rs がどこかの family の private item に「同一 module 前提」で触れている場合 | §3.1 の mesh 設計上、可視範囲は分割前と同値なので原理的に起きない。起きたら（= tests.rs を触りたくなったら）その phase を止めて設計を見直す |

## 9. Open questions（ユーザ判断待ち）

1. **命名 suffix**: 全 family へ `_decl` 統一（推奨、Y2 の `act_decl.rs` precedent）か、予約語
   衝突のない family（role・act・cast・error）だけ素の名前にするか。統一推奨の理由は grep 時の
   対称性と「このファイルは declaration family である」の自己記述性。
2. **impl tail core の置き場所**: impl_decl.rs 同居（推奨、§5.3）か、derives と対称に
   `impl_tail.rs` を独立させるか。
3. **variant_core.rs の名前**: `variant_core.rs`（推奨）／`variants.rs`／`variant_sequence.rs`。
   AGENTS.md の「曖昧名回避」に照らすと `_core` は許容範囲だが、より説明的な代案があれば。
4. **follow-up の扱い**（本計画 scope 外、着手可否と優先度だけ確認したい）:
   - `struct_` prefix のまま variant_core に住む共有 scanner 群の rename（例:
     `scan_struct_comma` → `scan_field_list_comma`）
   - `pub(super)` 一律 → narrow surface への段階的絞り込み
   - `tests.rs`（33,471 行）の family 別分割。test 追加が続けばこちらも rustfmt 限界に再接近する
     ため、いずれ同型の計画が要る
5. **phase 粒度**: 提案は module 単位 17 commit。より粗く（P7/P10/P13 を各 1 commit に束ねる）
   でもよいか。細かい側を推奨する理由は、pure move の review は「1 commit = 1 連続領域」が
   最も機械的に検証できるから。

---

改訂履歴:

- 2026-08-30: 初稿。current line map は commit `dfc213f9`（テスト分割直後）の実測。
