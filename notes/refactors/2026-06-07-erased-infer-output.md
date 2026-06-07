# erased lower へ移行する作業書

背景仕様:

- `spec/2026-06-07-principal-monomorphization.md`

## 目的

今の infer export は、推論中に集めた型・効果・apply evidence を IR に畳み込んでいる。
その結果、monomorphize が主型ではなく IR node に残った推論途中の型を読めてしまう。

この経路を切るため、lower の段階から「型推論用の computation 型」と「実行値の構造」を
分ける。infer の外へ出す IR から式 node の型と効果を消去するだけではなく、最終的には
lower が最初から erased IR を作る。
monomorphize は、主型、型を消した IR、`RefId` の解決テーブル、量化された `RefId` と
型クラス obligation の対応だけを入力にする。

## 方針

infer は推論中に型証拠を集めてよい。ただし、その証拠は infer 内で主型・scheme・diagnostics
へ畳み込む。monomorphize へ渡す IR は、型証拠を読み取れる構造を持たない。

monomorphize へ渡すものは概念的に次の形にする。

```rust
pub struct InferExport {
    pub erased: ErasedProgram,
}
```

diagnostics や language server 向けの情報は `InferExport` に含めない。
必要なら別 table として出す。monomorphize の入力型は `InferExport` だけに限定する。

実装上の `ErasedProgram` は、binding / root expression ごとに次の triple を持つ。

```rust
pub struct InferredExpr {
    pub typ: TypeBounds,
    pub eff: TypeBounds,
    pub ir: ErasedExpr,
}
```

`typ` と `eff` は erased IR node の field ではなく、lower / infer が外側でやりとりする
computation result である。`ErasedExpr` 自体は型・効果・annotation evidence・apply evidence を持たない。
これにより、後段は必要なら `typ` / `eff` を root constraint として読めるが、式木の途中に
畳み込まれた推論途中の型を読む経路は持たない。

## `ErasedProgram`

`ErasedProgram` は値の構造だけを持つ。

残すもの:

- module / binding / local binder の構造
- literal kind と literal value
- apply / lambda / block / if / catch / handler / record / variant などの構文構造
- direct reference node が持つ `RefId`
- span / source location
- pattern の binder 構造

消すもの:

- `Expr.ty`
- pattern の推論済み型
- expression / thunk / function の推論済み effect
- apply result type
- callee / argument / return の inferred slot type
- compact 表示用の型
- infer 内部の上下界
- 型注釈が置かれていた場所そのもの
- cast/coerce node

型注釈の意味は infer が主型と scheme metadata へ畳み込む。
後段に annotation evidence を渡してはならない。
cast/coerce は monomorphize / elaboration が producer-consumer の型差から挿入できるため、
erased IR に保持しない。

## direct refs と typeclass obligations

IR node は参照穴として `RefId` を持つ。direct な参照の意味は `RefExportTable` で渡す。

`RefId` は `InferExport` 全体で program-global に一意である。
binding-local な番号ではなく、erased IR、scheme、ref table のどこから見ても同じ参照穴を
同じ `RefId` で指す。

```rust
pub struct RefExportTable {
    pub direct: FxHashMap<RefId, DefId>,
    pub resolved_typeclass: FxHashMap<RefId, ResolvedTypeClassRef>,
}

pub struct ResolvedTypeClassRef {
    pub class: Path,
    pub member: DefId,
    pub impl_def: Option<DefId>,
    pub impl_member: DefId,
}
```

`direct` は通常の名前解決で、型クラス選択を伴わず `DefId` が確定する参照である。
例: 普通の関数、ローカル binding、module item。

first cut の実装では、legacy lower 済み AST にすでに `Var(DefId)` として入っている参照を、
erased lower の lexical local scope で分ける。lambda parameter、pattern binder、catch resume など
local binder を指す `Var(DefId)` は `ErasedExpr::Def(DefId)` として残す。local ではない
`Var(DefId)` は erased lower で synthetic な `RefId` を発行し、`ErasedExpr::Ref(RefId)` と
`RefExportTable.direct[RefId] = DefId` へ戻す。source ref と後解決 ref は元の `RefId` を保つ。

infer 時点で解けた型クラスや role member は `resolved_typeclass` に入れる。
これは direct 参照ではない。すでに impl selection は終わっているが、「型クラス経由で
この impl member に解けた」という identity を残す。

infer 時点でまだ解けない型クラスや role member は、scheme に属する `TypeClassObligation`
として残す。

```rust
pub struct Scheme {
    pub ty: PrincipalType,
    pub quantified_types: Vec<TypeVar>,
    pub quantified_effects: Vec<EffectVar>,
    pub quantified_refs: Vec<RefId>,
    pub typeclass_obligations: Vec<TypeClassObligation>,
}

pub struct TypeClassObligation {
    pub ref_id: RefId,
    pub class: Path,
    pub member: DefId,
    pub args: Vec<PrincipalType>,
    pub associated: Vec<AssociatedTypeConstraint>,
}
```

`TypeClassObligation` は「この型クラス要求が解けたら、どの `RefId` を埋めるか」を持つ。
主語は `RefId` ではなく型クラス要求である。

ここに入れる型クラス情報は、実装選択によって runtime の参照先が変わるものだけに限る。
主型の制約を作るだけで runtime の参照先を選ばない role 制約は入れない。

入れるもの:

- role / typeclass member 呼び出しで、impl 選択により呼ぶ `DefId` が変わる参照
- method selection が role member として解釈され、後段で impl を選ぶ参照
- infer 時点では impl が解けず、後段で impl を選ぶ参照

入れないもの:

- direct な名前解決だけで `DefId` が決まる参照
- infer 時点で impl が解けた型クラス参照
- 主型の制約を作るだけで runtime の参照先を選ばない role 制約
- diagnostics のためだけの候補情報
- 注釈の履歴
- 表示用に compact 化された型

infer 時点で impl が解けた型クラス参照は `RefExportTable.resolved_typeclass` に入れる。
その table は `RefId -> ResolvedTypeClassRef` であり、`impl_member` が実際に参照される
`DefId` である。ただし、`class` / `member` / `impl_def` も残す。
ここを `direct` に畳むと、型クラス経由だった identity が消える。

現行実装では role/typeclass の export identity は `DefId` ではなく `Path` である。
そのため `class` は `Path` として持つ。`impl_def` は通常の source impl / synthetic impl では
`Some` になるが、compiled snapshot 由来の候補ではまだ owner が保存されていないため `None` を許す。

`TypeClassObligation` は、scheme 内の型変数・効果変数を参照してよい。
monomorphize は scheme に具体代入を入れた後、その代入済み obligation を解く。
解決結果の impl member `DefId` は、obligation が持つ `ref_id` の concrete 解になる。

同じ `RefId` は、erased IR の参照 node と scheme の `typeclass_obligations` の両方に現れる。
これにより、「型クラスが解けた結果を IR のどこへ代入するか」が失われない。

## monomorphize 後の参照解決

`RefId` は program-global だが、最終的にどの単相化済み symbol を参照するかは、
その `RefId` が使われた monomorphize instance に依存する。

そのため、monomorphize 後の参照解決は `RefId` 単体ではなく、単相化 instance と組にして持つ。

```rust
pub struct MonoInstanceId(...);
pub struct MonoSymbol(String);

pub type ResolvedRefTable = FxHashMap<(MonoInstanceId, RefId), MonoSymbol>;
```

概念的には次の表である。

```text
ResolvedRefTable[(mono_name, ref_id)] = resolved_mono_name
```

意味は、「単相化された `mono_name` の body 内にある `ref_id` は、単相化後には
`resolved_mono_name` を参照する」である。

同じ `RefId` でも、`foo<int>` の中では `int_add`、`foo<float>` の中では `float_add` に
解けることがある。この違いは `RefId` ではなく `(MonoInstanceId, RefId)` にぶら下げる。

不変条件:

- `RefId` は `InferExport` 全体で一意。
- `RefExportTable.direct` は direct な `RefId -> DefId` だけを表す。
- `RefExportTable.resolved_typeclass` は infer 時点で解けた型クラス参照を
  `RefId -> ResolvedTypeClassRef` として表す。
- infer 時点でまだ解けない型クラス参照は、scheme の `typeclass_obligations` 側に現れる。
- `ResolvedRefTable` は monomorphize instance ごとの concrete 解決結果を表す。
- typeclass obligation が持つ `ref_id` は、単相化後に必ず
  `ResolvedRefTable[(instance, ref_id)]` を通って concrete 参照になる。
- `resolved_typeclass` の `RefId` も、単相化後に必ず
  `ResolvedRefTable[(instance, ref_id)]` を通って concrete 参照になる。
- direct ref は `RefExportTable.direct` から直接読んでもよいが、runtime IR へ落とす段階で
  同じ `ResolvedRefTable` に正規化してもよい。

型クラス参照の解決は、参照先を埋めるだけでは終わらない。
選ばれた impl member も普通の関数であり、さらに単相化される必要がある。

infer 時点で未解決だった `TypeClassObligation` の手順:

1. monomorphize が scheme に具体代入を入れる。
2. その scheme の `typeclass_obligations` にも同じ代入を入れる。
3. 代入済み obligation の `class/member/args/associated` から impl を選ぶ。
4. 選ばれた impl member `DefId` を、obligation が持つ `ref_id` の concrete 解にする。
5. `ResolvedRefTable[(instance, ref_id)] = impl_member_mono_symbol` を登録する。
6. impl member の主型に対する具体代入を作る。
7. `Demand(impl_member_def, concrete_subst)` を worklist に積む。

`fold` のように、選ばれた実装の返り値や内部の関数適用がさらに別の単相化を要求する場合は、
この impl member demand から次の需要が生まれる。

infer 時点で解けていた `resolved_typeclass` の手順:

1. monomorphize が `resolved_typeclass[ref_id]` を見る。
2. impl selection はやり直さず、記録済みの `impl_member` を使う。
3. `ResolvedRefTable[(instance, ref_id)] = impl_member_mono_symbol` を登録する。
4. impl member の主型に対する具体代入を作る。
5. `Demand(impl_member_def, concrete_subst)` を worklist に積む。

## monomorphize 入力 API

monomorphize の public input は、型付き IR を受け取らない。

許す入力:

- `SchemeTable`
- `ErasedProgram`
- `RefExportTable`

禁止する入力:

- infer 内部の `LowerState`
- `Expr.ty` を持つ typed IR
- apply evidence が型を直接持つ構造
- annotation evidence
- compact display type

型で保証するため、既存 `typed_ir::Expr` をそのまま渡す adapter は暫定でも避ける。
移行中に adapter が必要な場合も、adapter の出力型は必ず `ErasedProgram` にし、
monomorphize 側の関数 signature は型付き IR を受け取れない形にする。

## diagnostics / language server 情報

infer から出す IR には、diagnostics 用であっても型を持たせない。

language server や diagnostic renderer が型情報を必要とする場合は、IR とは別の table に逃がす。

```rust
pub struct InferDiagnosticExport {
    pub reports: Vec<DiagnosticReport>,
    pub language_server: Option<LanguageServerFacts>,
}

pub struct LanguageServerFacts {
    pub facts: FxHashMap<SourceFactId, DiagnosticFact>,
}
```

この table は `InferExport` とは別の出力であり、monomorphize の入力ではない。
crate boundary も分け、`yulang-monomorphize` から import できない位置に置く。

`LanguageServerFacts` が持ってよいもの:

- span / source location
- diagnostics の reason enum
- hover や error message 用に freeze された表示型
- role/member 候補の表示名
- definition / reference jump 用の `DefId` / `RefId`
- quick fix に必要な構造化 metadata

持ってはならないもの:

- 型付き IR
- `ExprId -> Type` のような推論結果 map
- infer 内部の上下界
- subtype graph
- apply evidence の型付き slot
- monomorphize が制約再構築に使える型証拠

表示型は、diagnostics のために freeze された view である。
主型や単相化の入力として再利用してはならない。

## 移行順

1. infer export / legacy lower の現状を棚卸しする。
   - `typed_ir::Expr` の型・効果フィールド
   - pattern に残る型
   - apply / coerce / handler evidence に残る型
   - `RefId` の発生場所
   - role / method / impl selection の発生場所
2. `ErasedProgram` と `RefExportTable` の型を追加する。
   - `yulang-erased-ir` に置く。
   - `RefExportTable` は typed IR ではなく erased IR 側の所有物にする。
   - まずは monomorphize はまだ差し替えない。
   - この段階で direct な `RefId -> DefId`、infer-resolved な
     `RefId -> ResolvedTypeClassRef`、scheme の `TypeClassObligation.ref_id` を
     検査できる dump を作る。
3. `erased_lower` で `ErasedProgram` を出す。
   - `LoweredComputation` は `tv` / `eff` / `ErasedExpr` を持つ `lower` の出力 carrier として置く。
   - 移行中は旧 typed IR export / diagnostics 用の shape side table を別に残す。
   - 最終形では source lowering の各 entrypoint が最初から `LoweredComputation` を返す。
   - `lower` はコピーせず、実際の lowering entrypoint を直接編集して `TypedExpr` carrier を外す。
   - binding / root は `{ typ, eff, ir }` の triple として出す。
   - 式 node の型・効果を IR に入れない。
   - annotation evidence は出さない。
4. 新しい elaboration crate の entrypoint を `InferExport` だけ受ける形で切る。
   - 作業名は `Elaborate`。crate 名は `yulang-elaborate` を候補にする。
   - 既存 `yulang-monomorphize` をそのまま流用しない。
   - `SchemeTable + ErasedProgram + RefExportTable` は `InferExport` の中から読む。
   - 旧 typed IR を読む処理は entrypoint の外へ追い出す。
5. elaborate 内で、主型と erased IR から単相化・cast 挿入に必要な制約を作り直す。
   - `expr.ty` 由来のロジックを、主型から作り直した制約へ置き換える。
   - apply / branch / handler / method selection は erased IR の構造と scheme から制約化する。
   - 関数型の cast は、呼び出し先へ遅延せず adapter lambda として生成する。
     引数は反変方向、返り値と返り effect は共変方向に cast する。
6. `resolved_typeclass` と `TypeClassObligation` を実際に解く。
   - `resolved_typeclass` は impl selection をやり直さず、記録済み `impl_member` を使う。
   - `resolved_typeclass` の impl member の主型にも具体代入を作り、monomorphize demand として
     worklist に積む。
   - `TypeClassObligation` は concrete 型代入後に impl selection を行う。
   - 解いた impl member `DefId` を obligation の `ref_id` の concrete 解として記録する。
   - 解いた impl member の主型にも具体代入を作り、monomorphize demand として worklist に積む。
7. diagnostics / language server 用の別 table を用意する。
   - `InferExport` には入れない。
   - 型付き IR ではなく、表示用に freeze された facts だけを持つ。
8. 旧 typed IR の型フィールドを export 経路から削除する。
   - 可能なら型定義自体を消す。
   - 移行中に旧 typed IR が残る場合も infer 内部に閉じ、export 型や monomorphize 入力へ出さない。

## 検証

最初に入れるべき検査:

- `ErasedProgram` に型・効果フィールドが存在しないことを型で保証する。
- monomorphize crate が infer の typed IR 型を import していないことを確認する。
- monomorphize crate が `InferDiagnosticExport` / `LanguageServerFacts` を import していないことを確認する。
- erased IR に現れる `RefId` は、`RefExportTable.direct`、`RefExportTable.resolved_typeclass`、
  いずれかの `TypeClassObligation.ref_id` のどれかに存在する。
- 同じ `RefId` が direct / resolved typeclass / unresolved obligation の複数に出る場合は export error にする。
- `ResolvedTypeClassRef` は必ず `class` / `member` / `impl_member` を持つ。
  `impl_def` は compiled snapshot 由来だけ `None` を許す。
- `TypeClassObligation` に入った role/member は必ず `RoleDefId + MemberDefId` を持つ。
- `resolved_typeclass` または typeclass obligation から得た impl member は、必ず impl member 自身の
  monomorphize demand を作る。
- annotation evidence が monomorphize input に存在しないことを regression test にする。

canary 候補:

- role/member 呼び出しを含む小さい関数で、impl が monomorphize 後にだけ決まる。
- infer 時点で impl が決まる role/member 呼び出しでも、IR node には型を残さず
  `resolved_typeclass` の `RefId -> impl_member` 解決だけで実行できる。
- 関数値を高階関数や record field に渡すケースで、関数 cast が adapter lambda として
  runtime IR に現れる。
- 型注釈で効果行が開くケースでも、monomorphize が注釈位置を読まず主型だけから制約を作る。
- `std::fs::open` / `std::str::line_view` / `for_in` 系の canary で、body 側に偶然残った型を使わない。

## 禁止事項

- monomorphize のために `Expr.ty` を残さない。
- 「移行期間だけ」として monomorphize entrypoint に typed IR を渡さない。
- annotation evidence を monomorphize input に戻さない。
- role/typeclass 制約をすべて `TypeClassObligation` に入れない。
  実装選択に関わるものだけ入れる。
- 関数 cast を呼び出し先の暗黙責務として残さない。
  型が変わる関数値は adapter lambda に包む。
- path / module / function 名の文字列で impl や型を決めない。
- `Any` / `Unknown` を concrete 型選択の fallback にしない。

## 未決事項

- `ResolvedTypeClassRef` に impl member 主型への具体代入を infer 時点でどこまで保存するか。
- `TypeClassObligation.associated` の正確な表現。

## 決定済み

- `RefId` は program-global にする。
- monomorphize 後の参照解決は `(MonoInstanceId, RefId) -> MonoSymbol` の表で持つ。
- direct ref は program-level の `RefExportTable.direct` に置く。
- infer 時点で impl が解けた role/member は direct に畳まず、
  `RefExportTable.resolved_typeclass` に `RefId -> ResolvedTypeClassRef` として置く。
- infer 時点でまだ解けない型クラス経由の参照は、scheme-owned な `TypeClassObligation` として持つ。
- `TypeClassObligation` は必ず解決結果を代入する `ref_id` を持つ。
- infer-resolved / monomorphize-resolved のどちらの型クラス参照でも、選んだ impl member は
  `ResolvedRefTable` へ入れるだけでなく、impl member 自身の monomorphize demand を作る。
- 関数 cast は adapter lambda として生成する。
  引数は反変、返り値と返り effect は共変に cast する。
- infer から出す IR には diagnostics 用であっても型を持たせない。
- language server 向けの診断・hover 用情報は、`InferExport` とは別の table に隔離する。
- first cut では `yulang-erased-ir` と、新しい elaboration crate を追加する。
  - 作業名は `Elaborate`。
  - crate 名候補は `yulang-elaborate`。
  - 既存 `yulang-monomorphize` は typed IR / evidence 前提が残るため、そのまま入口だけ
    差し替える対象にしない。
- erased IR は `typed_ir::Expr` 経由ではなく `erased_lower` で作る。
- `LoweredComputation` は `tv` / `eff` / `ErasedExpr` を持つ `lower` module の出力 carrier として置く。
- 移行中は `LowerState` の principal / top-level / lambda pattern の本線を erased carrier にし、
  typed shape が必要な旧経路だけ side table を読む。
- `lower` をコピーせず、実際の source lowering を module-by-module に
  `TypedExpr` 返却から `LoweredComputation` 返却へ変える。
- 最終形では source lowering の各 entrypoint が最初から `LoweredComputation` を返す。
- binding / root expression は `{ typ, eff, ir }` の triple として扱う。
  `typ` / `eff` は IR node の field ではない。
- lower 済み AST に `Var(DefId)` として残った global reference は erased lower で synthetic `RefId` に戻し、
  `RefExportTable.direct` に入れる。
- local binder reference は `ErasedExpr::Def(DefId)` として残す。
- `Coerce` は erased IR に入れない。legacy lower に `ExprKind::Coerce` が残っていても、
  erased lower では中身だけを使う。
