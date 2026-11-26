# C436 / I-79: 真の declared covariance は旧 header を通らない

正本 `integration/m1-final@a6c7ed28…`。C18 producer の `AuthoredUnaryChoice405.checked` には **registry 全体**の `Checked` が必要。C410 の unary reader のような一 declaration の `DeclarationChecked` だけでは足りない。一方、旧 `RoleDefault420.checkHeader` の便乗は実際の Box fixture で不可能。以下は exact source 上の設計・証明手順で、Lean コンパイルは未実施。

## 旧 gate が動かない理由（単に試していないのではない）

- `RoleDefault420.checkHeader` (Replay420 `b5d8b4cb…`) は `explicitCheck … (interpretation …)` を conjunct として必須にする。
- `GeneralSourceMetadataDeclarations291.explicitCheck` (`dd6b837a…`) は全 declaration HEAD/where/associated の `explicitUses` を走査し `supported` を要求。実ソース `row.head=[.app key [.var binder]]` から `(key,1)` が含まれる（`explicit_exact` で head の `PatternCovered` を逆に取り出してもよい）。
- `GeneralSourceMetadataUse291.supported` (`298b4d7d…`) は、右 kind／arity だけではなく、`primitives key = some …` または `invariantNominal key=true` が不可欠。 `GeneralNominalCenteredHeadWFSource.ConstructorUse` (`28e54c22…`) もまさにその二択。
- 逆に `ConstructorModes357.SourceMode.declared` は **同じ snapshot** の `primitives … key = none` と `invariants … key = false` を必須とする。 `readMode` は graph に declared-table が見つかったとき primitive/legacy-invariant を同時に見つければ失敗。不整合を許すため Box を invariant に塗り替えない。 `GeneralSourceMetadataRows291.Row.classification` は両 catalogue で `.unclassified` にし、実際の kind / variance は source body から得る（`GeneralDeclarativeWitnessVarianceFixtures357.actual_box_covariant`）。
- したがって valid declared covariance と old header true から、同じ key の none=some または false=true を得る。state 全体を範囲外と判定する根拠ではなく、旧実装チェックの誤った流用を排除する証明。

## 追記だけでできる native-aware header

```text
roles.check env.source.roles
&& GeneralDeclarativeWitnessModeCoverage357.check env
&& GeneralDeclarativeWitnessHeader349.checkedRegistry env.source
```

検査成功から roles の `Valid`、`ModeCoverage357.Coverage env`、各 row の旧来の `checksDecl` を取る。native `Coverage` は `readUse` に基づくため genuine declared key を受け取れる。 `ModeDeclaration357.scoped_decl (coverage.1 d member)` が **元の catalogue 上の** `d.ConstructorScoped` を与える。 `GeneralDeclarativeWitnessHeader349.decl_checked` (`1dc6b4e4…`) の証明を新 helper に実際の source fields のまま写し、その `declaration_scoped cov` **一箇所**を native `scoped_decl` に置き換える。signature, ids, produced, OutputOnly, scopes, countsCovered, paterson, conservative, captureStable は既存 `checksDecl`, `descent_parts` の全 conjunct を保持する。全体の `Nodup` は `checkedRegistry` が確認する。固定済みの old check/old evidence の定義は一文字も変えない。

`ModeDeclaration357.source_ready` だけで `Checked` とは言わない。この `SourceChecked` の `DeclarationReady` は weaker descent (smaller/stable) で、`DeclarationChecked` の `countsCovered` と `conservative` を一般には供給しない。両方を保持する上記の `checkedRegistry` を使う。fixture の where は空だが、registry 全体を空 where に制限する必要もない。もし legacy structural descent helper を通らない他の declaration が存在するなら、この狭い checker は unsupported のまま。言語拒否を追加しない。

## 最初に実行する境界試験

1. body-derived Box20 は `readUse env 20 1` で `.declared [coValue404]`、旧 `explicitCheck` が false、新 `checkHeader436` は true。
2. source body/registry unchanged のまま snapshot に invariant flag を立てた control は native check が false（これを positive に作り変えない）。
3. role table/arity、原 declaration ID の重複、未認識 constructor を置いた control は native check が false。foo.unclassified を nominal syntax として新しく受理する規則ではない。
4. これらの metadata test は public C18 checker の distinct true/false とは別。最後に実際の typed B6 retained row と同じ selective trace を通して、新 dispatcher の true（raw K2 なら false）、旧 R17 の全 witness `rfl` 保存まで確認する。
