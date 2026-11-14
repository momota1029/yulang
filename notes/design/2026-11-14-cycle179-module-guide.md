# Cycle179: 定理の型と残る境界

対象は I30 の元の G = `GeneralNominalCenteredGroundBoundary.groundBoundary`。
G'、分類、意味論、既存の定理を変更しない。以下は健全性側の部品と補助であり、
言語全体の完全性・主型性・一般の EvidenceNode 完了ではない。
型の全文は `tools/TypesCycle179.lean` の出力で確認する。

## 同一モデルでの discovery（健全性補助）

- `GeneralDictionaryNominalSharedDiscovery179.shared_shape_exists`:
  任意の context/declaration、異なる二つの slot、任意有限の名前列について、
  単一 nominal query の実際の Finished 検査から両 descriptor と引数区間を回復。
  名前の単射性を仮定しない。重複変数を含む具体的な Finished 例も検証した。
- `candidate_holds_iff_shared_merges`: 上記形式の実 Candidate と任意の現在の Models、
  terminal、空の出力を前提に、その同じモデルでの packet.Holds は、同名位置の
  意味的同値 Coherent と、実際の fresh capture merge 制約の連言と同値。
  candidate の存在モデルを現在のモデルへ置き換えてはいない。
- `GeneralDictionaryCenteredSharedAny179.point_shape_exists` と
  `point_holds_iff_shared_merges` は外側が同一 slot の場合を処理する。
  `holds_iff_shared_merges` は外側が等しい／異なる場合を統一し、任意の二 slot を扱う。
  内側引数区間は非点でもよい。sharing/merge 条件を自動とは主張しない。
- `GeneralDictionaryCenteredNested179.nested_holds/nested_evidence`:
  任意有限の unary nominal depth、単射な有限名列、正確な入力名列、実 Candidate、
  単一点の外側、実 report の PointInspection、terminal、空の出力から、
  任意の現在の Models で Holds/Evidence。Finished と Spine は仮定せず回復する。
  `recognized_evidence` は実行可能な syntax recognizer へ接続。
- `nested_evidence_at_G_root`: 実 G Reachable の元の root なら外側点性を回復する。
  role-local の terminal/nested format と全 singleton slot での PointInspection は残る。
  `nested_evidence_at_G` は generated focus も扱うが、その focus の点性を追加で要求する。
  いずれも一般 G.EvidenceNode ではない。
- NestedLimit179 は、inhabited な実 centered Candidate、外側点性、Finished から
  PointInspection を導けない具体例を証明する。同じ例で leaf Evidence は成立する。
  したがって PointInspection は言語の拒否規則ではなく、この helper の構造上の制限。

## 共通モデルの構成（初期状態の補助）

- `GeneralDictionaryCenteredPointReadback179.holds_iff_readback`:
  任意有限 linear nominal point leaf の source Models、input.Holds と正確な中心列の下で、
  centered Plan.Holds は有限 binder readback と同値。raw packet.Holds との混同を避ける。
- `GeneralDictionaryCenteredPointJoint179.readback_extension/joint_model`:
  任意有限 LinearLeafShape、正確な packet bounds、PointNames、source 名が seed 以下、
  元の source Models から、全元 source の Assignment（型と row）を厳密保存する
  別の extended モデルを存在構成する。そのモデルは initialAt の Models と Plan.Holds を満たす。
  非点の内側区間にも実際の nominal 観察値を入れ、単射名と fresh identity で衝突を防ぐ。
  これは元の固定モデルで Plan.Holds を示す主張ではない。
- `GeneralDictionaryCenteredPointCandidate179.discovered_shape/initial_joint`:
  実 Candidate の Finished から descriptor/bounds を回復し、上記の共通モデルへ接続。
- `GeneralDictionaryCenteredPointInstall179.initial_source_installable`:
  任意の InitialSource、点の root、実初期 Candidate + selected、singleton registry、
  有限単射名と exact nominal query/inputNames、terminal、root outputs=[] の下で Installable。
  Shape、PointNames、seed 上界、support、joint モデルを追加前提として要求しない。
  `initial_source_stable_instance` は同じ断片で Stable を使った現在モデルの Instance。
- `initial_committed`: この断片はすでに semantic Committed。Committed は packet list の
  メンバーシップではない。したがって Installable から novel Step や非 Stable は導けない。
  bad_model_not_selected は診断用の含意で、この断片に反例が存在することを主張しない。
- PointExample179.joint は実178 point fixture（内側区間(2,3)）へ上記構成を適用。
  binder の値を手で決めた例ではない。

## 有限 ledger frame（補助）

`GeneralNominalCenteredFrame179` は origin の根、site の端点/中心、schema の
観察根・binder・capture、必要な名前、有限 where clauses から有限 footprint を計算する。
`equations_iff` はその footprint 上の値一致だけで全 Plan.Equations を双方向移送する。
`equations_assign` は footprint 外の有限名の値更新を許す。
`ledger_frame/ledger_assign` は任意の登録済み site/plan を保存するが、raw journal Models
保存を別前提に残す。新しい binder が footprint 外という条件を到達可能性から導く証明は未完。
これは current journal の共通モデル構成が終わったという主張ではない。

## 次の正確な課題

1. 任意の reachable journal で新しい binder と既存 ledger footprint の分離、または
   意図した同一 binder の同値を生産する。初期状態の fresh-source 証明だけでは不足。
2. その更新による全 raw packet Models 保存を証明し、finite ledger frame と結合する。
3. generated/nonpoint/repeated/requirements/associated outputs を含む実 selected candidate へ
   共通モデル・guard を接続し、元の G の Stable から一般の現モデル EvidenceNode を生産する。

source frame と新しい補題を増やしても、一般 G.EvidenceNode の未証明数は減らない。

## 全 raw journal までの有限フレーム

`GeneralNominalCenteredEmptyFrame179` は raw sites の観察根と demand endpoints を
列挙する。`GeneralNominalRawFrame179` はさらに任意の raw packet の private state、
projection report、generated materialization schema の全参照名を有限列として列挙する。
`packet_iff`、`raw_models_frame`、`centered_models_frame/iff` は、最終的に任意の
centered state の全 Models を有限 `fullSources` 上の値一致だけから移送する。
この最終版には rawModels を別前提として残さず、empty-packets 仮定もない。

`centered_assign_kept` は footprint 内の再利用名について元の型値を保持し、
footprint 外なら任意の型値を書き込む有限更新を許す。row 値は assign が保存する。
これが証明するのは古い全モデルの保存であり、更新値同士の衝突整合性や新しい
Plan.Holds の成立は別途必要。source 名の seed 上界だけでは、過去の fresh binder も
含む fullSources との分離は導けない。前節の課題2の frame 定理自体は今回成立したが、
実 candidate の更新がその前提を満たす生産は課題1・3として残る。

## 任意の既存 journal 上の有限 nominal extension

`GeneralNominalCenteredJournalExtension179.nominal_extension` は任意の centered state、
有限 NominalArgument 列、元の Models と型値列を量化する。必要条件は各端点・観察根が
旧 fullSources にあること、各値の Fits/readback、同じ center への値の一致、旧 footprint
内に再使用する center の元の値保持。これらの局所的有限条件から、旧 Models を保ち、
旧 footprint の全 Assignment を保存し、指定した全 center の型値と NominalArgument.Holds
を同時に実現する extended モデルを構成する。新 Plan.Holds や共通モデルを仮定しない。
実 Candidate がこれらの overlap/readback 条件を供給することは引き続き未証明。
