# C22 — 元の output とモデルの二つの境界

- `MixedFixed442.replay442` は本物の候補テープ、raw root K2、元の lexical frame と要求を保った source replay で、R22 でも acceptance でもない。後段 `Replay.readOwnRefOutput` が元の typed B6 アプリ・mode・引数順と同じ frame の row/value center を照合する。報告の typed tree は row/tag 11 と value/tag 10 を保持し、固定先番号の差し替えで型を推定しない。
- `Cycle442I74MixedFixedEndToEnd` の元の `type out = ref 'e 'a` に対し、signed row `(56,[1,-2])` を持つ実適合モデル二つ。元の body・要求・ordinal・fixed target 21 と B6 出力は同一、nativeSyntax/typed view も同一。片方だけ target の値の内部 row が empty。元の source replay が通っても、このモデルでは同じ `I72.FixedTargets` が偽。
- `legacy_fixed_value_emission_iff_original_typed_footprint` は typed tree 任意深さでも実 row read が一つあれば legacy code がないことを示す。さらに全 .1 を固定して row center の .2 だけを変えられる二適合モデルでは、alias/composite を含む任意の単一旧 Expr が両方で元出力を表すことはない。逆に本当に意味が確認済みの別 source slot までの旧 alias 等式はその等式を中継できるだけで、意味を新規生成しない。
- 別の**実在する**旧 carrier `GeneralNominalState.Descriptor/Denotes` は引数の rowSource/value source と固定先の assignment equality を一緒に表せる。実 descriptor が既存 nominal slot に保持され、元の両 slot/target/constructor と対応し、同じ assignment が真正 companion Models を満たす場合の `existing_companion_has_independent_typed_fixed_equality442` は exact。同じ元 State の全 I72.Fits がその Models を満たす、という無条件 transport は上の反例により不可。これは既存 `Current.visible` 観測の置換でも、typed output の実保持イベントの provenance でも、完成/release の証拠でもない。

既存判断の中に canonical matching companion は供給されていない。現時点の public R21、I‑65 の声明・checker は変更しない。
