# C441 — ref の row/value の順序と literal 境界

起点: 正本 `integration/m1-final@2e47eb95797eda5d68d1b62ac1664fe07cb1d2c5` の C440 exact 採用、I-74 / I-78 / I-79。C423 C21、spec §6.2 L57 と §4.6 L221–235。`_` は独立の binder であり、row position を捨てない。

- **本物の狭い候補** `impl Add (ref _ 'a)`（where・出力なし、可視候補一つ、別 binder）。元の authored 射影の最初が row point、二番が value point。宣言 source / readUse / current table の順と kind を一致させ、row covariant + value invariant の real modes を使う。型と行は端点と capture のまま別々に保つ。row covariance は実 run body の公開引数の正の位置から、value invariance は callback の input/output の両位置から検査する。bound `'f` を含む X21 rank-2 source lowering の実装ではない。
- `DeepRead` の型を保持し、独立な元の source trace の候補と元の row/value capture をそのまま使う。元の raw graph K2 は origin table の support でフィルタしない。二位置は binder なので payload constructor は調べず、raw 循環上にある元 root は prior branch の拒否を保つ。doc/rule は「raw nominal value-only Expr が row を表現する」と仮定しない。
- 新しい plain data witness は元の origin table の索引と raw rank/escape だけ、答えや mode vector を含めない。元の R20 の任意 witness Boolean は無変更。固定外形: `check p r w = true → ClassifiedAs ... ∧ ∀ m, Fits ... m → ReportEvidence ...`。
- **literal `ref _ int`** はそのまま試す。固定 `DeepRead` で .app int [] から実 `.ordinary (.base .int)` は読めず、旧 centered Expression application は row/value catalogue を読めない可能性がある。二つの独立な障害を証明する。int を binder に変えたものを文字どおりの例と数えず、元の式も意味論も変えない。追加の判断は本当に必要な場合に限る。
