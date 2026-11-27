# C454: I-85 の同じ相だけで、全元 where から K2 の類を読む

- 根拠: `integration/m1-final@fa6ed2185643d29e9280c3abc4e5e573d55fdbe2`（C453 exact Lean `88e58b23ec1184d08b29c63eff9bc38420216087`）、inbox I-85 `0022cfc8f8bc0c6a6cde21c7b1d9fe7564466b5d` / I-84、C443 G03、spec 6.3 の needs 集約、6.5 と確定 K2 の実検査位置。
- C453 `WholeRoster` は「ある role の元子は一つの raw Alias 類に全部入る」という安全な十分条件で、異なる同 role 類の exact **same-phase** 報告に足りない。C452 `ScopedLiteralReport` は安全な子にも完全な G02 leaf の成功を要求するが、I-85 の K2 出所の報告からその成功を含意しない。旧入口は全入力の Bool をそのまま残す。
- データ: 同じ `FullProblem` の独立した `ParentSelection` と `OriginalDiagnostic`。C450 G03 の authored invariant list-point frame、実 canonical な unary literal binder where、空出力、元子をすべてその順で（位置数に上限を置かない）。C451 の exact finite matrix を使い同 role + **同じ相の raw Alias** とラベル一致を両方向で示す。安全な子の型選択/保留/曖昧さは決めず、実 raw status を全位置で記録する。
- 独立した判断: `∃ x : C452.InternalReport p, x.groups ≠ [] ∧ C453.SameReport r (exactSamePhaseReport x)`。C452 `InternalReport` は定理から復元する元 source/実 raw 関係であって checker 成功ではない。raw K2 のある各類はちょうど一回、類の元位置を欠落なし・宣言順のまま持つ。診断がゼロなら、この正の診断検査は通さない。レポートには代表、任意のラベル、類間の表示順規則を持たせない。
- 実行版は既存 data-only `SourceDiagnosticWire` を再生して非空と exact report を比較。結果に同じ親の選択済み head と元 where 列があること、各適合モデルについて実親 head の意味、全位置の raw RootCycle iff exactly one reported class witness、元位置の順序/保持を証明する。全称有限 witness と逆、以前の `check_full453` Bool 全引数同値。診断を圧縮した古い `WhereForest` は作らない。
- 試験: 実同 role の二つの別 raw 類（一方に元位置二つ）、異なる K2 状態/両類 K2、任意の元位置、raw-safe 子に選択の前提を足さない、違う元位置/順序/代表化/仮の類併合/親取り違えを false にする。これは G03 の元 literal 帯だけ。一般の構造 where/G15・名前付き出力/G16・相の遷移/G03b（実等式と新しい raw の読み直し）は別。
