# Yulang Lean cycle30

開始 2026-11-09T06:28:28Z。integration/m1-final@610879607 を再取得し standing orders と inbox I-12 を再読。ACTIVE・上限なし。前回29のcompleted心拍と報告を確認。同じ作業場・キャッシュを再利用。報告29と心拍のmerge衝突は統合版優先で解消。

## 部分目標と達成
実ordinary atomsから直接双方向変数辺とscalar等式を抽出し、任意長の辺連鎖・循環を通じてscalar証拠を有限飽和する。その全モデル保存と正規化後の閉包を証明。**この狭い部分目標は達成**。有限Hornエンジンを再利用し、全Fact=Fin n×Baseの容量4*nを内部で計算。呼出側からfuelや閉包証明は要求しない。外部の意味的含意証明を入力せず実atomを検査する。

## 定理（量化・前提・効く側）
S=CommonRoleEvidenceSaturation、N=CommonRoleEvidenceNormalization、E=CommonRoleEvidenceSaturationExamples。
S/Nの全定理は任意n、s:State n（既存ordinary文法の証明を含む）を量化。Factはslot:Fin nと4種のBase。Linkedは入力に直接の双方向var辺があること。Derivedは入力の直接scalar証拠またはLinkedを通じた帰納的転送。一般の型付けや候補選択ではない。

- S.facts_complete: 全Fact fが計算されたfacts nに属する（補助）。
- S.facts_length: 全nでfactsの長さ=4*n（補助）。
- S.edge_exact: 全i,jで実Bool edge成功 iff Linked s i j（健全性/完全性補助）。
- S.seeds_exact: 全i,bで実seeds所属 iff 入力Evidence（健全性/完全性補助）。
- S.saturate_capacity: 出力長≤4*n、外部fuel不要（停止性補助）。
- S.saturate_seed: 全i,b、入力Evidenceから出力所属（完全性補助）。
- S.saturate_transfer: 全i,j,b、Linkedとj,bの出力所属からi,bも所属（閉包/完全性補助）。
- S.rules_derived: 全生成rule、全premiseのDerivedからconclusionのDerived（健全性補助）。
- S.saturate_exact: 全f、実飽和出力所属 iff 独立Derived（健全性/完全性）。
- S.saturate_stopped: 実firstFreshがnone、内部容量終了後に新しい有効factなし（停止/閉包）。
- S.saturate_least: 任意P:Fact→Propで、全入力Evidenceを含み全Linked転送で閉じるなら、全飽和factがPを満たす（最小性補助、主型性ではない）。
- S.derived_models: 全f、Derived s f、任意assignment aと入力全モデル成立の下で、a f.slotの型はf.baseと同値（健全性）。
- N.emit_atoms: 任意fact列fsとatom、実emit後所属 iff 元の所属またはfsのいずれかのscalar等式pair所属（補助）。
- N.emit_models: 全fs、各factがDerivedという前提の下で、全assignment aについてemit前後モデルiff（健全性/完全性）。
- N.normalize_models: 全assignment aについて実normalize前後モデルiff。Derivedや充足性を外部前提にしない。矛盾stateも対象（健全性/完全性）。
- N.normalize_linked: 全i,jでnormalize前後の直接双方向辺が同値（補助）。
- N.normalize_evidence: 全i,b、正規化後直接Evidence iff 入力Derived（健全性/完全性）。
- N.normalize_derived: 全f、正規化前後のDerivedが同値（補助）。
- N.saturate_fixedpoint: 全f、再飽和と初回飽和で所属同値（閉包/固定点）。atomリストの構造的冪等性ではない。
- N.materializes_int: 全i、Derived s (i,int) と任意assignment aの入力モデル成立の下で、実materializerがnormalize後のiをintにする（健全性補助）。
- E.before_unknown: 具体3slot連鎖で初期slot0は実decoderがnone（回帰）。
- E.after_all_int: 全i:Fin3、実normalize後全slotがint（回帰、直接辺でない2段の転送を含む）。
- E.all_int_model: all-intの具体assignmentが入力モデル、例は矛盾による自明化ではない（回帰）。
- E.same_models: 全Fin3 assignmentで例のnormalize前後モデルiff（回帰）。
- E.second_pass: 全Fact3で例の再飽和所属が初回と同値（回帰）。

## 未達と次
一般B4の5橋は依然残る: source boundary、generated work閉包、飽和停止/閉包、独立最終分類、辞書健全性/観察順序同値。今回は橋1/3内部のscalar decoderを修復しただけで、role feedback driver停止を閉じていない。主型性・X13〜16外側PROVEDは未達。
直接の相互辺だけが対象。一方向の有向cycleから得るSCC等価、構造型の伝播、任意の意味的含意は対象外。bool/unitは証拠に含むが既存materializerのencodeはこれらをNoneにする。固定点はfact所属同値で、normalizeを繰返すとatom重複は増え得る。状態依存receiver/source lowering/annotation生成/role最終選択は未解決。
次の候補: (1) 本正規化を自己出力診断tree入口へ接続 (2) 有向辺SCCと構造型の証拠生成 (3) feedback driverの状態同値と停止。意味論の新判断なし、質問ノートなし。

## Yulang2との照合
取得済みy2-claims-role-boundaries-cycle-2.md（ROLE-MORE-001〜008）とspec6.3を再読。旧whereの効力を新specに持ち込まない。今回のordinary scalar転送は言語候補選択ではない。最新audit枝再取得・新実機照合はしていない。取得済み資料にこの正規化の直接の実機試験はなく、その点は未照合。

## 検証
既存ELAN_HOMEとPATHを設定。
`cd lean && lake build --wfail Yulang.CommonRoleEvidenceSaturationExamples`: exit0、311 jobs。
`lake env lean --trust=0 /tmp/cycle30-audit.lean`: exit0、25定理、標準三公理のみ。
全体build/全Audit/verify-lean.shは指示に従い未実行。全体PASSとは言わない。
初期focused証明ではmap所属の束縛名衝突、simp不足、帰納法で不要仮定を残したためエラー。修正後再検証成功。読取りレビューで問題なし（独立ビルドはなし）。git diff --check成功。環境中断なし。空き19GB、使用量枠不明。

### 最終検証出力全文
~~~text
✔ [309/311] Built Yulang.CommonRoleEvidenceSaturation (1.2s)
✔ [310/311] Built Yulang.CommonRoleEvidenceNormalization (1.0s)
✔ [311/311] Built Yulang.CommonRoleEvidenceSaturationExamples (1.1s)
Build completed successfully (311 jobs).
'Yulang.CommonRoleEvidenceSaturation.facts_complete' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleEvidenceSaturation.facts_length' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleEvidenceSaturation.edge_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleEvidenceSaturation.seeds_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleEvidenceSaturation.saturate_capacity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleEvidenceSaturation.saturate_seed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleEvidenceSaturation.saturate_transfer' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleEvidenceSaturation.rules_derived' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleEvidenceSaturation.saturate_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleEvidenceSaturation.saturate_stopped' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleEvidenceSaturation.saturate_least' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleEvidenceSaturation.derived_models' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleEvidenceNormalization.emit_atoms' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleEvidenceNormalization.emit_models' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleEvidenceNormalization.normalize_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleEvidenceNormalization.normalize_linked' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleEvidenceNormalization.normalize_evidence' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleEvidenceNormalization.normalize_derived' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleEvidenceNormalization.saturate_fixedpoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleEvidenceNormalization.materializes_int' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleEvidenceSaturationExamples.before_unknown' depends on axioms: [propext]
'Yulang.CommonRoleEvidenceSaturationExamples.after_all_int' depends on axioms: [propext]
'Yulang.CommonRoleEvidenceSaturationExamples.all_int_model' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleEvidenceSaturationExamples.same_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleEvidenceSaturationExamples.second_pass' depends on axioms: [propext, Classical.choice, Quot.sound]
~~~

## 公開
新Lean3・root/Audit/README追記3・design/index2・report/heartbeat2の10自身変更ファイル。公開時は最新remoteと全tree差分を確認し、統合版の差分も必要なら含める。個別blobと小さなSHA tree、非force・expected-headでwork/dots-mainだけ更新。最終時刻・照合は公開後に記録。
