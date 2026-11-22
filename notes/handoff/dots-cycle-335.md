# C335: 実際に成功停止した raw の出現・通常状態・辞書を照合

## 今回の範囲

02:30 UTC 枠。開始 2026-11-22 02:31:04 UTC。開始時 integration は e60c9f2240e4a9eaf5b5ef85bc107a3acf4c1960。終盤に integration c72d15eeb14d6cb343933a31d7e1a89f9eeb5ebf で I-61 と更新 spec を確認。standing orders、inbox I-60→I-61、spec §6.3/6.5 と、C334 完了版 8c712916a4a7cb86398a3e6ece943585bb25fa99 を確認。work/dots-main のみ expected-head / nonforce で更新。主証明と独立監査の固定 pin は 293360074691286b8398007782d3292d5f0ea7d0。

## (4) I-60 健全性は残り 0 群、I-61 一般化の追補は 1 群

C334 の任意状態・任意現モデルに対する同一モデルの再帰辞書健全性は変更しない。以下の試作による受理範囲の独自変更はない。後半に確認した I-61 の承認済み case を一つ検証した。

## 旧 Local との対応：残り 1 群

C334 の「新成功→同じ旧成功」は既存の定理。旧定義と当時の証人定義の無条件の逆は C334 で偽だったが、これは**今回承認された I-61 の現在の意味に対する反例ではない**。新しい区間射影一般を通した後の到達可能な成功停止全域での対応はまだ 1 群。

## I-61: 中心の元レコードなしで、C334 の実例を選ぶ

終盤に届いた「2」の決定に沿って、まず C334 の両端が同じ可視 field と同じ residual RHS を読む部分を検証した。元の中心の行を初期普通状態の行リストから**実際に除いた**（no_center_present）。支持付きの両端と普通の lower ≤ center ≤ upper から、各同一モデルで中心が同じ record RHS と同値になる（center_is_record）。その精密な endpoint certificate から行を読み下すだけなら、元のモデル集合は変わらない。孤立した adaptor を用い、owner 100 が一度も完了しないまま checked な実 impl を選び、固定出力 5=3 の実 compiler receipt と同じ辞書、非空モデルを確認した（Cut.actual_selected / actual_repaired）。この回帰では中心行を未完了出力から読んでおらず、parser がそれを直接書いたとも扱わない。

**I-61 一般化の追補**は、両側の field/tail 名が異なる本当の非点区間、open/closed residual 一般と反復 binder の I-58 を同じ Read/compile へ統合し、更新後の全域の辞書健全性を再証明すること。この周では witness kernel へ既存 named read を使って狭い断片を渡しただけで、一般化を実装したとは主張しない。

## (2) 成功停止の部分正当性：残り 2 群

1. **通常状態・モデルの実射影。** `GeneralStoppedLower335.exact_models` は任意の raw source state と assignment について、実 encoder が成功したとき、通常 Models と同じ assignment の raw source Models が同値。type と row の source 名を別々に保ち、通常 atom、区間、記録 scalar、型引数がすべて一点の opaque nominal を写す。対応しない raw structural head、行引数、非点 nominal は黙って消さず拒む。raw journal 全体のモデルは射影した通常モデルを満たすが、帳簿・live history の逆含意は一般には今回仮定しない。`OrdinarySite335` は現行物理 Site の実中心を上下端と別に読み、occurrence ID・順序・出力名と固定 target をそのまま取る。

2. **実 raw 経路を通る初期 source の輸送。** `ProjectedTrace335.sources_preserved / source_slice` は full mixed raw Step の実有限経路で、各 snapshot のこの射影が成功し、終状態の実 raw モデルがあるものに適用。通常 atoms と区間の包含、物理 slot から同じ論理名で point nominal の RHS 保持を証明。元 scalar の exact storage は、前後の raw knownness、実モデル、scalar 型の分離から導き、別の保存仮定にはしない。射影可能な point 状態では Improve する reobserve を始められないことは既存条件からこの証明に使うだけで、一般の停止性やすべての経路の射影可能性は述べていない。初期の本物の source と同じ行だけが source support を得る。追加普通 atom や意味的に等しいだけの出力を、入力の由来にはしない。

3. **任意の実経路から、保存された versioned effect の発行元と最新の site。** `InstallHistory335.installed_origin` は初期 effect が空で実経路の終状態に記録された effect から、実際の過去の install と当時の正確な occurrence、旧 Installable / 未commit、そこから現在までの経路を得る。`retained_projected` はそこで発行した全実 Site の順序が raw の canonical 子列と一致し、全 site と親子 edge が終状態に残ることを証明。各要求の出力先は文字どおり同じ。 `saved_projection` は現 raw モデルで同じ live effect と保存サイトの実中心の意味を使える。これはすべての selected が effect を持つという主張ではない。実 C276 では leaf は raw Local selected だが対応する installed effect がない（`DisplayHistory335.selected_not_installed`）。従って一般証明には記録済み枝と、現在の source から葉を直接読む枝の双方が要る。

4. **実 C276 Display(list int) の差と二つの検証。** この raw Step と成功停止を使い、root (0,0,0)、子 (1,1,1)、元からの nominal/primitive 行、実際に増えた 4 本の reflexive atom を確認した。このケースでは raw journal **全体** と通常射影の Models が任意の同じ assignment で同値。一方、元の普通コンパイラはこの point span でも (2,1,3) を生成するため、literal raw 子照合が失敗する。到達性が仮定された抽象例ではなく、既存実 raw の結果を再読した差。
   - **literal 試作**：相異なる binder の実 span をそのまま使う孤立したコンパイラ。checked/covered registry と独立の実読み・receipt による一般 Frame と辞書の健全性を Lean で証明。実 raw C276 の同じ literal site と同じ辞書 payload が、任意の同じ raw モデルで証拠まで通る。実モデルも確認。元の I-60 Rule は変更しない。
   - **元の I-60 を使う試作**：元の compileBody の出力 atom を使い、raw の既存名 0,1 を変えずに fresh 2,3 を定義する。実 raw 子 (1,1,1) に一般 `SameDemand` の mode 別 alias と同じ出力先リストを対応させ、実に発行された (2,1,3) で元の I-60 `Retained` と同じ payload を得る。すべての元 raw モデルが既存名を保ったまま拡張でき、その割当自体も raw モデルで、同じものを一つの普通の再帰証拠に使う。未拘束な fresh 名も元の assignment と同じとは主張しない。C276 は出力なしの実例で、一般の出力付き実停止は未検証。どちらの表現も実 solver の新既定値にしていない。

5. **順序の一般補助。** `Canonical335` は where を実 clause ID 順にした registry が checked/coverage を保ち、同じ入力名・出力 table なら順序だけ異なる宣言を正準化した通常コンパイルが完全に一致することを示す。`CanonicalChoice335.election_exact` は ordinary の待ち判断もその順序変更に不変という条件の下、候補照合、K2、選定を両方向に輸送。raw と ordinary が正準形でも同じ placement を選ぶことは別問題。

**残り A**: 任意の実成功停止の初期/終状態と各 occurrence から、今使える source/output の由来、actual center、同じ固定出力/子の receipt を構成する橋。今回は scalar/point 全経路の初期由来と versioned effect の実発行元を証明したが、nonpoint・row・compound な観測、完了 output の source 化、未install の一般枝は残る。 **残り B**: 任意の実停止から返る診断木（不成功な下位診断を含む）、辞書・固定出力を同じモデルで射影する全体定理。C276 では両表現を通したが、一般の正準順と placement、source-only Models と journal の意味の逆向きは未証明。停止性は扱わない。

## 検証と公開

23 Lean モジュールの focused Lake --wfail、全 source の直接 trust=0 と別ファイル 8 本の独立監査が成功。固定 pin から 31 ファイルを読み戻し、完全一致した source を直接再検証し、別の新規 C335 オブジェクトでも 23 モジュールと 8 監査を再検証。177 定理の個別公理は Classical.choice / Quot.sound / propext のみ（不要なものを含む）。restricted gate は 90,046 宣言を走査。宣言照合、差分監査は全て成功。証拠は [notes/verification/cycle335](../verification/cycle335/reproduce.md)。
凍結 lean/Audit.lean / lean/README.md は書かず元の blob を照合。lean/Yulang.lean は公開ごとに旧全 bytes と digest を照合し、当該モジュールの import のみ追加。全 repo の Lake/Rust ビルド・実行、利用枠の残量は未確認。

## 次に

まず新 I-61 の異なる両端・残余一般と I-58 の証人を一体化し、既存の辞書健全性に接続する。その後は (2) の残り A を先に。記録済み effect に閉じない root/child の current readback（特に完了した子の出力と固定 target）を actual normalized raw から得る。`InstalledBetween` の正準 site と `ProjectedTrace` の source-only Slice の間で、実出力 provenance を普通行の意味と区別する。次に二つの placement のどれかを一般既定にせず、同じ canonical child/target と models の明示的 transport を証明する。

新規質問ノートなし。今回見つけたのは既存二層の表現差であり、受理範囲に関する判断は行っていない。C334 の質問へのユーザー回答は I-61 として確認済み。
