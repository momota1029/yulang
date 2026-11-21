# dot cycle 322: 実 source の出力・既存の where 論理名・捕捉の宣言的健全性

2026-11-21 13:33:09 UTC 実測開始（13:30定時枠）。
`integration/m1-final` `2cf72ce2107b1333275df6329f757b265d312fb4`、
standing orders `7ae4d68d2ac7df80d1eadbd061dadd2296faf4c4`、
inbox `f259434f2d1b233c3dde6e6e2b9d804df9349b5a` と、
前回の完了 `95febf0bedda16ad784a5ac33f40b0a5835b61a0` を再読・照合。
今回も I-56。設計: [既存の論理名の読み出し](../design/2026-11-21-cycle322-existing-logical-names.md)。
solver の状態・Step・journal・slot・実行履歴を使わない。

## 今回確かめた一般補題

1. **通常状態にある等式を構成子の内側でも読める。**
   `Equalities322.Derives` は既存の等式・通常 alias・合同・対称・推移、
   共変ペアの成分逆向き分解から作る独立な構文上の証明で、
   `entails` は任意の普通状態の全モデルに対する健全性を示す。
   `Inequality322.invariant_at` は、一方向の通常不等式から不変 nominal
   の対応する引数が等値と示す。`DerivedNominal322.head_row` は、
   下端の頭が文字どおりの一行でなく、その出所で正当化した普通導出で
   あっても actual を読める。上端は不変性に使っても展開根拠にはしない。
   `ProjectedLower322.pair_first_head` は、二つのペア等式から
   普通の射影で既知 scalar 下端を得る。full ordinary state を保ったまま、
   片方の等式の出所が未完了だけならその scalar 読取りを得られない
   モデル、完了すれば得られる導出を実例で確認。一般の K2 の正規化
   や、どのプログラムを保留するかの新規則は主張しない。
2. **実引数中心の構文と、同じ binder の実名を構成。**
   `TermWalk322.substitute` は中間構成子に名前のない複合項をそのまま
   辿り、実際に現れた位置の捕捉を記録する。
   `TermOccurrences322.source_binders` は正確な順番と actual の極性を確認。
   `TermCapture322.named_binds` と `TermCapturedHead322.gives_heads` は、
   繰り返す binder の実項の等値が普通の導出で分かり、既存名が提供されるなら、
   全引数に共通の実名を実出現から選ぶ。候補から型モデルを探索しない。
   代表名の値が同じなら、同じ要求 target の式を
   `Substitute322.at_same_target` で運べる。必要な実項が普通の伝播から
   得られることや、共変な複合型の選定で共有が成立することは別の論点。
3. **実際の source emitter と全 where 列で一致。**
   `EmissionErasure322.all_source` は中心だけを消せば、任意の宣言シグネチャで
   新しい emitter の全要求列が既存の `GeneralDeclarationDemands.emitAll` の
   role・順序つき上下端・名前つき target と一致することを証明。
   `EmissionOperands322.input_proof` は正規化後の直接変数に同じ捕捉の三端を、
   `EmissionOutputs322.output_operand` は直接の出力専用 binder に同じ実名を
   使う。これらに新たな名前や等式証明を要しない。他の合成入力と named 要求
   では既存の普通状態での読み出しが必要。
   `NormalizeCovered322.normalize_covered` は、宣言の実際の構文が
   constructor metadata で被覆されるなら、隠れた field 除去と variant の
   tag 集約を行っても arity と解釈の被覆を保つ。使われない metadata を
   要求しない。`SourceCoverage322.compile_requirements` と
   `BinderEmission322.generates_from_binders` はその被覆から実 compiler
   の構文表を作り、変数のみの where と直接出力 binder の場合に
   where 側の名前選択／等式証明を取り除く。
4. **元の関連型出力 target をそのまま検証。**
   `DefaultCoverage322.return_from_body` と `FixedReturn322.requested_return`
   は実際の明示定義／role default の出所から両方の綴りをコンパイルし、
   親の固定 target には正規化した RHS の普通等式を確認する。
   単純 RHS が既にその actual と同じ名、または通常等式で結び付く場合は
   `supplied_center` / `positional_default_alias` で作れる。
   `ExistingNames322.recovered_forest` は、別ルートとして供給された
   既存の論理名リストから、普通の証明があるものを各位置で選べることを示す
   （既存要求の target を固定するには singleton を使う）。これは名前の
   候補を選び直す言語の判断でも、実行可能な型探索でもない。
   `RefuseOverwrite322.not_conservative` は、既存の要求名と式を読む全名前を
   保つなら、新事実を足しても元のモデルが偽にする等式を真にできないと示す。
5. **compiler と再帰 Evidence。**
   `OrdinaryProducer322.ordinary_produces` は任意の普通状態で、実観測の
   構文・通常の共有証明・既存名から捕捉を作り、確定した出力 RHS と合成
   where の普通の読み出しから、実 source emitter の子列に対する
   `BatchRecipe` を作る。compiler の結果やモデルの辞書を前提にしない。
   `EmissionLocal322.source_sound` はこの発行境界を使える宣言的断片について、
   選ばれた完全な診断木から全子を同じモデルで証明する。
   `DemandAliases322.evidence_transport` は、同じ各位置・名前・型であることを
   示せば Evidence を既存 alias の表現へ移せることを証明（default は
   actual 位置を読む）。言語の分類診断が alias で一致するという主張ではない。

## 実例

- チェック済みの Wrap / Container の実 source 発行で、where は元の点
  三端 (3,3,3) と item の target 5 を使用。未使用の fallback 400/401 を
  読まない。actual の名1が nominal 内に複合 pair を持つ普通式から、
  既存名3を実捕捉に取り、`ProducerFixture322.produced` を検証。
  可視候補・lower 観測・非再帰条件・順序付き子を検証し、
  `EmissionClassify322.actual_source_inhabited` で非空モデルに二節点の辞書。
- 同じ普通状態の既存 alias 表現では where 三端 (8,9,10)、item target 12
  を保つ。四つの compiler 等式は文字通りの行として存在しないが通常等式の
  合同・推移から帰結。実 emitter とは異なる**表現上の alias**であることを
  明示し、`AliasTransportFixture322.aliases_of_actual_child` で actual 発行の
  Evidence から同じモデルの再表現を検証。
- 12 から先の alias を一行だけ取り去ると、元の要求と同じ名前のままその
  出力等式を満たさない本物のモデルがある。そこで child の Evidence は偽、
  旧名12と RHS 名5を保つ任意の新等式列でも救えない。これは変数・合成型の
  新しい言語拒否ではなく、固定名の健全性の必要性の反例。

## 残る橋

**宣言的な (4): 1 本。** 承認された一般の source `Local.selected` から、
出所を保持する一般の正規化、正則 K2 の調査位置、全可視候補の生存／未了、
実位置と共有の普通の導出、および既存の合成 operand・親出力の安定普通等式を
得る source exactness。今回、実 source の名前発行・構文被覆・既存名への
普通導出・同一モデルでの再帰は独立に検証したが、選定全体を同値にしたり
証拠を持つことを選定と再定義したりしていない。C321の根拠なし/K2重複の
優先は保留のまま、係争部分と無関係な仕事を前進。新しい質問ノートなし。

**(2): 2 本。** solver 到達状態から普通状態と別の出所導出への射影／保持、
停止して返した診断木の宣言分類との一致。今回とも未着手。停止性、全体
build、Rust、Sat の実行結果は主張しない。使用量の枠は不明。

## 検証・公開

Lean 4.35.0。46モジュールの focused build は依存込み1,072 jobs、exit 0。
46ソースの個別 trust=0、I-51 standalone audit 6本も全て exit 0。
標準公理のみの scoped gate は61,327宣言で PASS。C322新定数667の
型・値の依存4,640を追い、指定の旧状態、solver、実行、物理配置の定数を
含まないことを照合。I-52 diff-only は exit 0、I-53 同時import 46件。
別の trust=0 検査でも、実 emitter の旧形式・中心つき形式・捕捉後の形式が
role 2、上下端 (3,3)、item target 5 を保つことを確認。
全出力は [検証](../verification/cycle322/verification.md)。
全体 build は実行せず。14:19 UTC までに検証し、50分枠で最終照合。

途中照合: 開始 `cea1884fd4ce551f82a9feabaefc1e176c6f9f85`、
早期 `c36a0bad9e96bd44aecbf39e8b231c0c4a98f24c`、
10分 `4530cc478736c72901d5c3d63a79d22bc8a8433a`、
20分 `95cba8536cd037df3ba3fae17b8c815cf9a4f546`、
30分 `592f5db25627982570e8e12f3cebf3128f3672e9`、
40分 `b684aa5a31417d4b3e43e4a774cbf9286932bfe0`。
最終検証ログの固定版 `59bd7613b57062cd72d8cc2059292f91231acc1f`。
`work/dots-main` のみ。前周からの差分 86 ファイル＋心拍1パス。
