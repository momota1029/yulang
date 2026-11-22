# C335: 実際の成功停止から通常状態を取り出す

まず既存の実 C276 Display (list int) 実行に結ぶ。raw の slot は既存の source/rowSource に読み下し、実中心は現行 Site による。scalar の記録と point 型引数を持つ opaque nominal はそのまま普通の等式にする。行パラメータ・非点 nominal や投影不能 head は黙って消さず、この断片の射影は失敗する。raw source の初期射影で裏づけられた行だけを source とし、停止時に普通に真であるだけの行に由来を与えない。

目標: 同じ任意の assignment に対する raw/通常 Models の同値（上の断片）、出現を保持した固定子順と確定 target の取り出し、raw の実成功から witnessed 診断木と辞書への戻し。停止済み範囲のみ、時間・停止性の主張なし。

## 実例で判明した placement の境界

実 C276 の raw Step で到達した停止状態に、元の nominal/primitive 行を保ったまま reflexive atom だけが 4 本足ることを読み取った。全 journal Models とこの普通状態の Models は、任意の同一 assignment で同値。raw 片は root/child の literal 三つ組 (0,0,0)/(1,1,1) を持つ。ところが今の普通コンパイラは、親の実 point span から子 (2,1,3) を生成する。型の違いではなく論理 endpoint の再命名であり、相互に等しいと示せても literal child check は失敗する。

この表現だけを比較するため、相異なる binder について actual span を再利用する別 compiler を作り、既存の ordinary Frame から全モデルでの正当性を得た。実 C276 のそのままの root と child に exact replay が通り、実モデルも確認した。既存 I-60 Rule・solver は変更しない。次は元の compiler を変えず、fresh aggregate を raw point へ正当に対応させる条件も比較する。

## 元の compiler を変えない replay

第二の表現では本当に実コンパイラが足した 8 つの通常 atom を使い、旧実モデルを名前 0,1 上まったく保つ構成で endpoint 2,3 だけを定義する。元からあった普通の行の origin は同じで、名前だけを真とする atom は独立の構成子の根拠に昇格しない。元の I-60 Classify で、親は元の普通 source slice から本物の (2,1,3) を生成し、子の lower/upper には普通の相互包含が根拠の読みを持つ。同じ辞書 payload を得るが、実 raw の子に対して型が各 mode で同値、出力先は文字どおり同じ、という明示的 placement 関係を使った。実 raw の全モデルについて元の名前のまま拡張できることを証明した。これを一般 solver の射影仕様に選んだわけではなく、元の assignment の未拘束な 2,3 まで同じとの主張でもない。
