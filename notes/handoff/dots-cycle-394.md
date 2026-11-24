# Yulang cycle 394

この周に閉じた補題: なし（I-69: 元の compound RHS を直接導く規則を追加、分割なし）

選ばれた実出現の元 RHS を生成する S13bbba のみ。鎖の不足は C392 の (a) のまま。release、solver、model から capture/型種や source emission を推定しない。

## 実装・検証

- [compound source tree と証明](https://github.com/momota1029/yulang/blob/d26c604e5c74537613d665f2f9dad8130a20812e/lean/Yulang/GeneralDeclarativeI65CompoundSourceRhs394.lean)。record の payload/tail、variant tag、join 左右の中の declared nominal を再帰的に保ち、逆に native の value argument の中にある structural 式も保持する。元 binder/実 slot、宣言表の parameter 順、値/行と点/非点、継承 invariant で使う原両端をそのまま持つ。same authored Supplies、occurrence、元 ordinal、target で得た logical typed tree が、元 body の正規化構文に正確に戻る。
- [元 Body を処理する proof-producing evaluator](https://github.com/momota1029/yulang/blob/3c620fdd9f7af5c8a4565abebd88cefaadd48de0/lean/Yulang/GeneralDeclarativeI65DeriveCompoundOutput394.lean)。deriveOriginalCompoundOutput394 は per-output RHS/完成 code を仮定せず、元の出力名で Supplies を引き、実の型種付き capture read から元 body の record/variant/join/native/value/row を再帰して、typed tree と局所 source 導出を同時に作る。既存 selection/checker を変更したものではなく、未対応の形を言語の拒否にしない。
- C392 native の任意 arity/深さの導出を埋め込み、実 C393 native/tagged output の元 Body/target/ordinal/ordered vector が **同じ既存 C386 literal write** に戻ることを証明。新しい compound を旧 flat vector に並べ替えない。kinded where binder は元の child equation と exact target の capture を保つことも、親の既成 output batch を置かず検証した。
- [設計と七つの厳格検証](https://github.com/momota1029/yulang/blob/6ed80ae7db1428c6ba74f40195edf7935f42ebf4/notes/design/dots-cycle-394-compound-native-rhs.md)。name 重複のない元宣言で同じ actual ordinal の source/body/code は一意。nested native 引数内の record/join があると旧の bare/tagged projection は none になることを証明した。これは**投影先の表現の不足**であり、言語の拒否の証明ではない。表現済み local rule では actual typed binders が揃えば evaluator が任意の独立 source 導出の exact code を回収し、actual C393 typed output の wire も同じことを検証した。
- Lean 4.35.0 と exact lakefile.toml。新規 module 二件を lake env lean --trust=0 -DwarningAsError=true、独立 audit も各単独。GitHub から exact source/audit blobs を取得し別 output で両 build/audit を再実行、全て exit 0。設計内七件も immutable bytes で --stdin --trust=0 -DwarningAsError=true、exit 0。依存は標準公理 [propext, Classical.choice, Quot.sound] の範囲。全体 build/Rust/checker は未実施。

## 残り

**S13bbba は未完。** 全ての実選択から actual SourceBindingReads と selected frame を得る source rule（特に actual head/where kind を含む）と、compound logical equation が元の固定型の literal receipt に対応する一般規則がまだない。普通の fallback、root-only native、serial flatten、数値での型種推定で代用していない。今回は新しい wire output や受理条件を登録せず、spec 未決の挙動も見つけていない。S13bbbb の retention は未作業。質問ノートなし。

**14 = 未証明 3（S01・S10・S13bbba）+ 一部 11（S02–S09・S11–S12・S13bbbb）。** 最上段/固定文、既存 checklist、他の行は変更なし。追加分割なし。Step 1 未完、Step 2・3 未着手、C は後回し。fixture、停止性、旧 Local/C334、受理範囲は触らない。

発行は expected-head non-force の work/dots-main のみ。新規 module/audit 各2・barrel の2行追記・設計・心拍・報告の計8パス。凍結2件は blob ID のみ。使用枠不明。
- 最終照合開始 `2026-11-24T14:20:53.536Z`（50 分経過）。
