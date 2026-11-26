この周に閉じた G の行: G01（解決済み呼び出し側の bare nominal 範囲。 `exact_call_site_choice_iff_whole_wire448`、`Opaque448.Whole.check_full_sound448`）。残り20行。

# Cycle 448 — G01: opaque な名前と呼び出し側の全候補

- 実開始: 2026-11-26T19:30:54.092Z。完了時刻・経過は同じコミットの heartbeat を参照。使用量の枠は不明。
- I-83、inbox `1b9ef468ce4e6f844f53533a59c431f27119f66a`。終了時の正本: `integration/m1-final@ca9762e1994c3276bab4a485404d256854fbf9ca`、Lean `0ea13a53694e26936d2ea31ba06d6ad51b8cfd1a`。
- 検証済み技術 pin: `work/dots-main@f1d5063e5a50deb2c59eb6fce9d05930751ede4d`、Lean `a4c0ec91b0a274ef0800351eca93d8590c198197`。今回の技術成果は work/dots-main。正本への統合は未確認。

## G01 の独立な規則と同じ状態での検査

- 対象は spec §6.2/6.3 の、呼び出し側で解決済みの可視範囲、空 arity の宣言済み opaque nominal。元の一入力の両端を同じ真正の authored slot で読み、全可視候補の宣言は空 where、要求の出力は空。照合で nominal の本体を開かない。元の役・宣言・実 origins とルート K2 を保持する。
- `OpaqueVisibility448` は上流で解決済みの「所有ファイルが自身またはロード済み、かつアクセス可」を、従来 `ModuleVisibility.FileScope` と同じ条件で元の宣言 ID に適用する。全行の順序と identity を保持し、`SameResolvedInput` は出現と実 metadata compile 結果を同じ既存 FullProblem に結びつける。隠れた実装を後に足しても元の入力と候補の結果は不変。可視一覧は witness の自己申告ではない。
- `OpaqueRoster448` は可視候補ごとの元 bare head と本物の宣言済み mode を読む。同じ名前は実 `SourceHead`、違う名前は実位置の `SinglePhysical` と異なる rigid 名を保持した既存 `RigidCandidateMiss`。候補を削らず全順序を保つ。どの候補も実 mode と局所ヘッダーを持つ範囲を対象とし、読めない出所・候補を「不一致」に偽装しない。全可視件数は任意で、**合致した宣言が一つ**のときだけ選択する。生の根 K2 不在も必要。
- `whole_choice_assembly448` は実 `SelectedHeadOrigin395`、元の宣言番号、元の Event を保持する trace を作る。全モデルで辞書と元報告の空の出力列を保証する。候補リストや結果は wire に入れない。
- 入口 `Opaque448.Whole.check_full448` はすべての従来 witness を同じ C447 由来の累積枝に委譲し、全入力の Bool が不変。新 `.wholeBare` は元 origin index と有限 raw 証明表のみ。`whole_wire_iff_exact_independent_report448` と `exact_call_site_choice_iff_whole_wire448` は、独立な元局所選択から同じ状態の正確な報告を実際に通す有限データ、逆向きに実 replay と同じ報告を証明する。全 `FitsFull` の健全性も同じ入口で示した。
- 別の origin を出しても、実適合モデルがある状態で合致した全可視宣言が二つ以上なら、どの新 wire も選択報告を通さない。根に元 raw K2 があれば実モデルの前提なしに新 wire を通さない。言語の曖昧・拒否の新診断は実装していない。

## 実際の入口の対照

1. 再帰する nominal 本体を持つ実 named 例。別 ID の同じ role/同じ nominal head の impl を、未ロードまたはアクセス不可とすると元の FullProblem が保たれ同じ報告が通る。ロードしてアクセス可にすると二つの本物の候補が元の全 tape に並び、旧選択報告は新分岐で通らない。元 slot と報告を偽った対照も偽。実行結果 `[true,true,true,false,false,false]`。
2. 別の opaque 名の正規の候補を、選ぶ元宣言の前または後ろにロードした実例。前に置いた場合、元一覧 `[rival,chosen]` を残し、実宣言番号1を保持。実適合モデルで rival の SourceHead は rigid mismatch に矛盾し、選んだ側の同じモデルの辞書は成立する。新しい累積入口は両順序で正確な選択を認め、同名の可視 rival と誤報を通さない。旧枝は従来どおり。実行結果 `[true,true,true,false,false,true,false]`。

## 検証と次の境界

公式 Lean 4.35.0 `--trust=0 -DwarningAsError=true`、production-only 経路で新 8 production と 10 standalone Audit を個別に確認。60件は標準公理のみ（または公理なし）。Audit の import: Yulang.* 以外 0 件。他の Audit を読まない。2組の `#guard_msgs #eval` は実行対照であり定理の証明に使っていない。公開バイトと検査入力を照合。旧 7715 production・2111 Audit、旧他の Lean エントリ31、凍結 Audit.lean/README.md の blob ID 不変。集約ファイルに新 8 import の追記のみ。全量 Lean build、verify-lean.sh、Rust は dot では実行していない。

G01 の閉鎖範囲は、既存の解決済みアクセス/ロード情報と照合できる完全な bare 名の roster。今の FullProblem 単独からモジュールの可視性を復元することはできない（同じ消去後カタログ・出現でもロード範囲で一覧が異なることを証明済み）。一般の parser/import・アクセス解決の実装、別の物理 source を扱う一般化、任意の構造候補や where、G10、全体の NoFalseRejection や証人を探索する solver は未実装・未証明。G02 以降には着手していない。新たな言語仕様の質問は発生しなかった。
