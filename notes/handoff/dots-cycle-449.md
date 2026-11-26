この周に閉じた G の行: G02（実宣言の invariant list-binder head の範囲。`exact_frame_wire_iff_independent_report449`、`ListSites449.Frame.check_full_sound449`）。残り19行。

# Cycle 449 — G02: 実際に調べる list の位置ごとの有限証人

- 実開始: 2026-11-26T20:28:33.455Z。完了時刻と経過は同じコミットの heartbeat を参照。使用量の枠は不明。
- 適用 I-83、inbox `1b9ef468ce4e6f844f53533a59c431f27119f66a`。終了時の正本: `integration/m1-final@48926909d6d38edf13ea0dead90d673417b3aaf4`、Lean `a4c0ec91b0a274ef0800351eca93d8590c198197`。
- 技術 pin: `work/dots-main@98511761a6d6f0622152b391cf436779b15d219d`、Lean `0135594ffed895c958a7e3e5c1468fa0bde89ca2`。今回の成果は work/dots-main。正本への統合は未確認。

## 独立な調査位置、有限データ、同じ報告

- spec §6.3 の K2 は根または非変数の head が本当に調べる位置が循環上にある場合。名前つきの本体を開かず、plain binder の payload は捕捉だけで新しい調査位置にしない。§6.5 の invariant value mode を元の宣言から読む。 `WrittenListSite` と `ListFrameVisits` は、元の書かれた list head・実入力の位置・authored origin、元 mode と捕捉を結ぶ独立な順序づけ。`inspection_safety_is_original_root_safety449` は、この範囲で集めた位置の安全性と元の raw RootCycle 不在が同値であることを示す。
- `checkSiteTable` は実位置の元の順序に証人を一つずつ重ねる。証人で位置や候補を指定しない。任意の元 raw graph と有限な位置列で、全実位置の AliasCycle 不在と実検査を通す有限表の存在が同値。C446/C447 の有向 Bound と flat Alias を別に扱う有限証人を使い、無関係な循環を禁止する全グラフ rank は求めない。 `accepted_frame_wire_indexes_actual_source_and_visited_cut449` は、受け入れた各 origin index と nth raw 証人が、その書かれた位置の実 origin・根に対応することを示す。単なる表の長さ比較ではない。
- 最初の singleton 経路は元 C410 の選択・実捕捉・報告をそのまま再現する。追加の `AuthoredFrame` / `ListFrameChoice` は、実候補一つ、where／要求出力なし、直に authored point を読む invariant list-binder の非空の入力列（異なる binder）を扱う。実データだけの `FrameWire` は元 index 列と有限の cut 表。同じ元 Event・実宣言番号・すべての実捕捉・辞書を再現する。選択が通ったという checker の前提や特定のモデルを独立規則に埋め込まない。
- 累積入口 `ListSites449.Frame.check_full449` は C448 までの全 witness の Bool を全入力で保存する。新形は `exact_frame_wire_iff_independent_report449` により同じ FullState の独立選択・正確な元報告と両向き。 `check_full_sound449` は同じ状態の全 FitsFull モデルで元の trace/capture/dictionary と報告の書き出しを示す。以前の規則・報告・State は変更せず、新しい同形の局所 trace だけ追加した。

## 実際の入口の対照

1. 元の再帰 list 宣言から invariant mode を導出した実例。根0から raw の矢印が二本あり、片向き Bound 2→0→1 と flat Alias 1~2 が混在する。捕捉する payload1 は実循環だが根0は循環上にない。従来の rank を兼用する証明器にはどの証人も通らず、新入口には実の適合モデルと exact capture/dictionary がある。実 alias 1~0 を足すと元の根が実循環になってすべての新 witness を通さない。偽 origin・証人不足／余り・誤報も含む実行結果 `[true,false,false,false,false,false]`。
2. 実入力の根が `[0,5]` の同じ状態で、元の別 binder 11→1・12→6 が同じ Event に届き、同じ適合モデルで辞書が成立。両 payload に実循環があっても binder として捕捉するだけなら true。第二の根だけに本当の戻り alias を足すと、第一の根は安全でも選択 false。元の payload を実際に第二の入力の head として読む場合も false。入れ替えた二つの cut／origin、cut 不足／余り、誤報は false。実行結果 `[true,false,false,false,false,false,false,false]`。

## 検証の範囲

公式 Lean 4.35.0 `--trust=0 -DwarningAsError=true`。公開 9 production + 11 standalone Audit を production-only import 経路で個別に確認、63件の公理出力は標準公理のみまたは公理なし。Audit の import: Yulang.* 以外 0 件。別 Audit を import しない。2組の `#guard_msgs #eval` は実行対照で、定理の証明ではない。公開バイトを検査入力と照合し、旧 7723 production、2121 Audit と他の Lean ファイル、凍結 Audit.lean/README.md の blob ID 不変を確認。集約ファイルは 9 import の追記のみ。全量 build、verify-lean.sh、Rust は実行していない。

閉鎖は上の実 invariant list-binder scope とその実調査位置に限る。一般の nested 非変数 pattern、別の mode／非点 source、同一 binder の繰り返し、where の子、複数候補、G03 以降、一般の R_full/NoFalseRejection と実 solver の証人生成／停止性は今回未着手。証人のない範囲外入力を言語の拒否とはしない。新しい言語仕様の質問は発生しなかった。
