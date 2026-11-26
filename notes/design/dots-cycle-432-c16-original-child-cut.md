# C432 C16: 元の選択木の where 出力を親の元出力専用 slot につなぐ

I-78 により C15 は統合済み。C16 は spec 6.3 の `Wrap(list 'a,out=list 'b) where Container('a,item='b)` が根拠。ここでは有限な実選択 trace からの読み戻しを追加する。元の where forest で実際の **子の導出そのもの** に位置づけ、等しい辞書・名前番号・モデル値は探索に使わない。親 declaration の元出力 binder から得た `OriginalWhereBinder395` の clause ordinal と output ordinal を合わせ、実子の B6 receipt と親の固定入力 slot（RHS でのみ用いる辞書の出力用変数）を同じ target につなぐ。適合モデルは位置同定に使わず、最後の RHS 値・所在の保持の証明にだけ使う。

禁止側の `Show (box 'a) where Container('a,item='b), Show 'b` は受理しない。得られるのは元親 RHS の出力専用 readback であり、別の where 子の名前なし入力の根拠ではない。兄弟は元順を表示・記録するが、実行順や安定化証明を導かない。

既存の実 C15 SourceTrace（元の位置 [71,0]）で索引の非空対照を行う。これは出力を持つ C16 canonical case とは別。C16 の独立 source rule・公開検査／固定 soundness がそろうまでは残り 7 のまま。