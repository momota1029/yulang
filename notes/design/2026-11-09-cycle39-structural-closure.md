# Cycle39: finite structural/path closure

状態: Draft。spec/04-types.md と既存Common意味論を変えない。

前回は一回のpath生成とpayload分解がモデルexactだった。今回は、それを反復し、計算された有限領域または実行時に検査された閉包証拠によって停止と閉包を区別する。燃料切れを言語エラーにしない。

データは有限変数Fin n上の実Atomリスト。宣言側の判断は各段での生成規則所属、意味側は全assignment aについてAll Common.model a atoms。実行版は既存normalizeを利用する。必要な外部仮定があれば名前つきで保持し、一般B4の終了とは報告しない。

部分目標: ∀ n xs a, 計算されたclosureのAll a iff 元xsのAll a、および返した閉包証拠の正確性を示す。そこから既存矛盾checkerと自己出力inferのモデル保存枝刈りへ接続する。

Yulang2は取得済みx-oracle-types-detailsのX13–X17を参照。局所区間挙動と外側のoracleを混同しない。最新実機照合は未実施。
