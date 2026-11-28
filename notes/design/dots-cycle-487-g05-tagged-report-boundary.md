# cycle 487: G05Goal に対するこの周の検査の境界

- 新 tag は既存 flat branch とそのまま同じ Bool。新旧 report / witness を交差させると false。新 tag の根は与えられた元要求の全順序と C482 の既存 root checker で読む。
- 合格には元候補の全 path が要る。元 ordinal・元引数・元 path を C485 の既存 tape に戻し、最小型商の signed termination を回収。prior は独立に正しいという `G05ExactVisitInputs487` の前提を通し、局所型付けから許可を発行しない。
- 真の K2 はローカル選択用証拠の不要な mark。非循環の各候補では局所検査から rigid match、definitive mismatch、unresolved のいずれかの証拠を別に受け取る。証拠の欠落や失敗は mismatch にしない。この callback の意味と全 FitsFull の意味保存は `G05ExactLocalProtocol487` 等の名前つき前提。
- 実装した checker の成功から同じ元可視候補の独立な完全報告と全 FitsFull の evidence を、上記前提のもとで得る。正準訪問列を持つ報告には、全実候補の head arity の条件と局所証明書の完全性のもとで、実行可能な root/tape に局所 token を合わせた有限 witness がある。
- `G05Goal` 全体は証明しない。とくに独立報告の訪問条件はメンバーシップで、今の checker は順序と重複込みの正準リストを比較する。同じ候補列で観測リストを二重化しても独立な正確さは変わらないが、空でないリストの二重化を今の checker が受理する witness は無い。この境界は Lean で分けて示した。今後は「正準化した検証＋独立報告を保った符号」の対応を証明する。仕様や固定声明を変えて課題を消さない。
