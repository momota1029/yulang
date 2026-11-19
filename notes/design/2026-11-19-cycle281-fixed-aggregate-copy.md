# Cycle 281 — 集約のコピーの版を外した固定書き先

同一捕捉の compiler を意味そのもの（binder・上下・source endpoint）と target の割り当てに分ける。一方は現 packet の版付き target、他方は seed / invocation / declaration / binder / polarity の固定 target。タグ付き compiler を実行し、前者は既存の版付き merge を全モデルで読み戻せることを確認する。固定 target へは新しい版の数を入れない。二つの観測の実 binder/endpoint は別のデータとして残す。

同じ保護された base（古い固定 target の定義を含まない）を持ち、二つの書き先表がそれぞれ base 支持・公開支持・読み元から分離しているなら、固定表または版付き表で拡張した公開モデルは厳密に同じ。ここで「古い固定 target を参照する消費者」を無条件で書き換えない。完全な再設置には保持された消費者を展開したうえで同じ支持条件が残ることを証明する必要がある。
