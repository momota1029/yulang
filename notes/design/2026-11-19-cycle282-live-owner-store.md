# Cycle 282 — 全 owner の live fixed 表と source 由来のアドレス上界
journal は versioned plans を新しいものから保持する。owner key の有限集合上で、最新の plan だけを一つずつ選ぶ。同じ seed なら、異 owner の固定ポートは絶対に衝突せず、同 owner の行は compiler 内で一意。全 live 表を一つの共有 witness に書くが、各古い consumer は版付き定義を展開した歴史表から読む。従って同じ固定ポートへ古い値と最新値の両方を書かない。この live target の有限 basis は Paterson の owner 候補と checked 宣言の inputNames だけから生成する。展開した RHS のサイズまたは全履歴表の一様な有限性とは区別する。
