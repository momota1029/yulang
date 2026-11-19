# Cycle 282 — type の source 基底と row 全域
projection の型座標は初期 seed 以下の有限 source 基底、row 座標は全域を固定する。過去 type を順序評価する操作と live fixed 表のコピーは、どの row も変えない。従って finite type 名だけを同定して row 制約を捨ててしまう議論と区別できる。証明は固定表、history compiler、旧全 journal、再帰的 payload の全てに同じ witness を使う。
