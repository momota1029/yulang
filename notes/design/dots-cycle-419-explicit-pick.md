# C419: C11, 実 Pick の明示 out

仕様 6.5 の `impl Pick {x:'a, ..'rest}: type out = 'a` を、根が独立に分かった一点の record に限って検査する。掲載の `Index str int` の `char` を int 等へ置換しない。元の record、保持した split/residual、全可視表の実 Pick、両 binder を取得する。入力の行検査だけ C415 を利用し、選択・B6・固定出力行を読むのは同じ元の出力つき Request/State のみ。明示 body を出力名で照合し、元の発現・宣言 ordinal・出力 ordinal を B6 のキーにし、値の型の path を B6 input から得る、元 target の保持行と構築した明示 ledger に照合する。where・default・一般非点区間や W の未完了例（別の C14）には踏み込まない。先行入口、固定 I65、未対応 false を保つ。
