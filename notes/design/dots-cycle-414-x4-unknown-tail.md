# C414: C06 / X4 未解決のレコード tail

仕様 6.3 の X4 前半だけ。元の点要求 `R { x: int, ..'a }` の行、int の field 行、元の可視候補の単独の開いた head と同じ binder を使う where を保持する。元入力の論理 slot と、宣言の binder は区別する。

保留は読取り失敗ではない。現時点の元入力を調べ、根・field・tail は別名、tail への代入・alias・追加の根拠がない、先頭 field は actual int、候補 head は actual record tail、要求の出力はない、と確かめた場合だけ対象。本断片では余分な普通の行、制約、native の根拠、依存証明を使わない。raw root K2 の優先を維持し、根・field・tail の閉路安全性を明示し、open row が既存 graph の正規 record shape として出ないことを「tail が空」と読まない。

独立規則は `other .pending []` のみ。新規の `elected` や置換・差分・where 子生成はない。実行版は元行・候補・元 provenance からこの規則を再構成し、固定の結果型で pending/pending/書込なしを返す。従来の検査は委譲する。新規閉鎖には R6 の DictionarySound、新規実行分岐、元の全称の check_sound と X4/control をすべて要する。
