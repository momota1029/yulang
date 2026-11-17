# Cycle241 — design-first aggregate rebase

開始13:30:30 UTC、研究14:15:30まで、最終14:25:30まで。
integration1c675172のI46/I47を再読。I47で240反証への設計判断が追加されていたため開始。
統合競合は監督版を優先し、237コメント修正を保持、240追加imports/design linksを重ねた。
凍結Audit.lean/README、specと独自inbox編集は行わない。

比較設計をLean着手前に保存し、A（owner-local rebase）を選択。
「私的名はsourceを制約しない」は現journalでは無条件でないため、source射影・
非escape・全live consumer再構築・有限進捗を別の義務に分けた。
初回成果は9新モジュール。表置換・実mergeの非escape射影・有限fact/dirty rank・
その実表との積機械を検証。これを全Yulang境界の完成とは扱わない。
Noop/Escapeは無制約置換の危険を示す独立の小例で、選択設計全体の反証ではない。

継続:230型具体private再評価の回帰、原sourceからの有限owner/観測閉包producer調査、
意味contractと機械serviceの接続。未証明な全境界Acc/EvidenceNodeを主張しない。
