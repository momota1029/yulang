# Cycle 3 label・constructor名前解決の対照

旧Y2 `d4c8bc8fc`、新spec `816ed8f1d`。source全文/実行コマンド/全出力は `runtime-cycle-3-control.md` と `runtime-cycle-3-label-more.md`。self-contained no-preludeでcheck、dump --poly、run --print-roots。

| ID | 出典 | 規則 | 例 | 実機の結果 | 新 spec | Lean | 分類 | 備考 |
|---|---|---|---|---|---|---|---|---|
| C3-CTL-LABEL-01 | control-flow.md case/catch label | labelはarm集合への再帰関数として直接applyできる | `case 'again :next: :next -> 'again :end; :end ->7`、intのcatch版 | check/poly/run0、case7/catch2。caseでlabelを高階引数として渡す形も7 | 3c.5では `.again` 操作に変更済み | surface label elaboration未確認 | 違う | 旧直接applyの成功は旧文書通り。新仕様で同じ綴りを採用する意味ではない。 |
| C3-CTL-LABEL-02 | 同上 | 新しい`.again`綴りを旧処理系へ渡す | `case/catch 'again ...: 'again.again next` | check/run1 functionとrecord {again}のshape不一致、poly0に診断 | 3c.5は`.again`、新決定 | source label→Core対応未確認 | 違う | 旧処理系の未実装であり、新仕様の拒否例ではない。 |
| C3-CTL-LABEL-03 | control-flow.md label、字句スコープ | 入れ子の同名labelは内側へ束縛 | 同名`'again`の二重case/catch | check/poly/run0、case11/catch3（外側の別値へ飛ばない） | 3c.3、3c.5 lexical binding | Core束縛とsurface labelの橋渡し未確認 | 一致 | source scopeの具体成功。新labeled enum/cast全体の証明ではない。 |
| C3-CTL-ENUM-01 | patterns.md enum pattern | 未import短名はfresh binder、修飾/importするとconstructor | color::blueをred/green/blueでcase | 未修飾未importは1、修飾版/import版は3。全check/poly/run0 | 3b.2に同じ注意 | 解決済みnominal pattern核は名前解決を含まない | 一致 | parser/importの具体境界の確認、推論核の一般完全性とは別。 |
| C3-CTL-LABEL-04 | control-flow.md再帰例の翻訳 | arm集合の入力/返値型を変える探索 | symbol→intのcatch、int→symbol再入のcase、関数返値を二段適用 | check/run1、polyにshape不一致 | 3c.5の一般label型/受理断片へ一意に対応させていない | 未確認 | 未確認 | 実験の翻訳/型選択失敗を新specの意味論上の拒否と数えない。 |
