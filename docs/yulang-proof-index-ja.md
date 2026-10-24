# Yulangの型健全性研究資料

このページは、現在読む証明稿、規範的な研究仕様、監査記録、歴史的資料を区別する索引である。証明を追加したり、証明 gate の状態を変更したりする文書ではない。

## 現在読む証明稿

以下の3稿は、限定された対象について紙上導出を記す個別の原稿である。いずれも独立査読と機械検証を終えた証明として扱わない。

| 文書 | 導出の対象 | 適用範囲と未完了部分 |
| --- | --- | --- |
| [操作的意味論と型健全性](yulang-operational-type-safety-ja.tex) | 宣言的型付けを持つ操作的計算について、値・操作の応答・継続の保存と進行を扱う。有限な効果と profile を含む安全性も別の定理として導く。 | この計算についての紙上導出であり、推論器や現行コンパイラーの全対応を示さない。原稿自身がソース対応を未完としている。実行 owner と保持する receiver evidence の区別は、後続のソース稿にある訂正を適用する。 |
| [ソース導出と実行核の接続](yulang-source-type-safety-ja.tex) | 2026年10月24日時点のソースから計算への導出を扱う。実行 owner と過去の receiver evidence を分け、rank-2、scoped release、wildcard、dot selection に関する候補構成も記す。 | 単独著者の未査読・未機械化稿である。候補規則の言語仕様への採用、ソースと native 実装および現行コンパイラーとの対応は未完であり、証明 gate の閉鎖を意味しない。 |
| [dot selection の安全性](yulang-dot-selection-safety-ja.tex) | 有限な選択証拠から、選択済みコードと型付け導出を構成する。 | 操作的計算に依存する。resolver の一意性と完全性、現行コンパイラーとの対応、独立査読は未完である。ソース稿は、この選択構成の一部を統合し、関連する前提を訂正している。 |

依存関係を読むときは、操作的意味論稿を実行核の紙上結果、dot selection 稿を有限証拠からその核へ接続する構成、ソース稿をソース導出と既存の owner 規則へ戻す後続稿として扱う。先行稿の証明を後続稿の訂正後の機械へ無検査で移してはならない。

## 規範的な研究仕様

[全言語意味論と型推論の拡張稿](yulang-whole-language-semantics-ja-expanded-20261023.tex)は、全言語を対象にする規範体系を提案する研究稿である。型付き意味論、推論手順、実装との照合目標を記すが、採用済みの言語仕様や全体証明の完了報告ではない。局所 evidence を構成する義務を含む未完了部分が残る。

この仕様は証明稿として引用しない。定義や目標を確認するときに参照し、成立済みの定理や現行実装との対応を主張するときは、対応する証明稿と現在の gate 状態を別に確認する。

## 監査と現在の gate 状態

R345監査が gate 基準として hash を固定する意味論稿は、拡張稿ではなく[拡張前の稿](yulang-whole-language-semantics-ja.tex)（SHA-256 `6246e7dc179a795b372603eac8cd64bf783ba69e9a4a733bcfc012ebd6869612`）である。拡張稿への切替や採用を暗黙に示さない。

[R345更新版の全言語意味論整合監査](Yulang%20Simple-sub%20%E6%8B%A1%E5%BC%B5%EF%BC%9A%E5%85%A8言語意味論整合監査・証明設計%EF%BC%88R345更新版%EF%BC%89.md)は、証拠、実装監査、未解決 gate を整理する監査・状態資料であり、証明本文ではない。

2026年10月24日の状態は[agent loop の現在状態](../tasks/agent-loop/current.json)を参照する。この時点で`OP-SEMANTICS-FULL-EFFECT`、`DOT-SELECTION-EVIDENCE-BRIDGE`、`CONSTRUCTOR-POLYMORPHISM-SCOPED-RELEASE`、`SOURCE-SAFETY-BRIDGE`は`OPEN_REVIEW`である。R149は`PARTIAL_REVIEWED`で、元のA/Bも未完了である。詳細な状態は現在状態ファイルを正とし、この索引では日付付きの要約以上に複製しない。

## 歴史的資料と安全な整理

次の文書は履歴や旧設計を調べる資料であり、現在の証明 authority ではない。

- [拡張前の全言語意味論稿](yulang-whole-language-semantics-ja.tex)
- [旧監査と crosswalk](Yulang%20Simple-sub%20%E6%8B%A1%E5%BC%B5%EF%BC%9A全体証明への移行監査・証明設計.md)、[全言語意味論整合版 crosswalk](Yulang%20Simple-sub%20%E6%8B%A1%E5%BC%B5%EF%BC%9A全体証明への移行監査・証明設計（全言語意味論整合版）.md)

旧証明コンパニオンと旧統合設計計画は、現行稿と重なる主張・訂正済みの設計説明を含むため、現行の docs から退役させた。内容を再確認するときは、[proof companion の固定版](https://github.com/momota1029/yulang/blob/8e4229bdc2d83d8fde9b38edb14f305419d5f5ea/docs/yulang-proof-companion-ja.md)と[統合設計計画の固定版](https://github.com/momota1029/yulang/blob/929f3a790b03261b28a04239fa65cfa5af5e9479/docs/yulang-unified-design-and-proof-plan-ja.md)を Git 履歴で読む。R255 と R302 の記録もこの固定版を指す。旧稿本文を現行の証明 authority として再利用しない。

拡張前の意味論稿と旧監査・crosswalk は、現行の gate が固定した入力・履歴として参照するため残す。これらは現行証明稿ではないが、A/B の元の主張、監査基準、各 gate が依拠した資料を追えるようにする。古い資料をさらに退役させる場合も、記録からの参照先と固定 hash を保つ。

現行資料の整理は次の状態にした。

1. この索引を現行の入口とし、証明3稿、規範的な研究仕様、監査・状態資料の役割を分けた。
2. 旧証明コンパニオンと統合設計計画の現行コピーを退役させ、R255/R302 の参照を固定した Git 版へ向けた。
3. gate 入力として固定された意味論稿・監査・crosswalk と、task/theory の履歴は残した。

旧 task や監査記録に使われたことは、その資料を現行の証明 authority にしない。反対に、現在の証明 authority ではないことも、gate の入力・履歴 pointer を消してよい理由にはならない。
