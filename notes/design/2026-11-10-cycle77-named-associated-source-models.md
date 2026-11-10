# Computed named allocation and independent name derivations

状態: Draft。2026-11-10、cycle77。有限associated source断片の接続。
この設計ノートの保存は最初のLean試作後となった。次回は試作前に保存する。

## 部分目標

cycle76の外部table/occurrence slot入力を、既存NamedAssociatedGraphの有限named列
から計算し、source名上の独立導出とordinary modelのiffまで接続する。
新しい意味論を選ばず、spec6.2の同名共有と6.3の普通の型変数・関連型等式に従う。

## 入力、判断、実行

入力は任意の有限`Program = List NamedOccurrence`、env/roles、wf、旧state。
Programの各行はscope解決済みreceiver/output名、関連名、base→goalのtemplate。
tableは既存の2位置/行allocatorで計算し、全occurrenceのreceiver/output slotも計算する。
既存stateのサイズはそのtable長であり、別のslot mapは入力でない。

独立`NamedDerives env roles p s name head`は次の二規則だけを持つ。
1. 元stateのあるslotに明示scalar等式があり、その計算済みsource名がnameならseed。
2. pのある行についてreceiver名のheadが導出され、独立の宣言解決とassociated型導出が
   template headからresultを与えれば、output名でresultを導出する。
共有名は同じ判断なのでidentity専用規則を置かない。実resolverや飽和の結果は参照しない。

実行は、計算したtableのordinary同一性等式を先に追加し、既存の有限associated
飽和とemitを行う。identity等式はvar-varで、元stateにないscalar seedを作らない。

## 量化された目標

任意env/roles、wf、awf、Program p、旧state s、全assignment vについて:

`All v (run env roles wf p s).atoms ↔ All v s.atoms ∧ ∃ values,
 Factors (table p) v values ∧ ∀ name head,
 NamedDerives env roles p s name head → Equivalent (values name) (base head)`。

同じ右辺でvも存在量化すると実ordinary solverのconsistent=trueと同値。
さらに全slot/headについて、返却stateの明示scalar Evidence iff そのsource名のNamedDerives。

## 証明連鎖と未達

ordinary identityがscalar seedを変えないことを示す。
allocatorのreceiver/output名保存を使い、割当slotの独立導出から名前導出へ帰納、
逆方向は任意の同名slotへidentityで輸送する。
導出名が必ずtable内にあることを証明し、cycle76のmodel iffから名前版へ移す。

有限programの大きさ・枝分かれ・cycle・同名・重複を制限しない。
有限programを実ソースから生成すること、templateが実receiverを忠実にmaterializeすること、
source scopeの決定、動的where生成、一般区間、最終分類、辞書は未達。
Q1/Q2、cycle23/24質問は維持し、任意templateを言語の自由度と解釈しない。
B4主要橋は5本のまま。全言語の主型性は結論に含まない。

## Yulang2

live work/dots-audit 55574b605のC3-PARENT両順/generic (11,22)とX13〜X16を再読。
source共有・関連型の素材であり、内部tableやnamed derivationの直接oracleではない。
新しい実機/parser実行は行わない。
