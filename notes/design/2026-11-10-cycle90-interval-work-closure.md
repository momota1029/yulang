# Cycle 90: interval where の有限仕事領域

Status: Draft implementation contract. 2026-11-10.

## 部分目標と境界

既存の有限 Form・linear capture 断片で、任意の有限 declaration registry と区間 root から、実際に捕捉される全 where 子の再帰的な有限領域を計算する。caller の visit 列・fuel・source owner 列は不要にし、任意の実 prepare が生成した子がその領域に含まれ、全 endpoint source が元 root の canonical owner へ戻ることを示す。

spec/06-roles.md 6.3 の宣言時 Paterson と、既存 stable checker / interval scanner をそのまま使う。新しい候補選択規則は作らない。複数候補を全て列挙するのは探索の仕事領域であり、その候補の制約を無条件に連言した solver ではない。outside の scanner 結果は別に列挙して残す。unknown を拒否に変換しない。

## データ、独立判断、実行版

- Registry は List Declaration。WF は全 member の既存 stable check が true。
- Edge registry parent child は、registry member declaration、独立 Accepts derivation、元 requirements member から child が生成されること。
- Reach は Edge の反射推移閉包。closure や scan の出力を読んで定義しない。
- children は各実 inspect を呼び、accepted capture の元 where を全て展開する。closure は両 endpoint のサイズを尺度にして再帰する。outside declaration は各訪問 goal で別に記録する。
- domain は closure 全体の endpoint source occurrences。locate は元 root table への既存 canonical lookup。

## 目標の型

任意 registry / WF / root / target で target ∈ closure ↔ Reach。
任意 closure member parent、任意 slots / old / declaration ∈ registry / bindingSource、実 prepare が返した任意 child で child ∈ closure。
任意 registry / WF / root で、domain の全 occurrence は元 root table の canonical owner を持つ。source identity は元 endpoint 名で決まり、型の値の一致ではない。

これは静的 interval syntax からの仕事領域。ordinary state の絞り込みで異なる endpoint が materialize される一般再生成、K2、候補 guard、associated annotation、辞書の観察同値は未達。有限 endpoint source 名だけで goal の有限性を主張せず、実 Paterson decrease を用いる。

Yulang2: work/dots-audit の x-oracle C3-PARENT / C3-PARENT-NEG を新定義前に読んだ。両兄弟順と欠如の観測は参照素材であり、この interval closure 自体の新規実機比較ではない。


## 読み取りレビュー後の境界検査

独立レビューは重大な欠陥を見つけなかった。重要な区別として、既存 registry-wide `scan` は一つでも outside 宣言があれば全体で none になるが、今回の closure は個別 accepted 宣言の潜在仕事を保持し、outside は `boundaries` で別に報告する。checked な join head と tick 再帰 head が同居する registry で、scan は none、compute は実 tick descendants を返す検査を追加した。これは意図した仕事領域で、whole-registry scan の成功との同値ではない。compute の some は「全scanがsupported」を意味せず、boundariesも別に読む必要がある。

次の実装候補: 既存 `CommonRoleSourceTemplateClosure.actual_child_all_states` は int-only/unary source template に限って将来stateを扱う。今回の Form 区間とはcarrierが異なる。新しい橋では、実materializationからendpoint templateを保ち、全future-stateの生成childをそのtemplateの有限閉包に含めることを示す必要がある。任意state列をcaller入力にするだけで飽和を完成させない。
