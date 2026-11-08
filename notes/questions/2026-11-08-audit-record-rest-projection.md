# Whole-record rest返値の追加field射影を、完全性の受理例に含める境界

## まず遅延する案

whole-recordを束縛するという§3b.3の決定は変更しない。下記の名前付き境界越しの受理保証は、source推論の対象fragmentとschemeの説明に接続されるまで「候補・未確認」として保存する。旧処理系の拒否を新specの拒否規則に追加しない。

```yulang
our keep {x, ..whole} = whole
(keep {x: 7, y: "kept"}).y
```

これは旧Y2でcheckは0、runで `{x:'open2} <: {y:'open0}` の制約エラーになる。keepの返値そのものには両fieldがある。直接の `((\{x,..whole}->whole){x:7,y:"kept"}).y` は成功し、同じ適用の結果を `my kept` に保存してから `.y` は拒否する。新仕様の単一field recordは末尾commaが必要なため、上は旧処理系向けの綴りである。

旧文書が説明するschemeは `('a & {x:'b}) -> 'a | {x:'b,..never}`。wholeの値保持だけから、任意の追加field射影をこのschemeで必ず受理できるとはまだ結論しない。新Leanの局所pattern規則は同じinputをrestへ渡すが、全source推論の主型性/完全性を表してはいない。

確認が必要な境界は「この名前付き版を新source完全性の受理例に含めるか、対象fragment/schemeのどの前提で保証するか」。wholeの意味を残余へ変える問いではない。明示 `{x,y,..whole}` は成功するが、それを新仕様で必須にする決定は監査では行わない。

根拠: `notes/audit/record-rest-boundary-cycle-3.md` とraw logs。動的solver provenance未追跡、根本原因と修正は未確定。新spec/Lean/sourceの変更なし。
