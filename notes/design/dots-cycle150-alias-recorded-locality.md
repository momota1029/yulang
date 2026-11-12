# Cycle150: literal occurrence equality を外す recorded alias coverage

一般 V5 は 6/14 供給・8/14 未解決。`GeneralDictionaryAliasRecordedLocality` は、
Related site の occurrence が focus と同じであるという以前の制限を外す。
異なる ID・子 ID・named output demand を持つ site も、その site 自身の実 packet
を同じ current model で replay するため、独立した存在モデルを混ぜない。

`Covered` は各 Related site に (1) 同じ occurrence の実 journal packet、
(2) 現在の selected key/children が存在する、という journal/classifier 条件。
Instance・BranchAt・Joint・Evidence は含めず、key 同士の等号も仮定しない。
各 site の replay と既存 journal-key coherence から同じ key の BranchAt を導く。
`covered_of_locality` は以前の literal locality と実focus packet/current selected
からこの coverage が従うことを示す。

`early_ordinary_joint` は、InitialSource からの実ordinary traceと、既存の
EarlyMergeChoices.Scheduled 証拠を**前提に取る**。traceからformation/growthを導き、
Scheduledから既存のcoherence定理を適用する。任意の実traceがScheduledであるとは
証明していない。Scheduledは既存のearly merge条件と全operational guardを保持する。
非自明aliasを禁止せず、空aliasesやoccurrence同一性を要求しないが、すべてのRelated
siteが記録済みで現在selectedというcoverageはなお残る。

SameInputsだけでは各occurrence固有のnamed outputsやcapture allocationの妥当性を
移せない。今回の定理はそれを仮定で隠さず、別々の実packetの同一モデルreplayで扱う。
未記録siteへの適用、任意alias classのcoverage、一般V5は未完成。

## 検証
Lean 4.35.0 direct compile `-DwarningAsError=true`: exit 0。
4定理の `#print axioms` と `#check @early_ordinary_joint` を
`lean --trust=0 -DwarningAsError=true` で検査: exit 0。
公理は propext / Classical.choice / Quot.sound のみ。
依存oleanは元commit 7a7b330のfocused build。full buildは行っていない。
