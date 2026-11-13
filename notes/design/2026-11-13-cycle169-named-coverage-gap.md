# Cycle169: 旧MixedTree coverageの名前つき出力の穴

Status: Proof plan. 2026-11-13. Scope: Evidence coverage.

任意のregistry・Shared状態・需要について、journalが空で需要の名前つき出力が非空なら、旧Mixed168Treeはどのpayloadにも存在しない。記録nodeにはpacket membershipが必要で、scalar/spine leafはoutputs=[]を要求するためである。

既存のternary named-output source fixtureは初期journalが空で、現在モデルとsemantic Evidenceを持つ。cycle169のShared Stable移送を使い、SourceFormed・Shared Stable・非空虚なsemantic Evidenceと旧MixedTree不存在が両立することを示す。言語やV5自体の矛盾ではなく、旧構造証明書を普遍coverageとして扱えないことの限定的な反例である。新しい名前つきleaf拡張は別moduleで担当する。
