# ASOB participation and precedence

このページは[ASOB](ambient-statement-owner-boundary.md)が参加する位置を示す。
implementation recordではなく、syntax-v0のownership referenceである。

## 参加する位置

ASOBは、completeまたはrecoveredなlocal anchorの後、そのanchorのgapがlocal continuation、retry、implicit separatorになる前だけに判定する。
openerの最初のitem、explicit separatorがすでに開いたnext item、local matching close、accepted syntaxがすでに開いたordinary mandatory right-hand sideには適用しない。
`IfExpression` condition、`forall`のbounded phase、`BR-H`/`BR-A`は、列挙されたmandatory-phase exceptionである。

| Construct family | 参加する境界 |
| --- | --- |
| Operator chainとfixed tail | tail、ML argument、terminal tailをattachする前のcontinuation gap。 |
| Expression-delimited form | parenthesized、call、index、projection formのcompleteまたはrecovered item gap。 |
| If expression | conditionの列挙されたmandatory-phase judge point。 |
| Pattern | Pattern continuation gap、およびparenthesized、list、record patternのcompleteまたはrecovered gap。 |
| StructとNamedRecord type field | field continuation、retry、inter-field gap。 |
| TypeExpression | path、call、application、arrow、malformed continuation、delimited type item gap。 |
| Polymorphic variantとbracket row | completeまたはrecovered tag、payload、continuation、または指定したbounded phaseのgap。 |
| `forall`とinline colon argument | 指定したbounded phase transition、または最初のargument後のcolon argument decision。 |

## 参加するgapの優先順位

local closeとexplicit separatorが先に勝つ。
次にASOBがstrict dedentまたはvisibleな`else`/`elsif` companionを取る。
どちらもない場合だけ、constructは通常のlocal continuation、layout、recovery ruleを使う。

ASOBがgapを取る場合、gapはambient ownerのために未消費のまま残る。
local implicit boundaryをすでにcommitしている場合、その1個のnext slotはlocalのままである。
ASOBは後のgapだけに適用する。

## 参加しない境界

ASOBは次の境界をclaimしない。

- missing inner close後のordinary same-indent statement candidate。
- current brace depthのbraced statement-owner boundary。
- caseまたはcatch arm-sequence boundary。
- `IfExpression` companion以外のcontextual stop。missing nested delimiterの後にあるarm `if`、`where`、`->`、binding `=`を含む。

これらはASOBの対象外である。
ownershipは各construct pageと既存のrecovery contractに従う。

## 関連する規則

local complete-item newlineの分類には[layout-aware separator authority](layout-aware-separator-authority.md)を使う。
malformed TypeExpression newlineの所有権には[TMN](tmn-malformed-newline-owner-policy.md)を使う。
ASOBが決めるのは、二つのambient statement-context claimが参加するlocal gapに先行するかだけである。

正本は、[syntax architecture design](../../../notes/design/2026-08-20-yu-syntax-chasa-architecture.md)のAuthoritativeなASOB addendum（18358–19160行）である。
