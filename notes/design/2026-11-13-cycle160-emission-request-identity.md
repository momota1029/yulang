# Emitted request identity under input-capture changes

Prove only the declaration-emitter boundary: equal output capture functions and
identical allocation imply identical materialization requests, although input
capture functions can differ. Variable input requests are omitted; nonvariable
input requests use fixed allocated endpoints. Output targets use output captures
or fixed allocation. This is not equality of child demands or child Evidence.
Lower/upper request modes remain present for nonvariable inputs. Structural
variable descendants retain those modes; nominal descendants reset to actual.
Consequently request identity alone does not discharge endpoint semantics.
