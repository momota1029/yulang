# Cycle196 rooted support is strictly weaker than global reinspection

`GeneralNominalRootedViewExample196` uses the inhabited descriptor-insertion
contexts from ViewExample196, with a registry containing a variable declaration
900 and unrelated nominal declaration901. Its one-node source tree selects900.
`supported` proves the finite tree has structural
reinspection Support. `not_global` proves registry-wide Rechecks is false: the
nominal declaration’s actual blocked report changes at the given bounds. The
inequality is checked by `decide +kernel`, not native execution or a new axiom.

Thus local support really admits cases excluded by the global hypothesis. This
regression certifies structural support, not semantic evidence for the selected
tree, and it is not an executable-refresh certificate. The separate executable
example supplies that distinct execution result.

Focused build target and strict Audit/Cycle196RootedExample.lean cover both
theorems, printed types/axioms and the allowed-axiom gate.
