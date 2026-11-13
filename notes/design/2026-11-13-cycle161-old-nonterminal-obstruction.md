# Cycle 161: exact old nonterminal Evidence obstruction

An attempted old-and-current full Evidence conjunction for the unchanged
certified fixture is impossible. `GeneralDictionaryNonterminalOldObstruction`
proves the obstruction rather than adding an old Evidence assumption.

The old parent report captures `(7,3,4)` and `(7,4,4)`. Its actual canonical
singleton where child uses the resulting private merged lower/upper IDs.
`child_unlocated` proves that argument location in the old source returns
`none`. These generated IDs are not old source slots.

Consequently:

- For every assignment, key and child list, the actual old child has no Instance.
- For every assignment and payload, it has no Evidence.
- For every assignment and payload, the old parent root has no Evidence.
  The last proof eliminates the two visible declarations: the terminal leaf
  has the wrong role, and the parent must include its actual unlocated child.
- `old_absent_current_present` combines absence for every old parent payload
  in the fixed model with the existing full current Evidence
  `node 31 [node 32 []]` at the exact certified reached context.

This is not a counterexample to conditional forward Evidence transport:
there is no old Evidence antecedent. It also does not contradict old parent
BranchModels, which describes candidate-private semantic checks rather than
located recursive child Evidence. The current positive fixture therefore
establishes evidence availability after the certified revision, not preservation
of a previously available full nonterminal dictionary.

No source, state, step, candidate, or prior fixture was changed. Making old
recursive Evidence available would require a separately justified source that
contains the generated child endpoints, not merely their private interpretation.

Verification: direct Lean 4.35.0 `--trust=0` module check and all 7 public theorem
axiom checks pass, exit 0, no warnings. Only `propext`, `Classical.choice`, and
`Quot.sound`; no full build or CLI claim.
