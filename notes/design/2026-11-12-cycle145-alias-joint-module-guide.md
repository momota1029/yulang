# Cycle145: one common Joint witness per registered alias class

Goal: reduce the dictionary `evidenceNode` residual without changing the target.
A `Joint` proof contains one model satisfying every site in an alias class. It
can therefore be rerooted at any registered member of that class, retaining the
same model, rather than reproving independent existential witnesses per site.
No claim is made that local survivor witnesses at distinct aliases can be joined.
The same registered-site premise is used in the reverse direction for an iff.

The actual output-equation merge transport is investigated separately; it must
retain one simultaneous model and may not silently combine two existential
models. All results are helper/soundness-side results, not full V5 completion.
