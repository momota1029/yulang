# Cycle248 actual raw-state model transport

Use the already existing GeneralNominalRebaseRawView243.compile and its exact
model theorem; do not introduce a parallel synthetic state. With the ordered
mapping, RawView.read is literally Ordered.solve. Old-block model recovery
makes solve old assignment globally type-equivalent with exact rows, and the
existing RawCongruence238 theorem preserves the actual nominal State.Models.
Thus the compiled full raw view under the new private solution is equivalent
to the old raw state's model predicate. This includes source slot expressions,
heads, ordinary atoms, nominal descriptors/parameters and base constraints
that compile_exact already covers; no name is hidden merely because private.

Proposed outer theorem: for any actual raw State, arbitrary consumer atoms,
old/fresh SafeOrder and fresh targets contained in old, the existence of one
assignment satisfying raw State.Models, consumers+old block and fixed public
coordinates equals existence of one assignment satisfying compiled View.Models,
rewritten consumers+fresh block and the same public coordinates. All requirements
use a single witness. This is representation transport only, not construction
of a successor operational state or coverage of separate history/cache fields.
