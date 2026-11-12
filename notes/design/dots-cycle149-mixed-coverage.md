# Mixed journal / structural leaf coverage

Pure packet coverage was too strict: a real stable successful recursive fixture
has an unrecorded selected scalar leaf. The mixed condition instead permits an
actual recorded packet with ordinary context extension OR a syntactic linear
nominal leaf OR a syntactic scalar leaf. The leaf alternatives contain no
BranchModels, Instance, Evidence, Joint or successful-key premise.

For every source-formed state, every current model and finite classified
selected dictionary, coverage for the actually generated selected nodes yields
Evidence in that same model. Keys and children are identified using current
uniqueness. Historical nodes obtain generated children from recorded edges;
structural leaves first prove that the selected child list is empty.

The existing recursive Display(List Int) fixture tests the combination: its
parent is recorded, its Int leaf is unrecorded, and the theorem reconstructs
Evidence for the current classified dictionary in every final journal model.
This does not prove mixed coverage for all reachable stable programs, general
V5, or executor termination.

## Final finite-spine variant

`GeneralDictionarySpineCoverage` replaces the linear one-level leaf alternative
by `HasSpineLeaf`: an actual finite chain of recorded unary point wrappers and
an arbitrary-arity interval-valued linear nominal leaf. The depth is structural
and unbounded, not a numeric cutoff. `of_mixed` preserves previous certificates;
`recursive_fixture` applies the final dictionary theorem to the actual success.
Branching nested heads, nonpoint wrapper arguments, repeated innermost binders,
row parameters and nonterminal unrecorded nodes are not covered by this leaf rule.
