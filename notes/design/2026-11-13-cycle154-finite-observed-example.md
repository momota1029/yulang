# Finite nominal output regression

Scope: conditional soundness/auxiliary evidenceNode work, not general V5 completion.
Construct an inhabited ternary nominal source and an actual named output request. The
source certificate must justify all three projection tests. Check that the older binary
certificate cannot describe this query. Connect the actual declaration output request
to generated materialization Models for every source model; do not assume generated
Models. Reachability, stable classification and complete dictionary evidence are separate
obligations unless proved explicitly below.

## Verified refinement

The concrete source has two slots: ternary nominal `N(int,int,int)` at slot 0,
and scalar `int` at slot 1. The sole checked role declaration has scalar input
and a closed ternary named output targeting slot 0. The source model is explicit;
the output is not freshly allocated. Arbitrary source models satisfy all four
materialization tests, hence the real recursive semantic Instance and leaf Evidence.
The initial source is reachable by the empty trace. It is already stable: its
terminal declaration and entailed output schema require no installation. We exclude
all actual feedback updates, including refreshed knowledge for unconstrained source
identities by two distinct scalar assignments. Current support and newest captured-value
boundaries both classify the source as the exact selected leaf dictionary.

This closes this concrete stable non-scalar output fixture, not general evidenceNode.
There is no claim of a nonempty journal, nonzero execution, fresh-output allocation,
general alias coverage, or full-language progress. General V5 remains 8/14 unresolved.
