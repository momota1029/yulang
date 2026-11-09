# Directed scalar-bound closure (Draft)

The previous reciprocal-edge engine misses directed chains. Use facts `(upper?, slot, base)` over a complete `8*n` universe. Upper bounds move backwards along `i ≤ j`; lower bounds move forwards. Seeds are actual scalar bound atoms. An independent inductive derivation has seed/transfer constructors. Finite Horn saturation is exact for that derivation; each derived bound is sound in every input model. Emitting these bounds preserves all models. Pairing lower and upper yields scalar equality without requiring reciprocal edges. This is a scalar-bound fragment, not arbitrary semantic entailment, structural types, or role feedback termination.

## Outer interface
For every n, state s, slot i and input model a, materializing int after directed normalization is equivalent to independently deriving both upper and lower int bounds for i. For every registry, source root and candidate table, re-normalization preserves the entire ordered diagnostic tree under the same model assumption. This does not prove a role-generation fixed point.

The regression is int ≤ x ≤ y ≤ z ≤ int. No scalar pair is initially present; hence the reciprocal-pair engine cannot start. The directed upper and lower derivations meet at y. Source syntax lowering is not asserted by this ordinary-atom example.
