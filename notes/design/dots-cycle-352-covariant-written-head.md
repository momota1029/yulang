# C352: actual written covariant head

The authoritative roles spec section 6.3 (I-63 source at `318375bb5f6ffd9c46766613b75b86d7823feab0`) approves same-tag merge of declared covariant box values to one box with the whole union, with every binder seeing that whole. C352 checked the concrete pattern written as two same-tag box arms, not just a caller-provided already merged shape.

The existing basic normalizer only merges the tag and retains a join of two boxes. The isolated checker verifies the actual basic-normalizer form, matches the exact tagged nominal identity and declared variance, builds one nested payload pattern, and checks both actual source arm indices in the same signature. The witness returns both binder positions with the same entire joined value; splitting, changing constructor identity or pretending the signature is invariant fail.

This is the narrow unary case with the two distinct source-arm patterns; it is not the full declaration-aware expression carrier or automatic same-state forest integration. It does not alter existing normalizer, candidate priority, or language acceptance. At the next stage connect the authorized declaration table to a typed source-backed expression representation and verify its actual current read, output and ordered compiler; do not enable the invariant flag as a proxy.
