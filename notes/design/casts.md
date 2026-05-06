# Cast Declarations

`cast(x: A): B = body` declares an implicit conversion rule from `A` to `B`.
It does not introduce a user-facing cast expression.

Cast rules are used at expected-type boundaries.  The compiler first records the
ordinary expected edge, then inserts an internal `.cast` call only when
`Cast A { type to = B }` resolves to exactly one implementation.

Important boundaries:

- no matching `Cast` impl: keep the ordinary subtype check and report that no
  implicit cast exists
- multiple matching `Cast` impls: report an ambiguous implicit cast
- same source and target type: do not require or insert a `Cast` impl

The long-term goal is for user-defined casts to share the same coercion
insertion path as built-in representation coercions such as `int <: float`.
Until that path is fully unified, new cast insertion sites should be wired
through expected-edge evidence rather than path-specific or syntax-specific
special cases.
