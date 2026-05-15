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

## Cache-tracked ambient casts

Cast lookup is ambient, but it must be cache-tracked.

The current direction is not to require every user-visible cast to be imported
explicitly before it can affect inference.  Instead, an inference session may
consult the currently available cast environment when it needs cast knowledge:

- expected-edge cast insertion;
- cast ambiguity checks;
- role-method selection paths that ask whether a cast can overlap a type.

The important invariant is that these lookups go through one dependency-recording
entrypoint.  Direct reads of the cast candidate table should be avoided in
inference code.  If a file-SCC inference result depends on cast information, the
compiled-unit cache records the cast environment fingerprint that was actually
consulted.

Conceptually:

```text
infer file SCC
  -> query_cast_environment(...)
       -> record used cast fingerprint
       -> answer lookup
  -> cache artifact records used cast fingerprints
```

On a later build, the artifact is valid only if the recorded cast fingerprints
still match.  This lets files that never consult casts keep their cache even
when unrelated casts change, while files that do consult casts are invalidated
conservatively.

Early implementation can use one coarse fingerprint for the visible/global cast
registry.  If this becomes too broad, it can be refined to per-realm,
per-module, or per-cast-group fingerprints without changing the inference rule.

This makes cast availability behave like a tracked ambient capability:

- casts can be seen broadly enough for ergonomic implicit conversion;
- cache invalidation remains local to file SCCs that actually used cast lookup;
- std can have its own compiled-unit artifact keyed by the cast environment it
  consulted;
- future inference or display passes only become cast-dependent when they ask
  whether a visible cast overlaps a type.

Named cast groups may still be added later as a user-facing import-control
feature.  Anonymous casts can be treated as belonging to a default `cast` group.
That grouping is useful for visibility and diagnostics, but cache correctness
does not rely on it: the cache relies on the recorded lookup fingerprints.
