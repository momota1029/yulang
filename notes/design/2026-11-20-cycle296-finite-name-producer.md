# Cycle 296: witness from finite source-name observations

C295 checks a finite trace against a supplied total function. It does not
distinguish an explicitly observed failed lookup from a key not observed
at all. For the selected wrapped CST fragment only, use a finite catalog
of typed query/reply observations. Role names, role-local output names,
and nullary constructor names remain distinct query variants. The caller
supplies all semantic ID observations; offsets and CST spelling alone must
never mint IDs.

Categorize a requested key by its full catalog fiber: no row (unobserved),
exactly one row (whose value is either present ID or observed absence), or
multiple rows (ambiguous, even if replies repeat). Do not replace missing or
ambiguous evidence by a successful absence. A temporary projected
environment can compute the existing C295 query shape, but require every
branch actually queried to have one row before releasing its trace.

Prove (1) producer success iff the exact C295 capture has complete unique
support, (2) every total environment consistent with that local support has
the same capture and lowering on this selected symbolic role, and (3) a
finite checked handoff can use that computed evidence without receiving
a total caller Environment. This is finite evidence consistency and scoped
replay, not completeness/authentication of the catalog or Rust name
resolution. Use a real archived method-only role and independently labeled
synthetic associated declarations, including unobserved and ambiguous cases.

A second, independently checkable producer can read the old *lowered*
row together with its selected symbolic role and recover the demanded
finite name evidence. Zip outputs in source order, distinguish required
absence, validate a binder's actual positional index, and read a nullary
constructor ID only from a zero-argument term. A witnessed C292 lowering
must yield the original finite capture. The reverse is a structural
consistency check, not authentication of a handed-in row; inconsistent
multiple replies must not produce a map. Identical repeats from a
capture (e.g. two uses of one constructor) can be coalesced only in this
explicit inversion, not in the raw catalog interface.

The selected one-row old table can now be inverted while retaining the
same sealed handoff. The recovered catalog contains precisely the
literal entries queried by that successful output. Re-running from
the shortened, coalesced catalog gives the identical trace and table.
Among catalogs that produce the same selected resolved row, the
occurrence trace is determined even if unused observations differ.

For test transport only, use a versioned JSON array of rows, not a
JSON object keyed by spelling: an object could erase duplicate evidence.
Each row must decode in place, preserve its typed domain, and distinguish
explicit null (observed absence) from an omitted row. The entry must
reject malformed evidence before invoking the existing selected adapter.
No Rust receipt schema is changed or adopted.

A final optional issued catalog can bind the exact selected wire,
address, scope/policy, and an independently named semantic environment
revision. Issue only after the finite producer succeeds and release
only its trimmed supported observations. A different revision must
decline even if source bytes coincide. Reuse still runs the current
selection/diagnostic gate; this is a value-equality contract, not a
signature, expiry mechanism, or authentication of self-asserted fields.

Observed absence is proper evidence, not necessarily a successful
export. In the existing selected fragment, any name actually demanded
by a successful old lowering must have an ID. This is separate from
an associated type slot that is required but has **no default term**:
that slot's name is still resolved. Preserve this distinction in the
producer proof and controls.
