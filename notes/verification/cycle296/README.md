# Finite selected naming evidence, cycle 296

The adapter consumes typed finite observations, not an oracle function or
the current Rust compiler's name environment. The archived Rust golden
contains role `a` with a method and no associated types. The separately
supplied [test observation](archived-a-observation.json) assigns `a → 7`
for this verification. That ID is not read from the archived Rust tree.

## Rebuild and replay

From the repository root, with Lean 4.35.0 and its pre-cycle dependencies:

```sh
bash notes/verification/cycle296/verify-focused.sh
```

The optional arguments select the C295 base ref (or its identical local
tree) and prior OLean directory. The script excludes all C296 objects from
its own shadow cache and uses one Lean thread; avoid building the whole
Lake target or running other heavy verification in parallel. Audits
print all 93 theorem declarations. It reconstructs the archived JSON
from the checked-in Rust test, independently replays three actual archived
and two synthetic Lean programs, and compares their logs byte-for-byte.

## Test evidence codec

An example for two role-local outputs:

```json
["yulang-name-evidence-v1", [
  [["role", "Index"], 2],
  [["output", 2, "value"], 0],
  [["constructor", "char"], 3],
  [["role", "unknown"], null]
]]
```

The last row is a known absence, not an unobserved role. Rows use
arrays so repeated evidence is not dropped. Repeating the same demanded
typed key is ambiguous even if the raw replies agree. Unrelated
observations are not touched. The version and array shape are checked
before delegation; IDs are accepted only in the exact nonnegative
integer JSON-value form. This is a **Lean test schema**, not a change to
the Rust API or a trusted authentication envelope.

## Intentional limits

An arbitrary catalog's entries are caller data. The materialized table
does not recover IDs from raw CST offsets, nor infer a key that is absent.
The structural reverse direction is exact for a matched symbolic role and
its actual old lowered row. If a different made-up table is structurally
consistent, its inferred numeric decisions may differ. A successful
checked round trip does not establish which of those tables is authoritative.

An issued packet keeps exact source wire and selected address, scope,
policy, separately provided environment revision, and fallback arity.
It coalesces only matched successful observations and does not redact the
full retained wire. A fresh recovery receipt is still required when
replaying. Matching a revision label or other field is not authentication.
A closed executable control reuses exactly the same archived wire and revision
label with the separately supplied IDs 7 and 8. Each verifies when alone;
only the combined inconsistent catalog detects ambiguity.

The current Rust release was **not** run in this cycle. A future authorized
Rust environment must capture both the actual retained parse with fallible
diagnostics and the independently trustworthy finite naming decisions,
including their revision and selection. Without both, these tests remain a
verified bridge for supplied observations, not a production resolver.
