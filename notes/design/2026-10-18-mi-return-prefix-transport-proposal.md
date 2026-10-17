# Return-prefix transport audit: configuration is not a source package

Date: 2026-10-18
Sprint: `mi-return-prefix-total-transport-20261018`, revision 2
Contract SHA-256: `200fc4362e532cfe1ffe4887fe01ae904c0c19211b919c499b3b1049523244e4`
Baseline: `ab8344e4b`
Status: **source/package audit; no complete transport or adoption**
Original/local/fixed-family conditions closed: **0/0/0**

## 1. Question and bounded answer

The fixed question is whether each actual original unfinished, zero-step, or
administrative Return prefix at `site_f` already has a whole typed package that
can be mapped into the new MI Prefix fiber and erased back without losing any
field, arm, guard, dependency, owner, or hidden witness.

The pinned original owner, `notes/theory/2026-10-08-call-semantic-input-realization.md`
§4.2, states that such a prefix retains the same current world, environment,
and original code incidences, with no asserted result, and includes zero-step.
It does not declare a prefix judgment's constructor or the types, order,
dependencies, or projections of those three retained incidences. It says that
an unfinished administrative prefix retains the same jointly valid fields;
it does not enumerate those fields as an eliminable typed telescope. Therefore
the exact source owner provides a semantic retention clause but not an
inspectable typed package interface from which the requested maps can be
constructed.

The added ordinary-computation Draft gives a candidate machine configuration
`C = (expression, lexical environment, live store, ordered activations,
value-carried runtime lineage)` and a source execution relation over
`Return(v,C)`/`Request(q,C,k)` with finite prefixes. It does not define a map
from the older §4.2 original prefix evidence to this configuration. In
particular, it gives no typed embedding of the old current World into live
store, no rule identifying old original code incidence with `C.expression`,
no map from the old environment incidence to the Draft lexical environment,
and no source-index theorem connecting either to `ReturnIntroId_MI(id_f)`.
The Draft's expansion law applies to its own derived shallow source form; it is
not an old-prefix transport rule.

Thus the requested total same-index transport is **not derivable from the
pinned owners**. The first obstruction is upstream of individual MI fields:
there is no source-declared typed original prefix package and no typed
projection/map from that package to either an MI prefix or the Draft machine
configuration. The exact missing owner is the §4.2 Return-prefix clause's
formal constructor/type and its world/environment/code incidence telescope.

## 2. Candidate target and the map that would be required

The previous MI proposal defines the candidate target fiber at
`id_f = ReturnIntroId_MI(site_f)` as:

```text
ObserveMI(id_f, Prefix, (C_e, w_e, env_e, code_occ)) :=
  JointWF(C_e,w_e)
  × EnvAt_MI(C_e,w_e,env_e)
  × CodeOccurrence_MI(id_f,C_e)
```

For each old actual prefix package `z` at the fixed original index, a valid
transport would have to provide the typed data below, preserving the actual
same-occurrence incidences rather than just matching syntax labels:

```text
lift_f(z) = (C_e, w_e, env_e, code_occ,
             j_world, j_env, j_code, hidden_z)
```

where `j_world` relates the old current world to `w_e`, `j_env` relates the
old environment to `env_e`, `j_code` establishes that the retained original
code incidence is exactly the `site_f` occurrence under `C_e`, and
`hidden_z` preserves every remaining original constructor field and witness.
The target must inhabit `ObserveMI(id_f,Prefix,...)`. A map

```text
erase_f : ObserveMI(id_f,Prefix,...) -> OriginalPrefixPackage(site_f)
```

must recover the original package, with `erase_f(lift_f(z)) = z` on every
constructor/witness, including zero-step and administrative packages. Neither
`OriginalPrefixPackage(site_f)` nor `j_world`, `j_env`, `j_code`, nor the
round-trip law is declared in the pinned original source. Writing these
signatures exposes the missing inputs; it does not add them as premises or
prove them.

The Draft configuration can be a target for a later bridge only if there are
typed maps from actual original evidence into all relevant configuration
components. The expression, lexical environment, and live store are candidate
locations for data, not proofs of incidence. Ordered activations and
value-carried runtime lineage must also be retained whenever present; their
ordering and identities cannot be reconstructed from a syntax-label or
environment projection.

## 3. Falsifiers checked

The following interpretations are consistent with the displayed owners and
block a total map:

1. The old prefix clause has an admitted zero-step prefix at `site_f`, while
   `CodeOccurrence_MI(id_f,C_e)` has an empty fiber. This is the existing
   empty-fiber counterinterpretation; the old prose does not state a rule that
   fills the new relation.
2. Two old prefixes agree on the printed expression and environment but differ
   in current-world or ordered code-incidence witness. The Draft tuple alone
   does not specify how the corresponding store/environment/code fields encode
   or preserve that distinction, so equality of a projection is not an
   erasure round-trip.
3. The Draft machine relation has a finite prefix of its own source expansion
   but there is no derivation relating that expansion's prefix to the old
   §4.2 prefix constructor. This satisfies the Draft's stated scope without
   supplying the requested old-to-new map.

These are underdetermination models, not evidence that any particular
implementation execution is wrong. They show that field names and the Draft's
own expansion theorem do not entail the bridge.

## 4. Exact next evidence

To continue by construction rather than repeat the same projection exercise,
an owner must supply an explicit original prefix declaration with at least:

```text
PrefixOrig_A(site_f, z) constructor / judgment
  -> current World and its `JointWF` evidence
  -> exact original Environment incidence
  -> ordered original Code incidences with their source-use/index relation
  -> all arm/guard/dependent/hidden fields for unfinished, zero and admin cases
```

and either direct typed maps from these fields to the candidate MI target, or
typed embeddings into the Draft configuration plus a theorem relating that
configuration to `site_f`. It must include a total lift, total erasure and
constructorwise round-trip; no empty-prefix or empty-fiber exception is
allowed. A syntactically typed new relation alone would be a new semantic rule
proposal, not closure of the old relation.

No such owner/type/map is present in the pinned inputs. Sol's packet should
independently challenge this boundary and attempt a constructive lift from the
displayed source, including zero/admin/unfinished and every hidden field. If
Sol also finds no constructor, report this first missing source package rather
than adding a guessed rule. A separate meaning change remains possible under
user authorization, but this audit does not silently adopt one.

## 5. Scope and parent application

- New MI ReturnIntroId formation and abstract products remain as previously
  established candidate structure; completed `ReturnMem_A` reuse remains
  pointwise on its original domain.
- The new MI prefix target remains a schema without source introduction.
- The old `Port_Return`/`Fam_Return`/SIG/license/registry/Code bridges,
  original `q_f`, and §7.2(2) parent application remain open.
- Original/local/fixed-family conditions closed by this audit: **0/0/0**.
- Implementation remains **WAITING**: the candidate source/call files remain
  quarantined; this proposal supplies no safe code slice or test claim.
- No tests or builds were run. Astra assignment/work: **0**.

## 6. Pinned inputs

| Input | SHA-256 |
|---|---|
| Sprint contract rev2 | `200fc4362e532cfe1ffe4887fe01ae904c0c19211b919c499b3b1049523244e4` |
| Original Call semantic input realization | `fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a` |
| Prior MI incidence telescope proposal | `0d1baa9aed2b88b33ce596485008d5e9294873fc4f4dfb8b0f18314063cbb722` |
| Bounded Draft computation semantics | `ee3f5cf8185d516775b8915b0fda6dbb07390c3ecad7ac028eb5995581dff917` |
