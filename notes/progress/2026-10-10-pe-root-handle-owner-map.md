# Native PE root handles: current owner map

Date: 2026-10-10
Baseline: `a6df6cdc0abeee2a7827bb6aacd8b7bcd586a200`
Status: bounded read-only correspondence map; no implementation authority
Scope: source/use identities, native `new`/alias frames and ordinary PE roots
Production inference / F5 cutover: none

## Result

Current default HIR and solver provide artifact-local source/use handles, but
they do not retain the semantic distinction needed by native Generalize between
an independent `Instance(p,i,r)` and `Alias(h,r)`. No current field connects an
actual source-use handle to a whole public frame, its ViewLogic/EventProof
allocation, or an ordinary public root. Therefore an existing HIR or Q/R ID
cannot be treated as the selected `new` or root identity by itself.

The checker proposal already gives a plausible internal root representation:
dense slots inside an immutable validated environment, with an environment
identity/generation bound to certificates. Direct q1/d1 adopted that proposal
as an architecture direction, not as an implementation or root-producer
approval. A compiler-owned slot can represent the selected identity contract if
the producer validates the actual new/alias frame map and installs its complete
ordinary record. This correspondence is unproved and remains gated.

## Current handles and their limits

| Handle | Owner and lifetime | What it identifies | Missing PE fact |
|---|---|---|---|
| `SourceNodeKey` | `yu-syntax/src/full_parse.rs:72,86,113,340`; parse-branded and backed by retained green allocation | One exact CST node in one immutable parse; reparsing creates a distinct brand | Not the semantic independent-instantiation event or alias map |
| `HirOccurrenceId` | `yu-hir/src/module.rs:176,333,355,975`; artifact pointer plus checked ordinal | One lowered expression occurrence in one HIR artifact | Not a whole frame, ViewLogic region or public root; lowering another artifact changes it |
| `DefinitionRootId` | `yu-hir/src/module.rs:185,211,807` | One admitted definition/public scheme owner in its HIR artifact | Not an incoming fresh use root |
| `DefinitionUseId` | `yu-solver/src/lib.rs:534,563,867,1216`; collection-branded, paired with full HIR occurrence | One collected dependency/routing occurrence in one batch | Not typed as `Instance` versus `Alias`; not retained as a decoded public-root identity |
| Q/R ordinal | F5 route in `yu-solver/src/lib.rs:14795` and substitution helpers | One quantifier/recursive binder occurrence in one closed scheme instantiation | Not the semantic frame key or public root; multiple binders belong to one use frame |

HIR equality deliberately does not collapse occurrence identities. Lowering a
parameterized binding creates a Lambda occurrence and a separate body
occurrence. Collection rejects duplicate exact use IDs and foreign collection
IDs. SCC graph condensation can merge equal parent/target arcs while retaining
each occurrence payload. These safeguards establish local provenance and
routing, not the selected native instantiation semantics.

## Selected owner and consumer duties

Native source Generalize §3.3–3.4 and §5.2 assigns the semantic distinction at
the owning source rule. `new` opens one whole component frame before assignments
or histories; aliases route to the antecedent frame. Eligible declarations,
ViewLogic, Shared, actual EventField and per-frame EventProof retain their
different owners and scopes. The constructor keys are source-level incidence
keys such as `(i,q)` and `(i,q,original-region-path)`, not numeric F5 ordinals.

Selected PE §4.2 then requires one fresh ordinary root `u_i` for each actual
`new`, installs all seven active equation entries after one whole frame action,
and makes an alias return exactly the same root/frame. PE §6.1 requires Direct
to read the actual submitted ordinary roots and reject a different/stale root.
The root is distinct in responsibility from the source final root. No selected
clause equates `u_i` with a `DefinitionUseId`, a Q/R row or the source root.

The checker plan §3 proposes an immutable environment with dense root slots,
an environment identity/generation and certificates borrowing the exact root
slots. It rejects caller-chosen F5 IDs. Under that direction, the natural owner
split is:

1. Source formation supplies a typed, validated `Instance`/`Alias` frame map
   with complete scopes, dependencies and final-root incidence.
2. The public-root producer assigns one environment-local slot per validated
   real new, routes aliases to the originating slot, and installs the complete
   PE equations and typed scope/evidence records.
3. Environment preparation validates/seals the entire package before Direct
   queries; the checker only reads exact roots and binds certificates to that
   environment generation.

This is a candidate ownership map within the approved architecture direction,
not an approved concrete API or implementation.

## Required correspondence laws and falsifiers

Before implementation, a reviewed producer contract must show:

- distinct real-new frames map injectively to distinct root slots even when
  endpoint terms and displayed types agree;
- every alias resolves to its antecedent's same root, frame and eligible
  witnesses, with no second allocation;
- root lookup is total for admitted references and reads the installed public
  record, never the source body or F5 endpoint;
- one whole frame action changes exactly eligible fields and incidences while
  preserving fixed imports, Omega, Shared and actual-event fields;
- certificates bind to the exact environment identity and root slots; stale or
  foreign identities fail atomically;
- environment storage rebuild invalidates old certificates without turning an
  alias into a new semantic frame or freshening a fixed monomorphic capture;
- duplicate/dangling handles, slot overflow and partial root-package
  construction have explicit validation/failure behavior.

The following tempting equalities are unsupported: `DefinitionUseId = i`,
`Q/R ordinal = frame declaration`, root slot = source root, or equal endpoint /
scheme = equal public root. Conversely, source/use IDs may be retained as typed
provenance inputs if an owning constructor proves their mapping to frame
incidence. Their existence alone does not prove that mapping.

## Exact remaining work

The current `DefinitionUse` route records a collection occurrence and target
root/use component. Same-SCC edges route monomorphically into an existing
component; cross-SCC edges instantiate a closed Q/R scheme into that already
collected use component. Substitution rows are memoized per ordinal and scratch
is cleared after routing. `SolvedModule` retains HIR, closed schemes and route
provenance, but not the PE whole-frame action or ordinary-root environment.
This lifecycle cannot serve as the missing supplier without a reviewed bridge
that constructs and retains the selected native records at their owning rule.

Thus the next gate is not another search for a unique numeric ID. It is the
typed source-owner output that distinguishes `Instance` from `Alias`, followed
by its validated dense-slot publication and exact Direct caller. Numeric work,
buffer and peak-byte limits also remain unset because the successor caller and
its complete root/query attempt schedule are not yet selected. The user-approved
flat-arena direction alone authorizes neither implementation nor F5 routing.

## Evidence and frozen inputs

This is a bounded report based on the current default-code paths and selected
design clauses, not an independent proof or repository-wide absence theorem.
No code was changed; no tests/builds/measurements ran.

```text
24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8  crates/yu-syntax/src/full_parse.rs
3bb488f9d9e13b43e79e472a65a35197ae4f2c76ae21a6f0f8f77195661f4363  crates/yu-hir/src/module.rs
236f4f433ef775df0d88294f046e11dd34c1816da2fa99d7f0d403b39c2ed4a2  crates/yu-solver/src/lib.rs
3cfce9acfddd77838398cd95cd13c053f71f27a8367b07175a83c825d68a8df8  crates/yu-solver/src/scc.rs
e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240  notes/theory/2026-10-08-source-generalize-definition-and-proof.md
4cf84e7a38153b893f1d339780598e2b79084c747ecb883acf0e4fdaa49cf631  notes/theory/2026-10-08-projection-public-export-construction.md
1947eff96d4450f33f446988e75f5d818bf5d75b641bdbfbfbb0d0dc2e6aae60  notes/design/2026-10-08-native-direct-consumer-plan.md
```

Approvals consumed: `native-direct-consumer-architecture/q1` selected the
flat-arena direction only (`questions/2026-10-08-native-direct-consumer/receipt.md`);
`successor-generalize-root-policy/q1` selected a transformed public target
direction only (`questions/2026-10-08-successor-generalize-root-policy/receipt.md`).
Neither approves this concrete owner/slot implementation.
