# INIT_WORLD: closed-import factor and current Rust seam

Date: 2026-10-09
Baseline: `1efde444c548f9f293c69775eecc0811dacfb6a7` on `research/simple-sub-intrusion`
Status: bounded conditional derivation, adversarial shortcuts, and source-to-code map; review pending
Authority: none; `INIT_WORLD` remains OPEN-SEMANTIC
Scope: PCINIT initial schema, fixed-support external import factors, and the current syntax/HIR/solver path

## Result

PCINIT supplies an open source schema, receipt, and conditional entry
construction. It does not supply initial-world validity, a semantic import
rule, or proof that a satisfying initial world exists. For an independently
typed external factor whose entire semantic support and original incidences
are fixed by every legal filling, its existing certificate is invariant under
filling. This leaves the joint root-extension obligation intact; separate
closed certificates for the old environment and individual roots do not
establish that the imported and newly formed roots coexist in one original
`(C0, xi)`.

The current production path parses import syntax but does not admit semantic
imports into HIR or F5. This matches the existing authoritative first HIR
slice, which expressly selects empty semantic imports and excludes import
graphs. Full INIT_WORLD support therefore needs a distinct source/world owner
and a later production gate; this mapping does not broaden that first slice.

## Conditional fixed-support result

Fix the original binder tree, `X`, `xi=(nu,K,D)`, configuration `C0`, and a
supplied independently typed external base certificate `E_B`. The following
premises are required:

1. Every provider, descriptor, reference/state identity, activation, owner
   witness, and semantic dependency used by `E_B` is independent of the open
   source holes `H_f,H_a`.
2. Each legal filling fixes that entire support, including its original
   incidences. A closed printed type alone does not establish this.
3. Imports use their supplied original certificates; aliases retain registered
   provider identities. No premise is obtained from checked-hole membership
   or pending-query success.
4. The other PCINIT obligations remain explicit: descriptor/profile meaning,
   argument-carrier contract, distinguished port, and ordered suffix.

Under these premises, substitution changes none of the free semantic
dependencies of `E_B`, so its existing interpretation is filling-invariant.
Conjoining that unchanged factor with PCINIT's punctured source schema yields
an obligation schema, not `INIT_WORLD` closure:

```text
E_B + OpenSourceGraph + OriginalProfilePositions
   + ArgumentCodeContract + OriginalPortAndSuffix
   + [joint import/current-world extension]
```

The bracketed obligation cannot be discharged by conjunction formation. The
smallest remaining world rule is a noncircular zero-step root-extension
introduction at the original importer/source incidence, with a restriction
equation recovering the old tuple. It must preserve old incidences and
reconcile shared provider/reference/state identities, activation, and live
ownership at the same `C0,xi`, while leaving holes open. It must not assume
checked-hole membership or validity of the extended world.

For a hole-dependent external import, the fixed-support proof stops earlier:
an authentic import-owner action on its original hole/rigid incidences and
dependent witnesses is missing. Pointwise valid closed fillings do not supply
that action. Independently valid roots also do not imply one jointly valid
environment or an inhabited initial world.

## Adversarial shortcut tests

These are conditional logical discriminators, not constructed Yulang worlds
or source-rejection claims.

| Shortcut | Minimized failure shape | Existing boundary that keeps the premise open |
|---|---|---|
| Treat every imported factor as filling-independent | One imported root has incidences `(H_f,k)` with rigid `k=a`. If two fillings are independently legal and send `H_f` to `a` and `b` (`a != b`), collapsing both reference obligations to one input atom `a` makes an identity-only transport require both `t(a)=a` and `t(a)=b`. | The initial-context construction explicitly requires an open-substitution certificate for a genuinely hole-dependent external value. |
| Admit a hole-dependent imported alias through checked membership | Installation asks for `DescMem(T_checked,f)` to admit the very alias whose acceptance is under check. If `f` can emit a request excluded by `T_checked`, that test can remove its challenge before observation comparison. | Existing initial/world clauses keep independent open-import/provider evidence and zero-step joint extension separate from checked membership. |
| Infer initial-world inhabitation from a puncture or receipt | The open schema can be formed while an independent world/import conjunct has no witness. `Gen(B^H)` and receipt formation therefore do not imply `exists X. Init(X)`. | PCINIT states validity and inhabitedness do not follow; the source/profile constructions require a satisfying whole tuple. |

The first shape needs two independently legal fillings to instantiate its
conditional contradiction. The second needs an independently justified
hole-dependent alias before it can be a source-level instance. Neither shape
proves that accepted Yulang source is rejected.

## Current Rust correspondence

| Layer | Current owner and result | Boundary |
|---|---|---|
| Syntax | `yu-syntax` discovers and parses `UseDeclaration`, `UseTree`, aliases, visibility, and unresolved import routes into `HeaderImport`. | Production syntax only; no resolved value/provider or semantic world is stored. Imported operator provenance is syntax capability data, not semantic import admission. |
| HIR input | `SemanticImports` in `yu-hir/src/module.rs` is unit-backed with only `empty()`. `lower_module` accepts `_imports`; `lower_module_with_counters` builds a local namespace. | Production lowering has no caller JointWF/environment evidence. |
| HIR item admission | `plan_root` accepts operator chains and supported bindings; `UseDeclaration` reaches `UnsupportedItem`. | Its alias does not enter local name resolution. |
| Solver / types | F5 collects local definitions and local uses, finalizes local closed schemes, then routes incoming SCC uses by Q/R row freshening. | This is local scheme use, not external provider/world admission or a whole-root import action. |
| Shadow evidence | HIR/solver shadow paths retain unresolved initial-provider/world or module-name premises behind default-off gates. | They inventory missing obligations; they do not prove source acceptance or construct INIT_WORLD. |

This is a bounded current-path map, not a repository-wide absence theorem.
The 2026-09-19 HIR simple-module-resolution first slice is Authoritative for its
stated empty-import boundary; this work does not change it.

## Review and next gate

Four independent methods contributed: owner/authority mapping, a conditional
construction, adversarial shortcut analysis, and a current-source code map.
No actionable conclusion promotes the gate. Independent compiler-referee and
spec-auditor review is pending for the integrated claim and authority boundary.

The smallest next evidence is a clause-level zero-step introduction and old-
tuple restriction derivation, exercised on (a) one scalar cross-world install,
(b) one source-open alias, and (c) one hole-dependent external import with a
rigid/hole overlap. Require a single jointly scoped tuple and explicit witness
transport; do not infer it from traces, fresh IDs, or the closed-support
lemma. Keep `INIT_WORLD` OPEN-SEMANTIC until this owner rule and its genuine
world evidence exist.

No new semantic rule, API, import envelope, test contract, production code,
test, build, or measurement is introduced. The user-approved root-policy
direction changes no import admission rule and grants no implementation
authority. The separate pending expression-annotation design question is
unrelated to this import/world gate.
