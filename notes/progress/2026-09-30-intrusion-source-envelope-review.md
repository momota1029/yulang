# Intrusion source-envelope review

Date: 2026-09-30
Scope: candidate first theorem graph class and its relationship to Oracle source fixtures
Status: characterization only; no implementation authority

## Review result

The first draft's proposed fixture-complete `S₁` was too broad. The named
Function source fixtures carry latent effect identities, and the Oracle probe
shows forced effect identities can be independently freshened at incoming
uses. The captured-diamond fixture also requires tuple and record subtype
closure, whose arity, field, optionality, and mismatch rules were not present in
the candidate closure relation. The nominal-guarded SCC additionally needs a
defined guardedness predicate and interval interpretation before it can be
claimed by a theorem.

The abstract-semantics draft §1 now marks the narrow effect-free polarized
Function graph as graph-level only. The Oracle source programs are explicitly
characterization fixtures outside that theorem; no source-level parity is
claimed from them. Product, nominal, latent-effect, and guarded-recursion rules
remain required semantic extensions before the theorem can include those
fixtures. The choice between proving this narrow graph fragment first and
expanding the theorem remains open.

Current Yulang3 HIR also has no expression-application node and rejects the
identity fixture's lambda/application route. This is a source-to-Rust lowering
gap in addition to the missing semantic rules. Until resolved, graph-level
results and source-level Oracle parity must be reported separately.

## Review provenance and limits

An independent compiler-referee review identified the effect, product-closure,
and guarded-recursion scope gaps. A spec-auditor review found the candidate
wording compatible with the charter's Gate C and confirmed the HIR caveat.
Delta review closed the effect/product overclaims, then found and closed the
missing guardedness/recursive-interval prerequisites and the nominal-rule
scope ambiguity. This narrowing only identifies a possible effect-free graph
lemma; it does not narrow the user's full Oracle-capability objective or
establish the final supported envelope. The next design pass must include the
observed latent-effect, product, nominal-recursion, use, and diagnostic behavior
needed by the chosen end-to-end envelope. No compiler code changed and no tests
or measurements were run.

Sources: `notes/design/2026-09-29-intrusion-abstract-semantics-draft.md` §1;
`notes/design/2026-09-29-scc-intrusion-redesign-charter.md` §§3–4;
`notes/progress/2026-09-29-intrusion-oracle-ledger.md`;
`notes/progress/2026-09-30-intrusion-bounded-negative-counterexample.md`;
`notes/progress/2026-09-29-intrusion-rust-replacement-map.md` § “Oracle source
witness is outside current Yulang3 HIR”.
