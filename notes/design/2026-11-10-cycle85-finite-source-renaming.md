# Finite-support source renaming

Status: Draft proof interface, 2026-11-10. No language-semantics decision.

## Objective and data

Close the cycle84 global-injectivity gap for the existing finite source entry.
Compute support from all source receiver/output names and all input assumption
names. Checking source names alone is unsound: an unrelated seed can collide
with a source receiver and manufacture readiness. Duplicated occurrences of the
same name are permitted. Role/member IDs and Goal binders are never renamed.

## Independent judgment and executable boundary

For arbitrary f : Nat → Nat, source and input, CollisionFree means that any two
names in computed support with equal images are equal. A finite Boolean checker
returns exactly this proposition. A checked rename returns none on collision,
otherwise the unchanged cycle84 renaming functions produce source and input.
None is an unsafe representation change, not a language rejection diagnostic.

## Statements and proof chain

1. Every independent Derives conclusion lies in support.
2. Under CollisionFree, every renamed derivation has an original supported
   witness; for any supported query name, Derives after ↔ Derives before.
3. Under CollisionFree, source Models after ↔ Models before. Existential
   valuations are constructed within the proof, never passed as caller inputs.
4. For arbitrary env/roles/wf/awf/src/input/f, any successful checked rename
   preserves runSource Bool after rechecking, reallocating and resaturating.
   No global injectivity, successful solver, model, package, fuel or state map
   is required. check=true is computed from the concrete source/input.

All statements retain the existing scalar/one-binder finite fragment. This is
soundness/completeness of a representation boundary, not the language's
principal-type theorem. The checker is conservative, not a necessary condition
for two readiness Bools to coincide. Collisions outside computed support are
irrelevant, and the map may be non-injective globally.

## Authority and remaining work

Spec §6.3 supplies associated equalities and conjunctive where siblings. The
work/dots-audit x-oracle C3-PARENT and C3-PARENT-NEG entries were reread. Numeric
identity encoding is a proof-interface concern, not a new Yulang2 behavior.
No new Yulang2 run or parser adequacy claim. Declaration lowering still lacks
preserved grouped source annotations in Roles.Impl.constraints; cycle84's
finding is unchanged. Invocation-sharing questions remain deferred. All five
main B4 bridges remain open. I-13's ledger remains incomplete.
