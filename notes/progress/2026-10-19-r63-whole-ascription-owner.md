# R63 source/native owner audit: whole-ascription crosswalk

Status: `SOURCE-NATIVE EVIDENCE` / `NO_SAFE_CODE_SLICE`. The expanded owners provide an exact structural crosswalk and caller-supplied typed-evidence checks. They do not supply the typed whole-definition-ascription formation judgment or its source/native correspondence. The original parent and A/B remain OPEN 0→0; R50 remains NOT ADOPTED.

## Fixed scope and authority

The inspected source is the fixed `io` / `forward` / `outer` example in the R63 contract. I kept the original provider and carrier, the distinct source positions `p_t`, `p_A`, and `p_R`, local permissions, the joint `K,D`, ordinary generated constraints, correlated results, and typed substitution/transport as obligations. Position names are locators from the pinned theory; no identity was inferred from equal spelling or shape.

The crosswalk/evidence modules are opt-in shadow code: `yu-core` has no default features, and `lib.rs` gates these modules on `feature = "shadow"`. Their comments state that they have no production consumer. Their existence is evidence about the retained source owners, not semantic authority or a production path.

## Source identity and annotation ownership

HIR source identity records admitted definition roots, occurrences, and parameters against exact syntax-node keys. The source annotation parser retains a `SourceAnnotation { owner, position, ty }`; each effect row retains its own source position. Concrete row names resolve through the source effect namespace to a unique `SourceEffectId`. The formal annotation and whole binding annotation therefore have source-owned syntax records. This establishes parsing and identity retention, not a typed-port assignment or permission judgment.

For the fixed direct `t` body, `LocalSourceBuilder` resolves the name through its lexical parameter binding. Candidate source planning routes a `Name` resolved to `Parameter` to that parameter's candidate endpoint. The outer `forward q` is retained as an `Apply`; source resolution and the candidate call machinery own its definition-use route. These native owners do not turn a row's source key into a typed profile or establish the whole ascription's admission rule.

The new HIR inventory traverses only the selected retained definition value and optional cold local initializer. It returns exact retained Apply occurrence/callee/argument identities and attached HIR errors; unsupported projections fail closed. It makes no completeness claim for source calls absent from that retained traversal. The `yu-core` source-annotation crosswalk joins those HIR identities to exact CST positions beneath the selected definition boundary and independently inventories every retained annotation under that boundary, including nested declarations. It returns `calls` and `annotations` as separate fields and expressly does not associate an annotation with an individual call. Its unresolved premise list includes annotation-to-typed-port/profile correspondence, annotation applicability/permission, call typing/admission, call completeness, original `Xi`/types/scopes, semantic witness, and legal whole-tuple substitution.

Thus this crosswalk can establish which retained syntax nodes and call identities are being observed. It does not construct the same-provider typed relation required between the written annotation and the checking/exposed interfaces.

## Typed-evidence owner

`AssumedTypedEvidence::new` accepts a caller-supplied original context, typed ports, profiles, flows, observations, and receipts. It checks context identity, duplicate `(view, position)` nodes, index validity, and then stores the supplied flow graph. The conditional query computes reachability and applies its current-activation filter. The API takes no source annotation or source crosswalk, and its documentation limits it to validating wiring; it does not license source correspondence, source permission, call typing, or an invocation rule.

Two different supplied flow graphs may consequently produce different conditional reachability results while both pass constructor checks. That is a difference between assumed evidence inputs. It is not a pair of source-semantic completions and does not establish semantic underdetermination for the fixed program.

## Native checking and exposed consumers

`candidate_source` builds the root `Action::Annotation` from the source carrier's root annotation, body endpoint, root component, and source occurrence. It separately creates `FormalAnnotation` for the annotated parameter. For a definition annotation, `candidate_effect::candidate_annotation` calls `candidate_annotation_pair`: the constructor builds the negative checking signature and positive exposed signature using shared value/effect-variable and view maps, then admits the body-to-checking slot 40, handles the optional computation-effect slot 42, and admits the exposed-to-root slot 41. The root annotation has no root effect row in this example; its nested argument/result rows enter through Function ports. Constructor order does not establish source formation or solution preservation.

The fixed concrete row at contravariant `p_A` remains rejected by candidate preflight/native signature construction. No guard was removed and this packet does not propose bypassing it. The parameter permission path is separate: `candidate_formal_annotation` retains `FormalPermission` values indexed by the parameter, source owner/scope, occurrence, position path, and row. That parameter-indexed domain cannot stand in for the whole-ascription `p_A` judgment. The positive `p_R` allowance and the correlation between checking/exposed results also remain separate obligations.

The crosswalk is default-off bookkeeping and is not consumed by these native constructors. The current guards and solver behavior do not authorize a new whole-ascription source rule.

## Exact remaining premise and safe code scope

The missing premise is a source formation/typing judgment for this explicit whole-definition ascription, or a derivation of that judgment from already settled decisions. It must identify the resolved original provider and carrier, the typed correspondence for `p_t`, `p_A`, and `p_R`, the applicability and permission of each annotation position, and the relation to checking and exposed interfaces. Its solution relation must retain ordinary constraints and the one joint `K,D`, preserve correlated result evidence and the same provider, and establish both source/native solution directions plus typed substitution/transport.

The actual source-dependent remainder `Q` cannot be declared independent of annotation auxiliaries from these owners. The crosswalk supplies no typed relation, and typed evidence treats its flow/profile records as premises. No `Corr`, source-solution lift, reverse interpretation, or substitution law follows from matching names, positions, ports, or constructor wiring.

This is a bounded source-owner finding, not a claim that no rule exists elsewhere and not an underdetermination witness. It does not create a new semantic approval gate: if the judgment follows from settled semantics, derive it; seek a new decision only if a genuine semantic choice remains. I inspected the source annotation parser/local carrier, HIR call inventory, `yu-core` crosswalk and typed evidence, candidate source planner, and candidate annotation consumers. There is no safe compiler edit in this packet; changing the guarded negative-row behavior or enabling the shadow wiring would implement an unestablished source judgment.

## Evidence boundary

Static inspection and exact hash verification only. No tests, builds, parser/solver/compiler execution, runtime, probes, instrumentation, code changes, or semantic adoption. The result is limited to the 35 dependencies pinned by R63 revision 1.
