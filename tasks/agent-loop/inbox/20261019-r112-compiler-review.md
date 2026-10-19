# R112 independent compiler/source review

Verdict: **CLEAN within the frozen finite production-owner scope**.
Reviewer: `/root/r112_compiler_review`; independent of the proof producer.
No BLOCKING, major or minor compiler-correctness finding.

## Reviewed bytes and authority

Fresh SHA-256 inspection matched:

| Input | SHA-256 |
| --- | --- |
| R112 rev3 contract | `ed7510f30473a7ea5c990cf12b13502e3c57e7a26e3a463ddc7402a5e17a273a` |
| R112 proof | `9444f51d980c2a8d01aacb407e81c4d2278f88785d6486c0d0ec696da1e48ca9` |
| R112 handoff | `51811cc902a33a185fc048d2b7ca9ba093947600089ab791a0ac12dcf0dfd048` |
| `crates/yu-hir/src/module.rs` | `c40ebde1755d300c83aafba0a81a85d19ed5200dfc2163ab72c8a3bb08baf29a` |
| `crates/yu-hir/src/module/local_source.rs` | `3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786` |
| R108 exact-source test | `ea90e8ef445aae1155e28e10356068dfaecb8b2bc430d5bf6f18094acee21e1a` |
| R108 closeout | `cfc0e6a45b329e099f1263833bc7c0160c8d0e034bf7596ffef1dc5da10666e8` |
| R100 rev6 contract | `d595f4878b9f931214e5da0cba6d7e53cf3e2e0ca243ecad784e55cac1611dec` |
| R100 conditional proof | `84a2aad8a63cad8673e2862e343eff27664c3daf003e97015a0289ba9569a971` |
| R100 handoff | `1a692cb7f3c31e83bf60ee90763216ef3253f2c357747c9258eff16e2f8cec19` |
| R100 implementation assessment | `60a1a90c37b5c8377addf12cd07d9703f98a093a9c1eeb86fb5db2b81f847596` |
| R85 proposed semantic contract | `fee3feaec5e8873fe4f056df3a9ae9ca16c342f0a8b314c027a35719eedd4609` |

Governing boundaries: root operating instructions, `rules/design-authority.md`,
the Authoritative top-level inference principles, and R112 rev3's finite
owner/source limit. The yulang-proofs skill's source-bridge distinction was
applied: an assumed transition is not source construction. R85's proposed
contract was read as Draft and grants no implementation or adoption authority.

## Independent source argument

The production branches were read before treating the submitted proof or
handoff as a claim to assess. Their self-explanations are not evidence.

This submission identifies the owning cause of the missing executable member;
it contains no repair. Production `lower_module` at `module.rs:1103` enables
ordinary carriers, and `lower_module_with_counters` at `1173–1184` enumerates
only direct node children. R108's test independently asserts that this exact
ImplDeclaration is a Root child, that the exact member reaches that same
implementation, and that the formal/body `selected` occurrences remain
distinct. Its retained raw child ordinal is not the node-only production
ordinal; the proof correctly uses the latter's actual enumeration instead.
R108's recorded pass is historical evidence, not a rerun in this review.

The complete `plan_root` at `1976–2025` returns UnsupportedItem for this
ImplDeclaration and RoleDeclaration before header admission or DefId creation.
It never visits the nested BindingStatement. `namespace` at `2027–2050` accepts
only Binding plans. The root-allocation match at `1245–1251` supplies None for
Unsupported; the unrelated root-loop occurrence does not become a member
DefinitionRootId, expression root or parameter.

The complete `lower_plan` at `2052–2204` returns Error from its Unsupported
branch before the executable-binding continuation. HirParameterId creation,
legacy LocalSource formation, lexical parameter insertion, `lower_body`, and
Lambda wrapping are all after that return. ErrorSink failure terminates the
attempt; it supplies no alternate successful member construction. The scope
restoration in the binding continuation does not affect this earlier branch.

Production carrier gates at `module.rs:1300` and `1311` accept Binding and
Expression respectively. Thus this Error has no carrier invocation and its
None outcome disappears on flattening. This conclusion uses those production
gates, not the Error arms inside cfg(test) helper traversals. The optional
ActDeclaration placeholder branch at `1273–1292` cannot consume this Impl.

`finalize_ordinary_admissions` at `1527–1656` requires an existing Binding at
the owner index (`1644`) before replacing an expression; it cannot promote
this Error. `local_source_for` at `979–988` only retrieves existing carriers
or definition-owned sources. `local_source::form_ordinary` at `502–554` needs
an existing owner and parameters. Its `form` at `556–642` rejects Unsupported
before Builder creation; earlier recovery/depth exits also construct no member.
For admitted bindings, its parameter/source/annotation/lexical work operates on
that admitted binding's original node. The separate top-level answer binding
cannot supply the nested implementation member's source or lexical ownership.

## Counterexamples considered and limit

No owner-local alternate producer for this exact nested member was found in
the inspected complete branches and production carrier gates. Equal spelling,
the retained role signature, root occurrences, and an unrelated executable
root fail the authentic-member requirement. Distinguishing RoleDeclaration,
ImplDeclaration, BindingStatement and OperatorChain is syntax-kind based;
the cut does not depend on the identifier or file path spelling.

The proof correctly allows an availability failure before item publication.
It proves neither successful whole-module lowering nor repository-wide absence
of a possible route. The claimed non-generation of this member's body
constraints through these owners follows from the missing executable source;
it is not a statement that the entire fixture generates no constraints.

R100-P2-MEMBER remains OPEN at authentic member materialization. Role lookup,
selection, dispatch, CheckedBody, P3/P4, runtime result `2`, R85 adoption,
original A/B and production promotion remain open. No new source pin or
semantic owner was required. No repair or promotion is recommended by this
receipt.

Checks: static text/source inspection and SHA-256 only. No tests, builds,
compiler/runtime invocation, formatter, Git, external contact or descendants.
Only this exact leased receipt was written; source and test files were not
edited. Review complete; worker stopped with no repair activity.
