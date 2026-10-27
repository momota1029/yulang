# Independent review: import source authority audit r1

Reviewer: `/root/import_source_authority_review` (`spec_auditor`), fresh
non-author read-only review. Sprint: `IMPORT-SOURCE-AUTHORITY-AUDIT-20261027/r1`.

## Verdict

Accept the source and proof handoffs as a bounded static authority audit. No
BLOCKING or major semantic finding. One minor procedural wording issue needs to
be recorded in the outcome.

## Independently checked evidence

The source handoff hash is
`e34bfc3a23e49dce3f1f9dc7ff2d048b243a508e0da7220b8cb0b51981a55a75`; the proof
handoff hash is
`8bcbe3f78a2070908387b04ff0aefbae3d42bb67e32d38175856bf7ca328dd91`. The proof
pin manifest hash matches
`993f2120a5e5577fec09018bede0d67d210af68d13738a0de9279bb168ae21a6`, and all 68
entries independently rehash unchanged.

The governing design adopts construction §§3–5 while withholding production
resolver authority (`2026-10-08-source-generalize-definition.md:3–9,35–38,140–155`).
Its companion requires source-owned Mono/Established, Published, Family and
Alias evidence (`2026-10-08-source-generalize-definition-and-proof.md:219–231,
305–321,617–624`). Resolver identity cannot choose among those constructions.

All seven `Binding` fields are accounted for. Ordinary binding records supply
`.published` and their defaults only conditional on an actual Source-binding
construction (`OriginalSourceSyntax.lean:188–226`). Formal registration supplies
annotation, entry and single-use metadata (`OriginalSourceGeneration.lean:132–136`).
The handoffs do not turn these defaults into seven independent semantic choices.

The alias distinction is correct. Rust chooses an exposure name while retaining
provider resolution (`module.rs:404–409`); the inspected fixture asserts common
provider identity (`module.rs:4817–4835`). SRC-J Alias instead copies an existing
complete Binding and shares an installed publication identity
(`OriginalSourceGeneration.lean:430–438,643–646`). Preservation is conditional on
successful installation (`OriginalSourceEnvironment.lean:1343–1362`).

Complete ordered roots remain separate. `moduleS` receives an existing Source
body and generates a supplied linking atom (`OriginalSourceGeneration.lean:344–347`);
it supplies no import elaborator. The provider-evidence transport and complete
module-root construction are unresolved correspondence premises, not an
established compiler defect or approved semantic change.

## Minor finding: contradictory reviewer command restriction

The sprint contract lines 76–77 prohibit all reviewer commands, while the
review assignment requires independent source and hash inspection. The primary's
assignment and clarification authorize read-only inspection; the contract's
resource section prohibits verifier execution. The review therefore used
read-only shell inspection and hashing only. Record the contradiction in the
outcome, and give future contracts precise command permissions. Do not claim
literal zero commands.

No theorem, verifier result, parent closure or new semantic decision is claimed.
The fixture tests were inspected, not run. Review created no files, used no Git,
Cargo, Lean/Lake, tests or formatters, and started no descendants. No process
remains.
