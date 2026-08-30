# Documentation policy

## Public documentation

Before writing or editing prose under `web/docs/`, read both:

- `notes/style/japanese-writing-guide.md` for orthography, formatting, paragraph construction, and argument construction;
- `notes/style/writing-rhythm-guide.md` for page-layer assignment, conflict arbitration, rhythm, English prose, and translation pairs.

Both guides apply. When they appear to conflict, use the arbitration rule in the rhythm guide rather than choosing whichever wording is easier.

These guides govern site prose only. They do not govern commit messages, internal agent reports, design provenance fields, diagnostics expectations, or direct user conversation.

## Documentation roles

Public docs, README text, guides, release notes, specifications, diagnostics, and UI text use the register appropriate to their audience. They do not inherit the primary agent's conversational Japanese style.

A documentation writer may implement confirmed content and structure but may not invent or finalize language/compiler design. When docs expose a missing semantic decision, stop and route it through design authority.

## Examples and translation pairs

Executable examples must agree with the current compiler/spec and receive regression review when changed. Do not “repair” an example by silently changing the language contract.

For Japanese/English paired pages, preserve semantic correspondence while following each language's register; do not force sentence-by-sentence literal translation.

## Review

Documentation changes should check:

- intended page layer and audience;
- terminology against authoritative spec/design;
- examples and commands against current behavior;
- links and navigation;
- Japanese/English semantic consistency where paired;
- absence of conversational agent phrasing in published artifacts.
