# Yulang syntax and CST reference

This bilingual reference documents Yulang `syntax-v0` surface syntax and its
lossless Rowan CST. It is an incremental reference migration: the syntax
content-model pages provide the complete syntax-v0 placement inventory, while
detailed construct pages are added or refined in phases.

The Authoritative *Syntax freeze and vertical-implementation completion-policy
amendment* (2026-09-17) preserves accepted syntax and direct-CST topology as
`syntax-v0`. Authoritative design records govern grammar, topology, and
recovery decisions. Implementation, tests, fixtures, and commits are not
normative sources.

- `en/` is the English book.
- `ja/` is the Japanese book.

Build either book from the repository root:

```text
mdbook build syntax-reference/en
mdbook build syntax-reference/ja
```

Serve either book locally:

```text
cd syntax-reference/en && mdbook serve
cd syntax-reference/ja && mdbook serve
```

Each book writes generated HTML to its own `book/` directory. Build output is excluded from version control.
