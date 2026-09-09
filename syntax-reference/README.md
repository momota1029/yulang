# Yulang syntax and CST reference

This bilingual reference specifies Yulang surface syntax and its lossless Rowan
CST. It is a language and tree-schema reference, not a chronicle of parser
implementation.

The reference records both implemented CST facts and approved construction
targets. Each affected page labels an approved target that has not yet reached
the implementation. The Authoritative design records remain the source for
grammar and recovery decisions.

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
