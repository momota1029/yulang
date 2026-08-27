# yu-syntax reference

`yu-syntax`のgrammar、CST、AST、typed recoveryを実装・保守する人のためのbilingual internal referenceである。

二つの独立した軽量mdBookを持つ。gettextや`mdbook-i18n-helpers`は使わず、両bookは同じ正本をそれぞれの言語で要約する。

- `en/`: future Claude/Codex sessionがimplementation symbolやfixtureを横断参照しやすいEnglish book。
- `ja/`: projectのhuman maintainerが読みやすいJapanese book。

どちらも正本ではない。構文規則、CST byte range、AST、recovery契約の正本は
`notes/design/2026-08-20-yu-syntax-chasa-architecture.md`にある。

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
