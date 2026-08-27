# yu-syntax reference

`yu-syntax` のgrammar、CST、AST、typed recoveryを実装者向けに横断参照するための内部referenceである。

ここは正本ではない。構文規則、CSTのbyte range、AST、recovery契約の正本は
`notes/design/2026-08-20-yu-syntax-chasa-architecture.md`にある。このsiteは、そのうち
Authoritativeかつ実装済みの要素を、implementation sourceとfixtureへの参照つきで要約する。

ローカルbuild:

```text
mdbook build syntax-reference
```

ローカルserve:

```text
cd syntax-reference
mdbook serve
```

`book/`は生成物であり、version controlへ入れない。
