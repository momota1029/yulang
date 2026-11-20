# Proposed next live Rust parser controls (not executed in cycle 293)

<!-- check: parse-ok -->
```yulang
role Index 'container 'key:
    type value
    type fallback = 'key
    type scalar = char
```

<!-- check: parse-error; shape: Equals exists but TypeExpression has Missing -->
```yulang
role Index 'container 'key:
    type value =
```
