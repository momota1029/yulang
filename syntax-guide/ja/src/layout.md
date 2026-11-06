# ブロックと字下げ

ブロックは、字下げ(`:` で始める)と、波括弧の両方で書ける。意味は同じ。

```yulang
if cond:
    a
else:
    b

if cond { a } else { b }
```

状態: 字下げの継続は確定・他は仮採用・未検査。出典: `spec/01-lexical.md` 1.3。

## 字下げが続きか、新しい文か

改行は、文の区切りになる。次の行の字下げが基準より**深ければ、前の式の続き**。同じか浅ければ、**新しい文**。

```yulang
f x
    y         // 字下げが深い → 同じ式の続き。f x y(y は 3 つ目の引数)

f x
y             // 字下げが同じ → 新しい文

xs
    .map f    // 字下げが深い → xs.map f
```

- 長い application は、続きの行を深く字下げして、複数行に折れる。`:` や `{}` は必須ではない。
- 括弧の中では、基準は開き括弧の直後の行の字下げ。基準より深い改行は現在の項目の続きで、基準以下の改行は次の項目の区切りになる。

## `:` の使い方

`:` は、「ここから本体」を表す。

```yulang
if n < 0: "negative"
elsif n == 0: "zero"
else: "positive"

for x in 0..10:
    say x

f: body                 // 式の中の colon application(空白の章を参照)
```

## 注意

`main:web/docs/ja/guide/pitfalls.md` の「改行で裸 application は閉じる」という記述は、この規則と逆で、古い。採らない。
