# reborrow-generic

Generalized reborrowing traits that extend Rust’s “reborrow” beyond plain references.

Rust lets you “reborrow” `&mut T` as `&mut T` with a shorter lifetime, but that mechanism is
*built-in for references* and doesn’t directly scale to “borrow handles you store in a struct”.

`reborrow-generic` gives you:

- a trait (`Reborrow`) to express “this thing can be reborrowed”,
- and (optionally) a derive macro so you can **store reborrowable fields** and still reborrow the whole struct.

## Core idea

The core trait is `Reborrow`:

```rust,ignore
pub trait Reborrow {
    type Target<'short>: Reborrowed<'short>
    where
        Self: 'short;

    fn rb<'short>(&'short mut self) -> Self::Target<'short>;
}
```

`Target<'short>` is “the same thing, but reborrowed for a shorter lifetime”.

This crate provides `Reborrow` impls for:

- `&mut T`, `&T`
- tuples up to length 32 (so you can reborrow `(a, b, c, ...)`)

## Usage examples

### Basic reborrowing (tuple of `&mut`)

```rust
use reborrow_generic::Reborrow;

let mut x = 1;
let mut y = 2;
let mut both = (&mut x, &mut y);

let (x2, y2) = both.rb();
*x2 += 10;
*y2 += 100;

assert_eq!((x, y), (11, 102));
```

### The real payoff: reborrowable structs (derive)

This is the main difference from Rust’s built-in “reborrow”: you can put `Reborrow::Target<'a>` in
fields, derive `Reborrow`, and then reborrow the whole struct safely.

```rust
# #[cfg(feature = "derive")]
# {
use reborrow_generic::Reborrow;
use reborrow_generic::short::Rb;

#[derive(reborrow_generic::Reborrow)]
struct Args<'a, A: Rb + 'a, B: Rb + 'a = ()> {
    a: A::Target<'a>,
    b: B::Target<'a>,
}

let mut x = 5;
let mut y = String::from("hello");

let mut both: Args<'_, &mut i32, &mut String> = Args { a: &mut x, b: &mut y };
let size_both = std::mem::size_of_val(&both);

*both.rb().a += 1;
both.rb().b.pop();
assert_eq!((x, y), (6, "hell".to_string()));

let mut z = 5;
let first_only: Args<'_, &mut i32> = Args { a: &mut z, b: () };
let size_first = std::mem::size_of_val(&first_only);

// `B = ()` is a zero-sized field, so it optimizes away.
assert!(size_first < size_both);
assert_eq!(size_first, std::mem::size_of::<&mut i32>());
# }
```

This pattern is especially handy for “argument bundles” passed through procedural code (parsers,
visitors, etc.), where you want to carry multiple borrows without fighting the borrow checker.

If you use a default type parameter of `()`, the unused field is zero-sized and can be optimized away.

```rust
use reborrow_generic::Reborrow;

type Arg<A, B = ()> = (A, B);

let mut x = 5;
let mut y = String::from("hello");

let mut both: Arg<&mut i32, &mut String> = (&mut x, &mut y);
let size_both = std::mem::size_of_val(&both);

{
    let (x2, _y2) = both.rb();
    *x2 += 1;
}
both.1.pop();
assert_eq!((x, y), (6, "hell".to_string()));

let mut z = 5;
let first_only: Arg<&mut i32> = (&mut z, ());
let size_first = std::mem::size_of_val(&first_only);

assert!(size_first < size_both);
assert_eq!(size_first, std::mem::size_of::<&mut i32>());
```

## Derive macro

Enable the `derive` feature to use the procedural macro.

```toml
reborrow-generic = { version = "0.1.0", features = ["derive"] }
```

```rust
# #[cfg(feature = "derive")]
# {
#[derive(reborrow_generic::Reborrow)]
struct Foo<'a> {
    s: &'a str,
}
# }
```

### Reference mode

If you want a type itself to reborrow as `&mut Self`, enable the `ref` mode on the derive.

```rust
# #[cfg(feature = "derive")]
# {
use reborrow_generic::Reborrow;

#[derive(reborrow_generic::Reborrow)]
#[reborrow(ref)]
struct Shared<T> {
    value: T,
}

let mut data = Shared { value: 1 };
*data.rb() = Shared { value: 2 };
# }
```
