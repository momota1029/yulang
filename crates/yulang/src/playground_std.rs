//! Compact embedded std profile for the browser playground.
//!
//! The full std package is still the semantic fallback. This profile keeps the
//! common playground path small by loading ordinary Yulang source modules for
//! arithmetic, collections, formatting, control flow, nondet, junction, and
//! console output without pulling parser/file/text-path modules into every run.

use std::path::PathBuf;

use sources::{Name, Path};

use crate::source::CollectedSource;

pub(crate) fn embedded_playground_std_sources() -> Vec<CollectedSource> {
    PLAYGROUND_STD_FILES
        .iter()
        .map(|file| {
            CollectedSource::new(
                PathBuf::from("<embedded-playground-std>").join(file.relative_path),
                module_path(file.relative_path),
                file.source.to_string(),
            )
        })
        .collect()
}

pub(crate) fn embedded_playground_std_contains_module_path(path: &Path) -> bool {
    PLAYGROUND_STD_FILES
        .iter()
        .any(|file| module_path(file.relative_path) == *path)
}

struct PlaygroundStdFile {
    relative_path: &'static str,
    source: &'static str,
}

fn module_path(relative_path: &str) -> Path {
    let module = relative_path
        .strip_suffix(".yu")
        .unwrap_or(relative_path)
        .trim_matches('/');
    Path {
        segments: module
            .split('/')
            .filter(|segment| !segment.is_empty())
            .map(|segment| Name(segment.to_string()))
            .collect(),
    }
}

const PLAYGROUND_STD_FILES: &[PlaygroundStdFile] = &[
    PlaygroundStdFile {
        relative_path: "std.yu",
        source: r#"
pub mod bool;
pub mod control;
pub mod core;
pub mod data;
pub mod float;
pub mod int;
pub mod io;
pub mod num;
pub mod prelude;
pub mod text;
"#,
    },
    PlaygroundStdFile {
        relative_path: "std/prelude.yu",
        source: r#"
pub use std::core::ops::*
pub use std::control::throw::*

pub use std::core::*
pub use std::core::cmp::*
pub use std::core::fmt::*
pub use std::core::seq::*
pub use std::core::convert::*
pub use std::num::*

pub use std::int::*
pub use std::float::*
pub use std::bool::*
pub use std::text::str::{
    str, concat, eq, len, line_count, line_range,
    index_raw, index_range, index_range_raw,
    splice, splice_raw,
    is_empty, replace_all
}
pub use std::text::char::*
pub use std::data::fold::Fold
pub use std::data::index::Index
pub use std::data::list::*
pub use std::data::opt::*
pub use std::data::range::*
pub use std::data::result::*
pub use std::control::flow::LoopLabel
pub use std::control::nondet::each
pub use std::control::nondet::guard
pub use std::control::junction::*
pub use std::control::var::*
pub use std::io::*
"#,
    },
    PlaygroundStdFile {
        relative_path: "std/core.yu",
        source: include_str!("../../../lib/std/core.yu"),
    },
    PlaygroundStdFile {
        relative_path: "std/core/ops.yu",
        source: r#"
use std::core::cmp::*
use std::control::throw::*
use std::num::*

pub nullfix(return) = std::control::flow::sub::return ()
pub prefix(return) 1.0.0 = std::control::flow::sub::return
pub prefix(fail) 1.0.0 = \e -> e.throw

pub nullfix(last) = loop_last()
pub nullfix(next) = loop_next()
pub nullfix(redo) = loop_redo()
pub prefix(last) 8.0.0 = label_last
pub prefix(next) 8.0.0 = label_next
pub prefix(redo) 8.0.0 = label_redo

pub nullfix (..) = std::data::range::full()
pub prefix (..) 8.0.0 = std::data::range::to_included
pub prefix (..<) 8.0.0 = std::data::range::to_excluded
pub suffix (..) 8.0.0 = std::data::range::from_included
pub suffix (<..) 8.0.0 = std::data::range::from_excluded
pub infix (..) 4.0.0 4.0.0 = std::data::range::inclusive
pub infix (..<) 4.0.0 4.0.0 = std::data::range::range
pub infix (<..) 4.0.0 4.0.0 = std::data::range::from_exclusive_to_inclusive
pub infix (<..<) 4.0.0 4.0.0 = std::data::range::exclusive

pub prefix(not) 8.0.0 = std::bool::not
pub prefix (-) 8.0.0 = \x -> std::int::sub 0 x

pub infix (+) 5.0.0 5.0.1 = \x -> \y -> x.add y
pub infix (-) 5.0.0 5.0.1 = \x -> \y -> x.sub y
pub infix (*) 6.0.0 6.0.1 = \x -> \y -> x.mul y
pub infix (/) 6.0.0 6.0.1 = \x -> \y -> x.div y
pub infix(div) 6.0.0 6.0.1 = std::int::div
pub infix(mod) 6.0.0 6.0.1 = std::int::mod
pub infix (==) 3.0.0 3.0.1 = \x -> \y -> x.eq y
pub infix (!=) 3.0.0 3.0.1 = \x -> \y -> std::bool::not (x.eq y)
pub infix (<) 3.0.0 3.0.1 = \x -> \y -> x.lt y
pub infix (<=) 3.0.0 3.0.1 = \x -> \y -> x.le y
pub infix (>) 3.0.0 3.0.1 = \x -> \y -> x.gt y
pub infix (>=) 3.0.0 3.0.1 = \x -> \y -> x.ge y

pub lazy infix(and) 2.0.0 2.0.1 = \a -> \b ->
    if a():
        b()
    else:
        false

pub lazy infix(or) 1.0.0 1.0.1 = \a -> \b ->
    if a():
        true
    else:
        b()

my loop_last() = std::control::flow::loop::last()
my loop_next() = std::control::flow::loop::next()
my loop_redo() = std::control::flow::loop::redo()
my label_last(label) = label.last()
my label_next(label) = label.next()
my label_redo(label) = label.redo()
"#,
    },
    PlaygroundStdFile {
        relative_path: "std/core/cmp.yu",
        source: r#"
pub role Eq 'a:
    pub a.eq: 'a -> bool

pub role Ord 'a:
    pub a.lt: 'a -> bool
    pub a.le: 'a -> bool
    pub a.gt: 'a -> bool
    pub a.ge: 'a -> bool

impl int: Eq:
    our x.eq y = std::int::eq x y

impl int: Ord:
    our x.lt y = std::int::lt x y
    our x.le y = std::int::le x y
    our x.gt y = std::int::gt x y
    our x.ge y = std::int::ge x y

impl float: Eq:
    our x.eq y = std::float::eq x y

impl float: Ord:
    our x.lt y = std::float::lt x y
    our x.le y = std::float::le x y
    our x.gt y = std::float::gt x y
    our x.ge y = std::float::ge x y

impl bool: Eq:
    our x.eq y = std::bool::eq x y

impl str: Eq:
    our x.eq y = std::text::str::eq x y

impl char: Eq:
    our x.eq y = std::text::char::eq x y

impl (list int): Eq:
    our xs.eq ys = case (std::data::list::view_raw xs, std::data::list::view_raw ys):
        (std::data::list::list_view::empty, std::data::list::list_view::empty) -> true
        (std::data::list::list_view::leaf x, std::data::list::list_view::leaf y) -> std::int::eq x y
        (std::data::list::list_view::node(xl, xr), std::data::list::list_view::node(yl, yr)) ->
            if xl.eq yl: xr.eq yr else false
        _ -> false
"#,
    },
    PlaygroundStdFile {
        relative_path: "std/core/convert.yu",
        source: r#"
pub role Cast 'from:
    type to
    pub from.cast: to

pub cast(x: int): std::num::frac::frac = std::num::frac::new x 1
pub cast(x: int): float = builtin_op::int_to_float x
pub cast(x: std::num::frac::frac): float = std::num::frac::to_float x
"#,
    },
    PlaygroundStdFile {
        relative_path: "std/core/fmt.yu",
        source: r#"
use std::core::ops::*
use std::data::opt::*

pub enum format_kind = display | debug | lower_hex | upper_hex
pub enum format_align = left | right | center
pub enum format_sign = plus | minus

pub struct format_spec {
    kind: format_kind,
    align: opt format_align,
    sign: opt format_sign,
    fill: opt str,
    width: opt int,
    precision: opt int,
    alternate: bool,
    zero_pad: bool,
}

pub role Display 'a:
    pub a.show: str
    pub a.say = std::io::out::write: a.show + "\n"
    pub a.note = std::io::err::write: a.show + "\n"

pub role Debug 'a:
    pub a.debug: str
    pub a.dd = std::io::err::write: a.debug + "\n"

my repeat(text: str, count: int): str =
    if count <= 0:
        ""
    else:
        text + repeat(text, count - 1)

my format_fill(spec: format_spec): str = case spec.fill:
    opt::just fill -> fill
    opt::nil -> if spec.zero_pad: "0" else: " "

my format_body(spec: format_spec, body: str): str = case spec.precision:
    opt::just limit ->
        if body.len <= limit:
            body
        else:
            std::text::str::index_range_raw body 0 limit
    opt::nil -> body

my starts_with_minus(body: str): bool =
    if body.len <= 0:
        false
    else:
        std::text::str::index_range_raw body 0 1 == "-"

my format_sign_prefix(spec: format_spec, head: str, body: str): str = case spec.sign:
    opt::just format_sign::plus ->
        if starts_with_minus body:
            head
        else:
            "+" + head
    opt::just format_sign::minus -> head
    opt::nil -> head

my format_with_padding(spec: format_spec, head: str, body: str): str = case spec.width:
    opt::nil ->
        my clipped = format_body spec body
        my body_prefix = format_sign_prefix spec head clipped
        body_prefix + clipped
    opt::just width ->
        my clipped = format_body spec body
        my body_prefix = format_sign_prefix spec head clipped
        my text = body_prefix + clipped
        my missing = width - text.len
        if missing <= 0:
            text
        else:
            my fill = format_fill spec
            case spec.align:
                opt::just format_align::left -> text + repeat(fill, missing)
                opt::just format_align::center ->
                    my left = missing div 2
                    my right = missing - left
                    repeat(fill, left) + text + repeat(fill, right)
                _ ->
                    if spec.zero_pad:
                        my padding = repeat(fill, missing)
                        my padded_prefix = body_prefix + padding
                        padded_prefix + clipped
                    else:
                        repeat(fill, missing) + text

pub format_display(spec: format_spec, value: 'a): str =
    where 'a: Display
    format_with_padding(spec, "", value.show)

pub format_debug(spec: format_spec, value: 'a): str =
    where 'a: Debug
    format_with_padding(spec, "", value.debug)

pub format_lower_hex(spec: format_spec, value: 'a): str =
    where 'a: LowerHex
    my head = if spec.alternate: "0x" else: ""
    format_with_padding(spec, head, value.lower_hex)

pub format_upper_hex(spec: format_spec, value: 'a): str =
    where 'a: UpperHex
    my head = if spec.alternate: "0X" else: ""
    format_with_padding(spec, head, value.upper_hex)

impl int: Display:
    our x.show = std::int::to_string x

impl int: Debug:
    our x.debug = x.show

impl float: Display:
    our x.show = std::float::to_string x

impl float: Debug:
    our x.debug = x.show

impl bool: Display:
    our x.show = std::bool::to_string x

impl bool: Debug:
    our x.debug = x.show

impl str: Display:
    our x.show = x

impl str: Debug:
    our x.debug = "\"" + x + "\""

impl char: Display:
    our x.show = std::text::char::to_string x

impl char: Debug:
    our x.debug = "'" + std::text::char::to_string x + "'"

impl unit: Display:
    our x.show = "()"

impl unit: Debug:
    our x.debug = "()"

my show_list_items(xs: list 'a): str =
    where 'a: Display
    case std::data::list::view_raw xs:
        std::data::list::list_view::empty -> ""
        std::data::list::list_view::leaf item -> item.show
        std::data::list::list_view::node(left, right) ->
            my left_text = show_list_items left
            my right_text = show_list_items right
            left_text + ", " + right_text

impl (list 'a): Display:
    where 'a: Display
    our xs.show = "[" + show_list_items xs + "]"

my debug_list_items(xs: list 'a): str =
    where 'a: Debug
    case std::data::list::view_raw xs:
        std::data::list::list_view::empty -> ""
        std::data::list::list_view::leaf item -> item.debug
        std::data::list::list_view::node(left, right) ->
            my left_text = debug_list_items left
            my right_text = debug_list_items right
            left_text + ", " + right_text

impl (list 'a): Debug:
    where 'a: Debug
    our xs.debug = "[" + debug_list_items xs + "]"

impl ('a, 'b): Display:
    where 'a: Display
    where 'b: Display
    our value.show = case value:
        (a, b) -> "(" + a.show + ", " + b.show + ")"

impl ('a, 'b, 'c): Display:
    where 'a: Display
    where 'b: Display
    where 'c: Display
    our value.show = case value:
        (a, b, c) -> "(" + a.show + ", " + b.show + ", " + c.show + ")"

impl ('a, 'b): Debug:
    where 'a: Debug
    where 'b: Debug
    our value.debug = case value:
        (a, b) -> "(" + a.debug + ", " + b.debug + ")"

impl ('a, 'b, 'c): Debug:
    where 'a: Debug
    where 'b: Debug
    where 'c: Debug
    our value.debug = case value:
        (a, b, c) -> "(" + a.debug + ", " + b.debug + ", " + c.debug + ")"
"#,
    },
    PlaygroundStdFile {
        relative_path: "std/core/seq.yu",
        source: r#"
pub role Len 'a:
    pub a.len: int

pub role IsEmpty 'a:
    pub a.is_empty: bool

impl str: Len:
    our s.len = std::text::str::len s

impl (list 'a): Len:
    our xs.len = std::data::list::len xs

impl str: IsEmpty:
    our s.is_empty = std::int::eq(std::text::str::len s, 0)

impl (list 'a): IsEmpty:
    our xs.is_empty = std::int::eq(std::data::list::len xs, 0)

pub len x = x.len
"#,
    },
    PlaygroundStdFile {
        relative_path: "std/num.yu",
        source: include_str!("../../../lib/std/num.yu"),
    },
    PlaygroundStdFile {
        relative_path: "std/num/frac.yu",
        source: include_str!("../../../lib/std/num/frac.yu"),
    },
    PlaygroundStdFile {
        relative_path: "std/bool.yu",
        source: include_str!("../../../lib/std/bool.yu"),
    },
    PlaygroundStdFile {
        relative_path: "std/int.yu",
        source: include_str!("../../../lib/std/int.yu"),
    },
    PlaygroundStdFile {
        relative_path: "std/float.yu",
        source: include_str!("../../../lib/std/float.yu"),
    },
    PlaygroundStdFile {
        relative_path: "std/text.yu",
        source: r#"
pub mod char;
pub mod str;
"#,
    },
    PlaygroundStdFile {
        relative_path: "std/text/char.yu",
        source: include_str!("../../../lib/std/text/char.yu"),
    },
    PlaygroundStdFile {
        relative_path: "std/text/str.yu",
        source: r#"
use std::core::ops::*
use std::data::opt::*
use std::data::index::*
use std::data::range::*
use std::text::char::char

pub concat: str -> str -> str = builtin_op::string_concat
pub eq: str -> str -> bool = builtin_op::string_eq
pub len: str -> int = builtin_op::string_len
pub line_count: str -> int = builtin_op::string_line_count
pub line_range: str -> int -> range = builtin_op::string_line_range
pub index_raw: str -> int -> char = builtin_op::string_index
pub index_range: str -> range -> str = builtin_op::string_index_range
pub index_range_raw: str -> int -> int -> str = builtin_op::string_index_range_raw
pub splice: str -> range -> str -> str = builtin_op::string_splice
pub splice_raw: str -> int -> int -> str -> str = builtin_op::string_splice_raw

pub type str with:
    pub s.splice r insert = std::text::str::splice s r insert
    pub s.replace_once from to = std::text::str::replace_once s from to
    pub s.replace from to = std::text::str::replace_all s from to
    pub s.len = std::text::str::len s
    pub s.is_empty = std::text::str::is_empty s
    pub s.print = std::io::print s
    pub s.println = std::io::println s
    pub s.eprint = std::io::eprint s
    pub s.eprintln = std::io::eprintln s

pub is_empty(s: str): bool = std::int::eq(std::text::str::len s, 0)

my starts_with_at(source: str, needle: str, start: int): bool =
    my end = std::int::add start (std::text::str::len needle)
    if std::int::le end (std::text::str::len source):
        std::text::str::index_range_raw source start end == needle
    else:
        false

my find_at(source: str, needle: str, start: int): opt int =
    if std::int::eq (std::text::str::len needle) 0:
        just start
    else:
        my limit = std::int::sub (std::text::str::len source) (std::text::str::len needle)
        my loop(i: int): opt int =
            if std::int::le i limit:
                if starts_with_at(source, needle, i):
                    just i
                else:
                    loop(std::int::add i 1)
            else:
                nil
        loop start

pub replace_once(source: str, from: str, to: str): str =
    if std::int::eq (std::text::str::len from) 0:
        source
    else:
        case find_at(source, from, 0):
            just i ->
                std::text::str::concat
                    (std::text::str::concat
                        (std::text::str::index_range_raw source 0 i)
                        to)
                    (std::text::str::index_range_raw
                        source
                        (std::int::add i (std::text::str::len from))
                        (std::text::str::len source))
            nil -> source

pub replace(source: str, from: str, to: str): str =
    replace_all(source, from, to)

pub replace_all(source: str, from: str, to: str): str =
    if std::int::eq (std::text::str::len from) 0:
        source
    else:
        my loop(start: int, out: str): str =
            case find_at(source, from, start):
                just i ->
                    my prefix = std::text::str::index_range_raw source start i
                    loop(
                        std::int::add i (std::text::str::len from),
                        std::text::str::concat (std::text::str::concat out prefix) to)
                nil ->
                    std::text::str::concat
                        out
                        (std::text::str::index_range_raw source start (std::text::str::len source))
        loop(0, "")

impl str: Index int:
    type value = char
    our s.index i = std::text::str::index_raw s i

impl str: Index range:
    type value = str
    our s.index r = std::text::str::index_range s r
"#,
    },
    PlaygroundStdFile {
        relative_path: "std/data.yu",
        source: include_str!("../../../lib/std/data.yu"),
    },
    PlaygroundStdFile {
        relative_path: "std/data/fold.yu",
        source: include_str!("../../../lib/std/data/fold.yu"),
    },
    PlaygroundStdFile {
        relative_path: "std/data/index.yu",
        source: include_str!("../../../lib/std/data/index.yu"),
    },
    PlaygroundStdFile {
        relative_path: "std/data/list.yu",
        source: r#"
use std::data::fold::*
use std::data::index::*
use std::data::opt::*
use std::data::range::*
use std::control::var::*
use std::core::ops::*

pub enum list_view 'a = empty | leaf 'a | node(list 'a, list 'a)

pub type list 'a with:
    pub xs.append ys = std::data::list::append xs ys
    pub xs.map f = std::data::list::map xs f
    pub xs.filter pred = std::data::list::filter xs pred
    pub xs.is_empty = std::data::list::is_empty xs
    pub xs.first = std::data::list::first xs
    pub xs.last = std::data::list::last xs
    pub xs.rev = std::data::list::rev xs

impl (list 'a): Index int:
    type value = 'a
    our xs.index i = std::data::list::index_raw xs i

impl (list 'a): Index range:
    type value = list 'a
    our xs.index r = std::data::list::index_range xs r

impl (ref 'e (list 'a)): Index int:
    type value = ref 'e 'a
    our r.index i = ref {
        get: \() -> std::data::list::index_raw (r.get()) i,
        update_effect: \() ->
            my loop(x: [_] _) = catch x:
                ref_update::update old, k ->
                    my new_item = ref_update::update (std::data::list::index_raw old i)
                    loop(k(std::data::list::splice_raw old i (i + 1) [new_item]))
            loop:r.update_effect()
    }

pub view_raw: list 'a -> list_view 'a = builtin_op::list_view_raw
pub merge: list 'a -> list 'a -> list 'a = builtin_op::list_merge
pub len: list 'a -> int = builtin_op::list_len
pub index_raw: list 'a -> int -> 'a = builtin_op::list_index
pub index_range: list 'a -> range -> list 'a = builtin_op::list_index_range
pub index_range_raw: list 'a -> int -> int -> list 'a = builtin_op::list_index_range_raw
pub splice: list 'a -> range -> list 'a -> list 'a = builtin_op::list_splice
pub splice_raw: list 'a -> int -> int -> list 'a -> list 'a = builtin_op::list_splice_raw

my fold_impl xs z f = case std::data::list::view_raw xs:
    list_view::empty -> z
    list_view::leaf x -> f z x
    list_view::node(left, right) -> fold_impl(right, fold_impl left z f, f)

impl (list 'a): Fold:
    type item = 'a
    our xs.fold z f = fold_impl xs z f

pub empty(): list 'a = []

pub singleton(x: 'a): list 'a = [x]

pub is_empty(xs: list 'a): bool = std::int::eq(std::data::list::len xs, 0)

pub cons(x: 'a, xs: list 'a): list 'a = std::data::list::merge(singleton x, xs)

pub uncons(xs: list 'a): opt ('a, list 'a) =
    my n = std::data::list::len(xs)
    if std::int::eq(n, 0):
        std::data::opt::opt::nil
    else:
        std::data::opt::opt::just (std::data::list::index_raw xs 0, std::data::list::index_range_raw xs 1 n)

pub fold xs z f = fold_impl xs z f

pub append(xs: list 'a, ys: list 'a): list 'a = std::data::list::merge xs ys

pub rev(xs: list 'a): list 'a = case std::data::list::view_raw xs:
    list_view::empty -> empty()
    list_view::leaf x -> singleton x
    list_view::node(left, right) -> append(rev(right), rev(left))

pub map(xs: list 'a, f: 'a -> 'b): list 'b = case std::data::list::view_raw xs:
    list_view::empty -> empty()
    list_view::leaf x -> singleton(f(x))
    list_view::node(left, right) -> append(map(left, f), map(right, f))

pub filter(xs: list 'a, pred: 'a -> bool): list 'a = case std::data::list::view_raw xs:
    list_view::empty -> empty()
    list_view::leaf x ->
        if pred x: singleton x else empty()
    list_view::node(left, right) -> append(filter(left, pred), filter(right, pred))

pub first(xs: list 'a): opt 'a = case uncons xs:
    std::data::opt::opt::nil -> std::data::opt::opt::nil
    std::data::opt::opt::just (head, _) -> std::data::opt::opt::just head

pub last(xs: list 'a): opt 'a = case uncons xs:
    std::data::opt::opt::nil -> std::data::opt::opt::nil
    std::data::opt::opt::just (head, tail) ->
        if is_empty tail: std::data::opt::opt::just head
        else: last tail
"#,
    },
    PlaygroundStdFile {
        relative_path: "std/data/opt.yu",
        source: include_str!("../../../lib/std/data/opt.yu"),
    },
    PlaygroundStdFile {
        relative_path: "std/data/range.yu",
        source: include_str!("../../../lib/std/data/range.yu"),
    },
    PlaygroundStdFile {
        relative_path: "std/data/result.yu",
        source: include_str!("../../../lib/std/data/result.yu"),
    },
    PlaygroundStdFile {
        relative_path: "std/control.yu",
        source: include_str!("../../../lib/std/control.yu"),
    },
    PlaygroundStdFile {
        relative_path: "std/control/flow.yu",
        source: include_str!("../../../lib/std/control/flow.yu"),
    },
    PlaygroundStdFile {
        relative_path: "std/control/junction.yu",
        source: include_str!("../../../lib/std/control/junction.yu"),
    },
    PlaygroundStdFile {
        relative_path: "std/control/nondet.yu",
        source: include_str!("../../../lib/std/control/nondet.yu"),
    },
    PlaygroundStdFile {
        relative_path: "std/control/throw.yu",
        source: include_str!("../../../lib/std/control/throw.yu"),
    },
    PlaygroundStdFile {
        relative_path: "std/control/var.yu",
        source: include_str!("../../../lib/std/control/var.yu"),
    },
    PlaygroundStdFile {
        relative_path: "std/io.yu",
        source: r#"
pub mod console;

pub use std::io::console::*
"#,
    },
    PlaygroundStdFile {
        relative_path: "std/io/console.yu",
        source: include_str!("../../../lib/std/io/console.yu"),
    },
];
