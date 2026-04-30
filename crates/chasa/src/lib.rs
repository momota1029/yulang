pub mod back;
pub mod char;
pub mod error;
pub mod input;
pub mod parser;

pub use back::{Back, Front, RbBack, RbFront};
pub use error::{ErrorSink, LatestSink, MergeErrors, NullSink};
pub use input::{Input, Offset, SeqInput, ToSpan};

/// Common exports for examples and quick tests.
pub mod prelude {
    pub use crate::back::Back;
    pub use crate::char::{
        ASCII, ASCII_ALPHA, ASCII_ALPHANUM, ASCII_DIGIT, SPACE, ascii, ascii_alpha,
        ascii_alphanumeric, ascii_digit, space, ws, ws1,
    };
    pub use crate::input::{In, Input, SeqInput, ToSpan};
    pub use crate::parser::choice::{choice, or};
    pub use crate::parser::flow::{
        flow, flow_many, flow_many_map, flow_many_map_mut, flow_many_map_once, many_till,
    };
    pub use crate::parser::item::{
        any, eoi, item, item_of, none_of, one_of, satisfy, satisfy_map, satisfy_map_mut,
        satisfy_map_once, satisfy_mut, satisfy_once, set::ItemSet as _,
    };
    pub use crate::parser::many::{
        many, many_map, many_map_mut, many_map_once, many_skip, many1, many1_skip,
    };
    pub use crate::parser::prim::{
        cut, cut_after, cut_on_ok, is_true, label, label_with, lookahead, maybe, not, uncut, value,
        with_range, with_seq, with_span,
    };
    pub use crate::parser::sep::{
        sep, sep_map, sep_map_mut, sep_map_once, sep_reduce, sep1, sep1_map,
    };
    pub use crate::parser::then::{
        and_then, and_then_mut, and_then_once, between, bind, left, map, right, seq, skip, then,
        then_mut, then_once, to,
    };
    pub use crate::parser::token::tag;
    pub use crate::parser::{
        Parser as _, ParserMut as _, ParserOnce as _, SkipParser as _, SkipParserMut as _,
        SkipParserOnce as _, prim::from_fn, prim::from_fn_mut, prim::from_fn_once,
    };
}
