use core::ops::ControlFlow;

use crate::error::LatestSink;
use crate::error::std::StdErr;
use crate::input::{In, IsCut, Offset};
use crate::parser::item::{item, satisfy_map};
use crate::parser::prim::from_fn_mut;
use crate::parser::then::to;

#[test]
fn many_collects_items_and_consumes() {
    let mut input = "aaab";
    let mut errors: LatestSink<Offset<char>, StdErr<char>> = LatestSink::new();
    let mut is_cut = false;
    {
        let mut i = In::new(&mut input, &mut errors, IsCut::new(&mut is_cut));
        let out: Vec<char> = i.many(item('a')).unwrap();
        assert_eq!(out, vec!['a', 'a', 'a']);
    }
    assert_eq!(input, "b");
}

#[test]
fn many1_requires_at_least_one() {
    let mut input = "bbb";
    let mut errors: LatestSink<Offset<char>, StdErr<char>> = LatestSink::new();
    let mut is_cut = false;
    {
        let mut i = In::new(&mut input, &mut errors, IsCut::new(&mut is_cut));
        let out: Option<Vec<char>> = i.many1(item('a'));
        assert!(out.is_none());
    }
    assert_eq!(input, "bbb");
}

#[test]
fn sep_use_trail_accepts_trailing_separator() {
    let mut input = "a,a,";
    let mut errors: LatestSink<Offset<char>, StdErr<char>> = LatestSink::new();
    let mut is_cut = false;
    {
        let mut i = In::new(&mut input, &mut errors, IsCut::new(&mut is_cut));
        let (out, did_trail): (Vec<char>, bool) =
            i.sep_use_trail(item('a'), to(item(','), ())).unwrap();
        assert_eq!(out, vec!['a', 'a']);
        assert!(did_trail);
    }
    assert_eq!(input, "");
}

#[test]
fn sep_map_sums_items() {
    let mut input = "1,2,3";
    let mut errors: LatestSink<Offset<char>, StdErr<char>> = LatestSink::new();
    let mut is_cut = false;
    {
        let mut i = In::new(&mut input, &mut errors, IsCut::new(&mut is_cut));
        let digit = satisfy_map(|c: char| c.to_digit(10).map(|v| v as u32));
        let out = i
            .sep_map(digit, to(item(','), ()), |iter| iter.sum::<u32>())
            .unwrap();
        assert_eq!(out, 6);
    }
    assert_eq!(input, "");
}

#[test]
fn sep1_map_requires_first_item() {
    let mut input = "";
    let mut errors: LatestSink<Offset<char>, StdErr<char>> = LatestSink::new();
    let mut is_cut = false;
    {
        let mut i = In::new(&mut input, &mut errors, IsCut::new(&mut is_cut));
        let digit = satisfy_map(|c: char| c.to_digit(10).map(|v| v as u32));
        let out = i.sep1_map(digit, to(item(','), ()), |iter| iter.sum::<u32>());
        assert!(out.is_none());
    }
    assert_eq!(input, "");
}

#[test]
fn sep_reduce_left_associates() {
    let mut input = "1+2+3";
    let mut errors: LatestSink<Offset<char>, StdErr<char>> = LatestSink::new();
    let mut is_cut = false;
    {
        let mut i = In::new(&mut input, &mut errors, IsCut::new(&mut is_cut));
        let digit = satisfy_map(|c: char| c.to_digit(10).map(|v| v as i32));
        let out = i
            .sep_reduce(digit, item('+'), |left, _op, right| left + right)
            .unwrap();
        assert_eq!(out, 6);
    }
    assert_eq!(input, "");
}

#[test]
fn flow_many_map_collects_until_break() {
    let mut input = "12x34";
    let mut errors: LatestSink<Offset<char>, StdErr<char>> = LatestSink::new();
    let mut is_cut = false;
    {
        let mut i = In::new(&mut input, &mut errors, IsCut::new(&mut is_cut));
        let parser = from_fn_mut(|i| {
            let ch: char = crate::parser::item::any(i)?;
            if ch.is_ascii_digit() {
                Some(ControlFlow::Continue(ch.to_digit(10).unwrap() as u32))
            } else {
                Some(ControlFlow::Break(ch))
            }
        });
        let (out, break_): (Vec<u32>, Option<char>) =
            i.flow_many_map(parser, |iter| iter.collect()).unwrap();
        assert_eq!(out, vec![1, 2]);
        assert_eq!(break_, Some('x'));
    }
    assert_eq!(input, "34");
}

#[test]
fn many_till_collects_until_end_parser() {
    let mut input = "ab]cd";
    let mut errors: LatestSink<Offset<char>, StdErr<char>> = LatestSink::new();
    let mut is_cut = false;
    {
        let mut i = In::new(&mut input, &mut errors, IsCut::new(&mut is_cut));
        let (out, end): (Vec<char>, char) =
            i.many_till(crate::parser::item::any, item(']')).unwrap();
        assert_eq!(out, vec!['a', 'b']);
        assert_eq!(end, ']');
    }
    assert_eq!(input, "cd");
}

#[test]
fn many_till_allows_empty_prefix() {
    let mut input = "]";
    let mut errors: LatestSink<Offset<char>, StdErr<char>> = LatestSink::new();
    let mut is_cut = false;
    {
        let mut i = In::new(&mut input, &mut errors, IsCut::new(&mut is_cut));
        let (out, end): (Vec<char>, char) =
            i.many_till(crate::parser::item::any, item(']')).unwrap();
        assert!(out.is_empty());
        assert_eq!(end, ']');
    }
    assert_eq!(input, "");
}

#[test]
fn many_till_fails_without_end_parser() {
    let mut input = "ab";
    let mut errors: LatestSink<Offset<char>, StdErr<char>> = LatestSink::new();
    let mut is_cut = false;
    {
        let mut i = In::new(&mut input, &mut errors, IsCut::new(&mut is_cut));
        let out: Option<(Vec<char>, char)> = i.many_till(crate::parser::item::any, item(']'));
        assert!(out.is_none());
    }
    assert_eq!(input, "");
}
