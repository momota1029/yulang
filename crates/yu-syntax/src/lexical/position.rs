//! Coordinates derived from the single live source suffix.
use crate::cursor::SyntaxIn;

pub(crate) fn suffix_marker(mut i: SyntaxIn) -> (usize, usize) {
    i.token(|lex| Some((lex.remainder().as_ptr() as usize, lex.remainder().len())))
        .expect("the live expression suffix probe is total")
}

pub(crate) fn advanced_origin(
    item_origin: usize,
    (entry_pointer, entry_length): (usize, usize),
    i: SyntaxIn,
) -> usize {
    let (suffix_pointer, suffix_length) = suffix_marker(i);
    let consumed = entry_length
        .checked_sub(suffix_length)
        .expect("a direct expression child cannot lengthen its live suffix");
    assert_eq!(
        entry_pointer.wrapping_add(consumed),
        suffix_pointer,
        "a direct expression child keeps the input on one source suffix",
    );
    item_origin
        .checked_add(consumed)
        .expect("a direct expression coordinate must fit usize")
}
