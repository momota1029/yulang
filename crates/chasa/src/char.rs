//! `char`-level convenience parsers and sets.
//!
//! This module is intended for inputs where `I::Item = char` (e.g. `&str`).
//!
//! The building blocks are:
//! - predicate sets like [`SPACE`], [`ASCII_ALPHA`], ...
//! - single-character parsers like [`space`], [`ascii_digit`], ...
//! - common whitespace consumers [`ws`] / [`ws1`]

use reborrow_generic::short::Rb;

use crate::back::RbBack;
use crate::error::ErrorSink;
use crate::error::std::Unexpected;
use crate::input::{In, Input};

/// `char::is_whitespace` as an [`item::set::ItemSet`] predicate.
pub const SPACE: fn(char) -> bool = is_space;
fn is_space(c: char) -> bool {
    c.is_whitespace()
}

/// Parse one whitespace character.
///
/// ```text
/// use chasa::prelude::*;
///
/// let out = " \t".test(space);
/// assert_eq!(out, Some(' '));
/// ```
#[inline]
pub fn space<I, E, N, L>(mut i: In<I, N, L, E>) -> Option<char>
where
    I: Input<Item = char>,
    N: Rb,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Unexpected<char>: Into<E::Error>,
{
    i.one_of(SPACE)
}

/// Consume zero or more whitespace characters.
///
/// ```text
/// use chasa::prelude::*;
///
/// let out = " \t\na".test(ws);
/// assert_eq!(out, Some(()));
/// ```
#[inline]
pub fn ws<I, E, N, L>(mut i: In<I, N, L, E>) -> Option<()>
where
    I: Input<Item = char>,
    N: Rb,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Unexpected<char>: Into<E::Error>,
{
    i.many_skip(space)
}

/// Consume one or more whitespace characters.
///
/// ```text
/// use chasa::prelude::*;
///
/// let out = " \t\na".test(ws1);
/// assert_eq!(out, Some(()));
/// ```
#[inline]
pub fn ws1<I, E, N, L>(mut i: In<I, N, L, E>) -> Option<()>
where
    I: Input<Item = char>,
    N: Rb,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Unexpected<char>: Into<E::Error>,
{
    i.many1_skip(space)
}

/// `char::is_ascii` as an [`item::set::ItemSet`] predicate.
pub const ASCII: fn(char) -> bool = is_ascii;
fn is_ascii(c: char) -> bool {
    c.is_ascii()
}

/// Parse one ASCII character.
///
/// ```text
/// use chasa::prelude::*;
///
/// let out = "aβ".test(ascii);
/// assert_eq!(out, Some('a'));
/// ```
#[inline]
pub fn ascii<I, E, N, L>(mut i: In<I, N, L, E>) -> Option<char>
where
    I: Input<Item = char>,
    N: Rb,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Unexpected<char>: Into<E::Error>,
{
    i.one_of(ASCII)
}

/// `char::is_ascii_alphabetic` as an [`item::set::ItemSet`] predicate.
pub const ASCII_ALPHA: fn(char) -> bool = is_ascii_alpha;
fn is_ascii_alpha(c: char) -> bool {
    c.is_ascii_alphabetic()
}

/// Parse one ASCII alphabetic character.
///
/// ```text
/// use chasa::prelude::*;
///
/// let out = "Z9".test(ascii_alpha);
/// assert_eq!(out, Some('Z'));
/// ```
#[inline]
pub fn ascii_alpha<I, E, N, L>(mut i: In<I, N, L, E>) -> Option<char>
where
    I: Input<Item = char>,
    N: Rb,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Unexpected<char>: Into<E::Error>,
{
    i.one_of(ASCII_ALPHA)
}

/// `char::is_ascii_digit` as an [`item::set::ItemSet`] predicate.
pub const ASCII_DIGIT: fn(char) -> bool = is_ascii_digit;
fn is_ascii_digit(c: char) -> bool {
    c.is_ascii_digit()
}

/// Parse one ASCII digit.
///
/// ```text
/// use chasa::prelude::*;
///
/// let out = "7a".test(ascii_digit);
/// assert_eq!(out, Some('7'));
/// ```
#[inline]
pub fn ascii_digit<I, E, N, L>(mut i: In<I, N, L, E>) -> Option<char>
where
    I: Input<Item = char>,
    N: Rb,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Unexpected<char>: Into<E::Error>,
{
    i.one_of(ASCII_DIGIT)
}

/// `char::is_ascii_alphanumeric` as an [`item::set::ItemSet`] predicate.
pub const ASCII_ALPHANUM: fn(char) -> bool = is_ascii_alphanumeric;
fn is_ascii_alphanumeric(c: char) -> bool {
    c.is_ascii_alphanumeric()
}

/// Parse one ASCII alphanumeric character.
#[inline]
pub fn ascii_alphanumeric<I, E, N, L>(mut i: In<I, N, L, E>) -> Option<char>
where
    I: Input<Item = char>,
    N: Rb,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Unexpected<char>: Into<E::Error>,
{
    i.one_of(ASCII_ALPHANUM)
}
