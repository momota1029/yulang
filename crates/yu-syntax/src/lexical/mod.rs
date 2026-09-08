//! Lexical input owns retained Items, scanning, physical fences and stop observation.
//! Grammar owners consume these facts without reopening source or emitting trivia twice.

pub(super) mod current_item;
pub(super) mod expression_item;
pub(super) mod item;
pub(super) mod lexer;
pub(super) mod observation;
pub(super) mod operator_scan;
pub(super) mod position;
pub(super) mod yumark;

pub(crate) mod stops;
pub(crate) mod trivia;
