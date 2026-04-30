use chasa::prelude::*;
use unicode_ident::is_xid_continue;

use crate::EventInput;
use crate::context;
use crate::sink::EventSink;

pub fn boundary<I: EventInput, S: EventSink>(
    prev_char: char,
    mut i: context::In<I, S>,
) -> Option<()> {
    if is_xid_continue(prev_char) {
        i.not(one_of(is_xid_continue))
    } else {
        Some(())
    }
}
