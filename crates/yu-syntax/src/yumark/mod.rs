//! Isolated Yumark Gate 2 judges and structural frame storage.
//!
//! This module implements §§2–4 and Gate 2 of the authoritative doc-comment
//! addendum plus the frame-transaction storage addendum. It deliberately has
//! no root, Statement, header, CST, or public parser dispatch edge.

#![allow(
    dead_code,
    reason = "Gate 2 is an isolated construction; production dispatch belongs to Gate 6"
)]

mod frame;
mod judge;
