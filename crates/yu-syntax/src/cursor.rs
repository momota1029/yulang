//! Live syntax and lexical cursors with their recoverable operator environment.

use chasa_recover::{In, Recoverable};

use crate::{cst_output::CstOutput, operator_table::OperatorTable};

pub(crate) type SyntaxIn<'a, 'source, 'recover, 'operators, 'output, 'frozen> =
    In<'a, &'source str, &'recover mut Recover<'operators>, &'output mut CstOutput<'frozen>>;

pub(crate) type LexIn<'a, 'source, 'recover, 'operators> =
    In<'a, &'source str, &'recover mut Recover<'operators>, ()>;

pub(crate) struct Recover<'operators> {
    operators: &'operators OperatorTable,
}

impl<'operators> Recover<'operators> {
    pub(crate) fn new(operators: &'operators OperatorTable) -> Self {
        Self { operators }
    }

    pub(crate) fn operators(&self) -> &'operators OperatorTable {
        self.operators
    }
}

impl Recoverable for Recover<'_> {
    type Mark = ();

    fn mark(&self) -> Self::Mark {}

    fn rollback(&mut self, _: Self::Mark) {}
}
