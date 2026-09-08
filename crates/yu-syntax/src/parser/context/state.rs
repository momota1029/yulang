use chasa_recover::Recoverable;

use crate::operator::OperatorTable;

pub(in crate::parser) struct Recover<'operators> {
    operators: &'operators OperatorTable,
}

impl<'operators> Recover<'operators> {
    pub(in crate::parser) fn new(operators: &'operators OperatorTable) -> Self {
        Self { operators }
    }

    pub(in crate::parser) fn operators(&self) -> &'operators OperatorTable {
        self.operators
    }
}

impl Recoverable for Recover<'_> {
    type Mark = ();

    fn mark(&self) -> Self::Mark {}

    fn rollback(&mut self, _: Self::Mark) {}
}
