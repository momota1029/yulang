use chasa_recover::Recoverable;

use crate::operator::OperatorTable;

pub(super) struct Recover<'operators> {
    operators: &'operators OperatorTable,
}

impl<'operators> Recover<'operators> {
    pub(super) fn new(operators: &'operators OperatorTable) -> Self {
        Self { operators }
    }
}

impl Recoverable for Recover<'_> {
    type Mark = ();

    fn mark(&self) -> Self::Mark {}

    fn rollback(&mut self, _: Self::Mark) {}
}
