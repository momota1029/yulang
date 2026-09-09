//! Live syntax and lexical cursors with their recoverable operator environment.

use chasa_recover::{In, ParserOnce, Recoverable};

use crate::operator_table::OperatorTable;

pub(crate) mod recovery;

pub(crate) struct SyntaxIn<'a, 'source, 'operators, 'cache> {
    source: &'a mut &'source str,
    recover: &'a mut Recover<'operators>,
    pub(crate) state: &'a mut rowan::GreenNodeBuilder<'cache>,
}

pub(crate) type LexIn<'a, 'source, 'recover, 'operators> =
    In<'a, &'source str, &'recover mut LexRecover<'operators>, ()>;

/// Temporary lexical observation of the immutable operator environment.
pub(crate) struct LexRecover<'operators> {
    operators: &'operators OperatorTable,
}

impl<'operators> LexRecover<'operators> {
    fn new(operators: &'operators OperatorTable) -> Self {
        Self { operators }
    }

    #[cfg(test)]
    pub(crate) fn new_for_test(operators: &'operators OperatorTable) -> Self {
        Self::new(operators)
    }
    pub(crate) fn operators(&self) -> &'operators OperatorTable {
        self.operators
    }
}

impl Recoverable for LexRecover<'_> {
    type Mark = ();
    fn mark(&self) {}
    fn rollback(&mut self, _: ()) {}
}

impl<'a, 'source, 'operators, 'cache> SyntaxIn<'a, 'source, 'operators, 'cache> {
    pub(crate) fn new(
        source: &'a mut &'source str,
        recover: &'a mut Recover<'operators>,
        state: &'a mut rowan::GreenNodeBuilder<'cache>,
    ) -> Self {
        Self {
            source,
            recover,
            state,
        }
    }

    pub(crate) fn rb(&mut self) -> SyntaxIn<'_, 'source, 'operators, 'cache> {
        SyntaxIn::new(self.source, self.recover, self.state)
    }

    pub(crate) fn token<O>(
        &mut self,
        operation: impl FnOnce(LexIn<'_, 'source, '_, 'operators>) -> Option<O>,
    ) -> Option<O> {
        let mut view = LexRecover::new(self.recover.operators);
        let mut i: LexIn = In::new(self.source, &mut view, ());
        i.token(operation)
    }

    pub(crate) fn map<P, F, O1, O2>(self, parser: P, map: F) -> Option<O2>
    where
        P: for<'view> ParserOnce<&'source str, &'view mut LexRecover<'operators>, (), Output = O1>,
        F: FnOnce(O1) -> O2,
    {
        let mut view = LexRecover::new(self.recover.operators);
        let mut i: LexIn = In::new(self.source, &mut view, ());
        i.check(parser).map(map)
    }
}

pub(crate) struct Recover<'operators> {
    operators: &'operators OperatorTable,
    recoveries: Vec<recovery::RecoverySlot<'operators>>,
    diagnostics: recovery::DiagnosticSequence<'operators>,
    active_structured: Option<usize>,
}

/// Own the recovery state for the complete source-file construction.
pub(crate) fn parse_root(
    source: &str,
    operators: &OperatorTable,
    frozen: &[crate::recovery_record::CommittedRecoveryRecord],
) -> crate::source_file::RootCandidate {
    let mut remaining = source;
    let mut recover = Recover::reconcile_scoped(operators, frozen);
    let mut builder = rowan::GreenNodeBuilder::new();
    builder.start_node(crate::SyntaxKind::Root.into());
    crate::root_statement::parse_root_statements(
        source.len(),
        &mut remaining,
        &mut recover,
        &mut builder,
    );
    builder.finish_node();
    crate::source_file::RootCandidate {
        green: builder.finish(),
        committed_recoveries: recover.finish_recoveries(),
    }
}

/// Header discovery borrows its cursor but cannot replace or finalize it.
pub(crate) fn discover_header(
    source: &str,
    frozen: Option<&[crate::recovery_record::CommittedRecoveryRecord]>,
) -> crate::header::HeaderDiscovery {
    let operators = OperatorTable::empty();
    let mut recover = frozen.map_or_else(
        || Recover::new(&operators),
        |records| Recover::reconcile_scoped(&operators, records),
    );
    let mut builder = rowan::GreenNodeBuilder::new();
    let mut header = crate::header::discover_header_with_cursor(source, &mut recover, &mut builder);
    let _ = builder.finish();
    header.recoveries = recover.finish_recoveries();
    header
}

impl<'operators> Recover<'operators> {
    fn new(operators: &'operators OperatorTable) -> Self {
        Self {
            operators,
            recoveries: Vec::new(),
            diagnostics: recovery::DiagnosticSequence::fresh(),
            active_structured: None,
        }
    }

    #[cfg(test)]
    pub(crate) fn new_for_test(operators: &'operators OperatorTable) -> Self {
        Self::new(operators)
    }

    pub(crate) fn operators(&self) -> &'operators OperatorTable {
        self.operators
    }
}
