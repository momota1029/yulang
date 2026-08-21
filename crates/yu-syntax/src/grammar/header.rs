//! Internal candidate for source-leading header discovery.
//!
//! This module deliberately shares declaration parsing with full mode while
//! keeping its result private until it replaces the legacy `HeaderCursor`
//! entrypoint in a later vertical slice.

use std::ops::Range;

use chasa::{
    Back as _,
    input::IsCut,
    prelude::{In, from_fn},
};

use crate::{
    HeaderImport, HeaderOperator, HeaderStop,
    input::SourceInput,
    scan::trivia::scan_trivia,
    session::{LineState, ParseLocal},
};

use super::declaration::{HeaderDeclaration, parse_header_declaration};

/// Header facts and coverage discovered by the shared grammar candidate.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct HeaderDiscovery {
    coverage: Range<usize>,
    stop: HeaderStop,
    imports: Vec<HeaderImport>,
    operators: Vec<HeaderOperator>,
}

impl HeaderDiscovery {
    pub(crate) fn coverage(&self) -> &Range<usize> {
        &self.coverage
    }

    pub(crate) fn stop(&self) -> HeaderStop {
        self.stop
    }

    pub(crate) fn imports(&self) -> &[HeaderImport] {
        &self.imports
    }

    pub(crate) fn operators(&self) -> &[HeaderOperator] {
        &self.operators
    }
}

/// Discovers leading header declarations without changing the public entrypoint.
pub(crate) fn discover_header(source: &str) -> HeaderDiscovery {
    let mut source_input = SourceInput::new(source);
    let mut local = ParseLocal::new();
    local.set_line(LineState {
        at_line_start: true,
        ..LineState::default()
    });
    let mut expectations = chasa::LatestSink::new();
    let mut is_cut = false;
    let mut input = In::new(
        &mut source_input,
        &mut expectations,
        IsCut::new(&mut is_cut),
    )
    .set_local(&mut local);
    let imports = Vec::new();
    let operators = Vec::new();

    let stop = loop {
        input
            .run(from_fn(scan_trivia))
            .expect("trivia scanning is total");
        if input.input.remainder().is_empty() {
            break HeaderStop::Eof;
        }
        if !at_header_statement_start(input.local.line()) {
            break HeaderStop::FirstNonHeader;
        }

        let statement_start = input.checkpoint();
        let Some(declaration) = input.run(from_fn(parse_header_declaration)) else {
            input.rollback(statement_start);
            break HeaderStop::FirstNonHeader;
        };
        match declaration {
            HeaderDeclaration::Use(_) => {}
            HeaderDeclaration::OperatorHeader(_) => {}
        }
    };

    HeaderDiscovery {
        coverage: 0..input.pos(),
        stop,
        imports,
        operators,
    }
}

fn at_header_statement_start(line: LineState) -> bool {
    line.at_line_start && line.line_indent == 0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dispatches_use_and_operator_header_starters_but_stops_at_binding() {
        let use_only = discover_header("use std::data\n");
        let operator_only = discover_header("infix (<+>) 50 51 =");
        let mixed = discover_header("use std::data\ninfix (<+>) 50 51 =");
        let binding = discover_header("my value = 1\nuse std::data\n");

        assert_eq!(use_only.stop(), HeaderStop::Eof);
        assert_eq!(use_only.coverage(), &(0..14));
        assert!(use_only.imports().is_empty());
        assert!(use_only.operators().is_empty());
        assert_eq!(operator_only.stop(), HeaderStop::Eof);
        assert_eq!(operator_only.coverage(), &(0..19));
        assert!(operator_only.imports().is_empty());
        assert!(operator_only.operators().is_empty());
        assert_eq!(mixed.stop(), HeaderStop::Eof);
        assert_eq!(mixed.coverage(), &(0..33));
        assert_eq!(binding.stop(), HeaderStop::FirstNonHeader);
        assert_eq!(binding.coverage(), &(0..0));
    }
}
