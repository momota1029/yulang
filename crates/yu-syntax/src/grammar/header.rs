//! Internal candidate for source-leading header discovery.
//!
//! This module deliberately shares declaration parsing with full mode while
//! feeding the public header-discovery entrypoint.

use std::ops::Range;

use chasa::{Back as _, input::IsCut, prelude::In};

use crate::{
    HeaderCoverage, HeaderImport, HeaderInfo, HeaderOperator, HeaderStop,
    input::SourceInput,
    scan::{opaque_body::scan_opaque_body, trivia::scan_trivia},
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
    pub(crate) fn into_header_info(self) -> HeaderInfo {
        HeaderInfo {
            coverage: HeaderCoverage {
                range: self.coverage,
                stop: self.stop,
            },
            imports: self.imports.into(),
            operators: self.operators.into(),
        }
    }

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
    let mut i = In::new(
        &mut source_input,
        &mut expectations,
        IsCut::new(&mut is_cut),
    )
    .set_local(&mut local);
    let mut imports = Vec::new();
    let mut operators = Vec::new();

    let stop = loop {
        i.run(scan_trivia).expect("trivia scanning is total");
        if i.input.remainder().is_empty() {
            break HeaderStop::Eof;
        }
        if !at_header_statement_start(i.local.line()) {
            break HeaderStop::FirstNonHeader;
        }

        let statement_start = i.checkpoint();
        let Some(declaration) = i.run(parse_header_declaration) else {
            i.rollback(statement_start);
            break HeaderStop::FirstNonHeader;
        };
        match declaration {
            HeaderDeclaration::Use(declaration) => {
                // Header facts are immutable planning input. Until diagnostics
                // can represent a branch-local expansion failure, do not
                // silently freeze a partial projection from one declaration.
                if let Ok(expanded) = declaration
                    .expand_header_imports()
                    .into_iter()
                    .collect::<Result<Vec<_>, _>>()
                {
                    imports.extend(expanded);
                }
            }
            HeaderDeclaration::OperatorHeader(declaration) => {
                operators.push(declaration.to_header_operator());
                i.run(scan_opaque_body)
                    .expect("opaque body scanning is total");
            }
        }
    };

    HeaderDiscovery {
        coverage: 0..i.pos(),
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
    use crate::HeaderImportForm;

    const LEADING_USE_FIXTURES: [(&[u8], HeaderImportForm, &[&str]); 4] = [
        (
            include_bytes!(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/../../tests/contracts/phase2-parser/v0/cases/leading-use-plain/main.yu"
            )),
            HeaderImportForm::Plain,
            &["std", "data"],
        ),
        (
            include_bytes!(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/../../tests/contracts/phase2-parser/v0/cases/leading-use-mod/main.yu"
            )),
            HeaderImportForm::Mod,
            &["math", "value"],
        ),
        (
            include_bytes!(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/../../tests/contracts/phase2-parser/v0/cases/leading-use-realm/main.yu"
            )),
            HeaderImportForm::Realm,
            &["tools", "format"],
        ),
        (
            include_bytes!(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/../../tests/contracts/phase2-parser/v0/cases/leading-use-band/main.yu"
            )),
            HeaderImportForm::Band,
            &["support", "value"],
        ),
    ];
    const INFIX_OPERATOR_SOURCE: &[u8] = include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../tests/contracts/phase2-parser/v0/cases/infix-operator-header/main.yu"
    ));
    const LATE_USE_SOURCE: &[u8] = include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../tests/contracts/phase2-parser/v0/cases/late-use-after-body/main.yu"
    ));

    #[test]
    fn dispatches_use_and_operator_header_starters_but_stops_at_binding() {
        let use_only = discover_header("use std::data\n");
        let operator_only = discover_header("infix (<+>) 50 51 =");
        let mixed = discover_header("use std::data\ninfix (<+>) 50 51 =");
        let binding = discover_header("my value = 1\nuse std::data\n");

        assert_eq!(use_only.stop(), HeaderStop::Eof);
        assert_eq!(use_only.coverage(), &(0..14));
        assert_eq!(use_only.imports().len(), 1);
        assert!(use_only.operators().is_empty());
        assert_eq!(operator_only.stop(), HeaderStop::Eof);
        assert_eq!(operator_only.coverage(), &(0..19));
        assert!(operator_only.imports().is_empty());
        assert_eq!(operator_only.operators().len(), 1);
        assert_eq!(mixed.stop(), HeaderStop::Eof);
        assert_eq!(mixed.coverage(), &(0..33));
        assert_eq!(binding.stop(), HeaderStop::FirstNonHeader);
        assert_eq!(binding.coverage(), &(0..0));
    }

    #[test]
    fn expands_complete_use_declarations_and_skips_an_invalid_one() {
        let source = "use std::io::{read, write}\nuse std::fmt::debug as log\nuse std::fs::{read as one as two}\nuse core::fmt\n";
        let header = discover_header(source);

        assert_eq!(header.stop(), HeaderStop::Eof);
        assert_eq!(header.coverage(), &(0..source.len()));
        assert_eq!(
            header
                .imports()
                .iter()
                .map(|import| import.path().join("::"))
                .collect::<Vec<_>>(),
            [
                "std::io::read",
                "std::io::write",
                "std::fmt::debug",
                "core::fmt",
            ]
        );
        assert_eq!(header.imports()[2].alias(), Some("log"));
        assert!(
            header
                .imports()
                .iter()
                .all(|import| import.path().join("::") != "std::fs::read")
        );
    }

    #[test]
    fn skips_an_operator_body_before_dispatching_the_next_header() {
        let source = "infix (<+>) 50 51 = {\n  \"{ not an outer delimiter }\"\n}\nuse std::data\nmy value = 1\n";
        let header = discover_header(source);
        let body_end = source.find("my value").expect("test has a body binding");

        assert_eq!(header.stop(), HeaderStop::FirstNonHeader);
        assert_eq!(header.coverage(), &(0..body_end));
        assert_eq!(header.operators().len(), 1);
        assert_eq!(header.operators()[0].name(), "<+>");
        assert_eq!(header.imports().len(), 1);
        assert_eq!(header.imports()[0].path(), ["std", "data"]);
    }

    #[test]
    fn projects_every_leading_use_fixture_with_its_form_and_route() {
        for (bytes, form, path) in LEADING_USE_FIXTURES {
            let source = std::str::from_utf8(bytes).expect("fixtures are UTF-8");
            let header = discover_header(source);
            let body_start = source.find("my value").expect("fixture has a body binding");

            assert_eq!(header.stop(), HeaderStop::FirstNonHeader, "{source}");
            assert_eq!(header.coverage(), &(0..body_start), "{source}");
            let [import] = header.imports() else {
                panic!("expected one import for fixture: {source}");
            };
            assert_eq!(import.form(), form, "{source}");
            assert_eq!(import.path(), path, "{source}");
            assert!(header.operators().is_empty(), "{source}");
        }
    }

    #[test]
    fn projects_the_infix_header_fixture_after_skipping_its_body() {
        let source = std::str::from_utf8(INFIX_OPERATOR_SOURCE).expect("fixture is UTF-8");
        let header = discover_header(source);
        let body_start = source.find("my value").expect("fixture has a body binding");

        assert_eq!(header.stop(), HeaderStop::FirstNonHeader);
        assert_eq!(header.coverage(), &(0..body_start));
        assert!(header.imports().is_empty());
        let [operator] = header.operators() else {
            panic!("expected one operator for fixture: {header:#?}");
        };
        assert_eq!(operator.name(), "<+>");
        assert_eq!(operator.range(), &(0..19));
    }

    #[test]
    fn expands_group_items_in_source_order() {
        let source = "use std::io::{read, nested::{write, flush}, close}\nmy value = 1\n";
        let header = discover_header(source);

        assert_eq!(header.stop(), HeaderStop::FirstNonHeader);
        assert_eq!(
            header
                .imports()
                .iter()
                .map(|import| import.path().join("::"))
                .collect::<Vec<_>>(),
            [
                "std::io::read",
                "std::io::nested::write",
                "std::io::nested::flush",
                "std::io::close",
            ]
        );
    }

    #[test]
    fn stops_before_a_late_use_in_the_body_fixture() {
        let source = std::str::from_utf8(LATE_USE_SOURCE).expect("fixture is UTF-8");
        let header = discover_header(source);
        let body_start = source.find("my value").expect("fixture has a body binding");

        assert_eq!(header.stop(), HeaderStop::FirstNonHeader);
        assert_eq!(header.coverage(), &(0..body_start));
        let [import] = header.imports() else {
            panic!("expected exactly one leading import: {header:#?}");
        };
        assert_eq!(import.path(), ["std", "data"]);
    }
}
