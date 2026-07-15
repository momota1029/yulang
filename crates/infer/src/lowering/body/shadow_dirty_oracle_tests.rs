use super::*;

use super::stage0_tests::{fixture_source, repository_std_loaded, root_value_def};
use crate::analysis::with_shadow_dirty_oracle_for_new_sessions;

#[test]
fn shadow_dirty_oracle_characterizes_yumark_and_repository_std_owner_checks() {
    let cases = [
        ShadowOracleCase::fixture(
            "markdown",
            "std_prefix_yumark_markdown_workload.yu",
            Some("proof"),
            Some("render_markdown_doc"),
        ),
        ShadowOracleCase::fixture(
            "html",
            "std_prefix_yumark_html_fallback.yu",
            Some("proof"),
            Some("render_html_doc"),
        ),
        ShadowOracleCase {
            name: "repository-std-only",
            source: "use std::prelude::*\nmod std;\n".to_string(),
            target: None,
            workload_owner_label: None,
        },
    ];

    for case in cases {
        let loaded = repository_std_loaded(&case.source);
        let output = with_shadow_dirty_oracle_for_new_sessions(|| {
            lower_loaded_files(&loaded).expect("lower shadow dirty oracle fixture")
        });
        assert!(
            output.errors.is_empty(),
            "{}: {:?}",
            case.name,
            output.errors
        );
        let report = output
            .session
            .shadow_dirty_oracle_report()
            .expect("fixture lowering session must carry the enabled oracle");
        assert_eq!(
            report.predicted_clean + report.predicted_dirty,
            report.owner_checks,
            "{}",
            case.name
        );
        assert!(report.owner_checks > 0, "{}", case.name);
        assert!(report.predicted_clean > 0, "{}", case.name);
        assert_eq!(
            report.root_available_predicted_clean + report.root_available_predicted_dirty,
            report.root_available_checks,
            "{}",
            case.name
        );

        let target = case.target.map(|name| {
            let def = root_value_def(&output.modules, name);
            (def, report.owner(def).cloned())
        });
        let workload_owner = case.workload_owner_label.and_then(|label| {
            report
                .owners
                .iter()
                .find(|owner| output.labels.def_label(owner.owner) == Some(label))
                .cloned()
                .or_else(|| {
                    report
                        .owners
                        .iter()
                        .find(|owner| {
                            output
                                .labels
                                .def_label(owner.owner)
                                .is_some_and(|owner_label| owner_label.ends_with(label))
                        })
                        .cloned()
                })
        });
        if case.workload_owner_label.is_some() {
            assert!(
                workload_owner.is_some(),
                "{} workload owner must be observed",
                case.name
            );
        }
        eprintln!(
            "shadow dirty oracle {}: passes={}, owner-checks={}, clean={}/{} ({:.2}%), root-available-clean={}/{} ({:.2}%), target={:?}, workload-owner={:?}, mismatches={:?}",
            case.name,
            report.forced_passes,
            report.owner_checks,
            report.predicted_clean,
            report.owner_checks,
            percentage(report.predicted_clean, report.owner_checks),
            report.root_available_predicted_clean,
            report.root_available_checks,
            percentage(
                report.root_available_predicted_clean,
                report.root_available_checks,
            ),
            target,
            workload_owner,
            report.mismatches,
        );
        assert!(
            report.mismatches.is_empty(),
            "{} clean prediction changed under the real solve: {:#?}",
            case.name,
            report.mismatches
        );
    }
}

struct ShadowOracleCase {
    name: &'static str,
    source: String,
    target: Option<&'static str>,
    workload_owner_label: Option<&'static str>,
}

impl ShadowOracleCase {
    fn fixture(
        name: &'static str,
        fixture: &str,
        target: Option<&'static str>,
        workload_owner_label: Option<&'static str>,
    ) -> Self {
        Self {
            name,
            source: fixture_source(fixture),
            target,
            workload_owner_label,
        }
    }
}

fn percentage(numerator: usize, denominator: usize) -> f64 {
    if denominator == 0 {
        return 0.0;
    }
    numerator as f64 * 100.0 / denominator as f64
}
