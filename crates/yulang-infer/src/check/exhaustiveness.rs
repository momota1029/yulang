use std::collections::HashSet;

use rowan::TextRange;

use crate::lower::{CaseArmPattern, CaseCheckSite, LowerState};
use crate::symbols::{Name, Path};

use super::report::CheckReportBuilder;
use super::{DiagnosticCode, RelatedDiagnostic};

pub(crate) fn push_case_exhaustiveness(builder: &mut CheckReportBuilder, state: &LowerState) {
    for site in &state.case_check_sites {
        let Some(diagnostic) = case_exhaustiveness_diagnostic(state, site) else {
            continue;
        };
        builder.push(
            DiagnosticCode::NonExhaustivePattern,
            diagnostic.message,
            Some(site.span),
            diagnostic.related,
        );
    }
}

struct CaseExhaustivenessDiagnostic {
    message: String,
    related: Vec<RelatedDiagnostic>,
}

fn case_exhaustiveness_diagnostic(
    state: &LowerState,
    site: &CaseCheckSite,
) -> Option<CaseExhaustivenessDiagnostic> {
    let coverage = collect_enum_case_coverage(site)?;
    let declared = state.enum_variants_by_enum_path.get(&coverage.enum_path)?;
    if declared.is_empty() {
        return None;
    }

    let missing = declared
        .iter()
        .filter(|variant| !coverage.covered.contains(*variant))
        .cloned()
        .collect::<Vec<_>>();
    if missing.is_empty() {
        return None;
    }

    Some(CaseExhaustivenessDiagnostic {
        message: missing_variants_message(&coverage.enum_path, &missing),
        related: guarded_variant_related(&missing, &coverage.guarded),
    })
}

struct EnumCaseCoverage {
    enum_path: Path,
    covered: HashSet<Name>,
    guarded: Vec<GuardedVariant>,
}

struct GuardedVariant {
    variant: Name,
    arm_span: TextRange,
}

fn collect_enum_case_coverage(site: &CaseCheckSite) -> Option<EnumCaseCoverage> {
    let mut enum_path = None;
    let mut covered = HashSet::new();
    let mut guarded = Vec::new();

    for arm in &site.arms {
        if !arm.guarded
            && arm
                .patterns
                .iter()
                .any(|pattern| matches!(pattern, CaseArmPattern::CoversAll))
        {
            return None;
        }

        for pattern in &arm.patterns {
            let CaseArmPattern::EnumVariant {
                enum_path: pattern_enum_path,
                variant,
            } = pattern
            else {
                continue;
            };
            match &enum_path {
                Some(enum_path) if enum_path != pattern_enum_path => return None,
                Some(_) => {}
                None => enum_path = Some(pattern_enum_path.clone()),
            }
            if arm.guarded {
                guarded.push(GuardedVariant {
                    variant: variant.clone(),
                    arm_span: arm.span,
                });
            } else {
                covered.insert(variant.clone());
            }
        }
    }

    Some(EnumCaseCoverage {
        enum_path: enum_path?,
        covered,
        guarded,
    })
}

fn missing_variants_message(enum_path: &Path, missing: &[Name]) -> String {
    let variants = missing
        .iter()
        .map(|variant| format!("`{}`", format_variant_path(enum_path, variant)))
        .collect::<Vec<_>>()
        .join(", ");
    if missing.len() == 1 {
        format!("case is not exhaustive: missing {variants}")
    } else {
        format!("case is not exhaustive: missing cases {variants}")
    }
}

fn guarded_variant_related(missing: &[Name], guarded: &[GuardedVariant]) -> Vec<RelatedDiagnostic> {
    guarded
        .iter()
        .filter(|guarded| missing.contains(&guarded.variant))
        .map(|guarded| RelatedDiagnostic {
            message: "guarded arm does not prove this variant is covered".to_string(),
            span: Some(guarded.arm_span),
            file_span: None,
        })
        .collect()
}

fn format_variant_path(enum_path: &Path, variant: &Name) -> String {
    let mut segments = enum_path
        .segments
        .iter()
        .map(|segment| segment.0.as_str())
        .collect::<Vec<_>>();
    segments.push(variant.0.as_str());
    segments.join("::")
}
