use std::collections::{HashMap, HashSet};

use rowan::TextRange;

use crate::lower::{CaseArmPattern, CaseCheckSite, LowerState};
use crate::symbols::{Name, Path};

use super::report::CheckReportBuilder;
use super::{DiagnosticCode, RelatedDiagnostic};

pub(crate) fn push_case_exhaustiveness(builder: &mut CheckReportBuilder, state: &LowerState) {
    for site in &state.case_check_sites {
        for diagnostic in unreachable_case_arm_diagnostics(state, site) {
            builder.push(
                DiagnosticCode::UnreachablePattern,
                diagnostic.message,
                Some(diagnostic.span),
                diagnostic.related,
            );
        }

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

struct UnreachableArmDiagnostic {
    span: TextRange,
    message: String,
    related: Vec<RelatedDiagnostic>,
}

struct CaseExhaustivenessDiagnostic {
    message: String,
    related: Vec<RelatedDiagnostic>,
}

fn unreachable_case_arm_diagnostics(
    state: &LowerState,
    site: &CaseCheckSite,
) -> Vec<UnreachableArmDiagnostic> {
    let mut covered = PriorCaseCoverage::default();
    let mut diagnostics = Vec::new();

    for arm in &site.arms {
        if let Some(reason) = covered.unreachable_reason(state, arm) {
            diagnostics.push(UnreachableArmDiagnostic {
                span: arm.span,
                message: "case arm is unreachable".to_string(),
                related: reason.related(),
            });
        }
        if !arm.guarded {
            covered.record_unconditional_arm(arm);
        }
    }

    diagnostics
}

#[derive(Default)]
struct PriorCaseCoverage {
    covers_all_span: Option<TextRange>,
    enum_variants: HashMap<Path, HashMap<Name, TextRange>>,
}

enum UnreachableReason {
    CoveredByWildcard {
        span: TextRange,
    },
    CoveredByEnumVariants {
        spans: Vec<TextRange>,
    },
    CoveredByCompleteEnum {
        enum_path: Path,
        spans: Vec<TextRange>,
    },
}

impl PriorCaseCoverage {
    fn unreachable_reason(
        &self,
        state: &LowerState,
        arm: &crate::lower::CaseArmCheckSite,
    ) -> Option<UnreachableReason> {
        if let Some(span) = self.covers_all_span {
            return Some(UnreachableReason::CoveredByWildcard { span });
        }
        if arm.patterns.is_empty() {
            return None;
        }
        if arm
            .patterns
            .iter()
            .any(|pattern| matches!(pattern, CaseArmPattern::CoversAll))
        {
            return self.complete_enum_reason(state);
        }
        let covered_spans = arm
            .patterns
            .iter()
            .map(|pattern| self.covered_variant_span(pattern))
            .collect::<Option<Vec<_>>>()?;
        if covered_spans.is_empty() {
            None
        } else {
            Some(UnreachableReason::CoveredByEnumVariants {
                spans: covered_spans,
            })
        }
    }

    fn record_unconditional_arm(&mut self, arm: &crate::lower::CaseArmCheckSite) {
        for pattern in &arm.patterns {
            match pattern {
                CaseArmPattern::CoversAll => {
                    self.covers_all_span.get_or_insert(arm.span);
                }
                CaseArmPattern::EnumVariant {
                    enum_path,
                    variant,
                    payload_covers_all,
                } if *payload_covers_all => {
                    self.enum_variants
                        .entry(enum_path.clone())
                        .or_default()
                        .entry(variant.clone())
                        .or_insert(arm.span);
                }
                CaseArmPattern::EnumVariant { .. } => {}
            }
        }
    }

    fn covered_variant_span(&self, pattern: &CaseArmPattern) -> Option<TextRange> {
        let CaseArmPattern::EnumVariant {
            enum_path, variant, ..
        } = pattern
        else {
            return None;
        };
        self.enum_variants.get(enum_path)?.get(variant).copied()
    }

    fn complete_enum_reason(&self, state: &LowerState) -> Option<UnreachableReason> {
        let mut complete_enums = self
            .enum_variants
            .iter()
            .filter_map(|(enum_path, covered)| {
                let declared = state.enum_variants_by_enum_path.get(enum_path)?;
                (!declared.is_empty()
                    && declared.iter().all(|variant| covered.contains_key(variant)))
                .then(|| {
                    let spans = declared
                        .iter()
                        .filter_map(|variant| covered.get(variant).copied())
                        .collect::<Vec<_>>();
                    (enum_path.clone(), spans)
                })
            });
        let first = complete_enums.next()?;
        if complete_enums.next().is_some() {
            return None;
        }
        Some(UnreachableReason::CoveredByCompleteEnum {
            enum_path: first.0,
            spans: first.1,
        })
    }
}

impl UnreachableReason {
    fn related(self) -> Vec<RelatedDiagnostic> {
        match self {
            UnreachableReason::CoveredByWildcard { span } => vec![RelatedDiagnostic {
                message: "previous arm covers all remaining inputs".to_string(),
                span: Some(span),
                file_span: None,
            }],
            UnreachableReason::CoveredByEnumVariants { spans } => spans
                .into_iter()
                .map(|span| RelatedDiagnostic {
                    message: "previous arm already covers this pattern".to_string(),
                    span: Some(span),
                    file_span: None,
                })
                .collect(),
            UnreachableReason::CoveredByCompleteEnum { enum_path, spans } => {
                let mut related = spans
                    .into_iter()
                    .map(|span| RelatedDiagnostic {
                        message: "previous arm covers one variant of this enum".to_string(),
                        span: Some(span),
                        file_span: None,
                    })
                    .collect::<Vec<_>>();
                related.push(RelatedDiagnostic {
                    message: format!(
                        "previous arms already cover all variants of `{}`",
                        format_path(&enum_path)
                    ),
                    span: None,
                    file_span: None,
                });
                related
            }
        }
    }
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
                payload_covers_all,
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
            } else if *payload_covers_all {
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

fn format_path(path: &Path) -> String {
    path.segments
        .iter()
        .map(|segment| segment.0.as_str())
        .collect::<Vec<_>>()
        .join("::")
}
