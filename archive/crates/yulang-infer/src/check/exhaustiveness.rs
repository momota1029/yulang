use std::collections::{HashMap, HashSet};

use rowan::TextRange;

use crate::lower::{
    CaseArmPattern, CaseCheckSite, CatchArmCheckKind, CatchArmCheckSite, CatchCheckSite, FileSpan,
    LowerState,
};
use crate::symbols::{Name, Path};

use super::report::CheckReportBuilder;
use super::{DiagnosticCode, RelatedDiagnostic};

pub(crate) fn push_exhaustiveness(builder: &mut CheckReportBuilder, state: &LowerState) {
    for site in &state.case_check_sites {
        for diagnostic in unreachable_case_arm_diagnostics(state, site) {
            builder.push_with_file_span(
                DiagnosticCode::UnreachablePattern,
                diagnostic.message,
                Some(diagnostic.span),
                diagnostic.file_span,
                diagnostic.related,
            );
        }

        let Some(diagnostic) = case_exhaustiveness_diagnostic(state, site) else {
            continue;
        };
        builder.push_with_file_span(
            DiagnosticCode::NonExhaustivePattern,
            diagnostic.message,
            Some(site.span),
            site.file_span,
            diagnostic.related,
        );
    }

    for site in &state.catch_check_sites {
        for diagnostic in unreachable_catch_arm_diagnostics(site) {
            builder.push_with_file_span(
                DiagnosticCode::UnreachablePattern,
                diagnostic.message,
                Some(diagnostic.span),
                diagnostic.file_span,
                diagnostic.related,
            );
        }
    }
}

struct UnreachableArmDiagnostic {
    span: TextRange,
    file_span: Option<FileSpan>,
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
                file_span: arm.file_span,
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
    covers_all_span: Option<RecordedArmSpan>,
    enum_variants: HashMap<Path, HashMap<Name, RecordedArmSpan>>,
}

enum UnreachableReason {
    CoveredByWildcard {
        span: RecordedArmSpan,
    },
    CoveredByEnumVariants {
        spans: Vec<RecordedArmSpan>,
    },
    CoveredByCompleteEnum {
        enum_path: Path,
        spans: Vec<RecordedArmSpan>,
    },
}

#[derive(Debug, Clone, Copy)]
struct RecordedArmSpan {
    range: TextRange,
    file_span: Option<FileSpan>,
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
                    self.covers_all_span.get_or_insert(recorded_arm_span(arm));
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
                        .or_insert(recorded_arm_span(arm));
                }
                CaseArmPattern::EnumVariant { .. } => {}
            }
        }
    }

    fn covered_variant_span(&self, pattern: &CaseArmPattern) -> Option<RecordedArmSpan> {
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
                span: Some(span.range),
                file_span: span.file_span,
            }],
            UnreachableReason::CoveredByEnumVariants { spans } => spans
                .into_iter()
                .map(|span| RelatedDiagnostic {
                    message: "previous arm already covers this pattern".to_string(),
                    span: Some(span.range),
                    file_span: span.file_span,
                })
                .collect(),
            UnreachableReason::CoveredByCompleteEnum { enum_path, spans } => {
                let mut related = spans
                    .into_iter()
                    .map(|span| RelatedDiagnostic {
                        message: "previous arm covers one variant of this enum".to_string(),
                        span: Some(span.range),
                        file_span: span.file_span,
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

fn recorded_arm_span(arm: &crate::lower::CaseArmCheckSite) -> RecordedArmSpan {
    RecordedArmSpan {
        range: arm.span,
        file_span: arm.file_span,
    }
}

fn recorded_catch_arm_span(arm: &CatchArmCheckSite) -> RecordedArmSpan {
    RecordedArmSpan {
        range: arm.span,
        file_span: arm.file_span,
    }
}

fn unreachable_catch_arm_diagnostics(site: &CatchCheckSite) -> Vec<UnreachableArmDiagnostic> {
    let mut covered = PriorCatchCoverage::default();
    let mut diagnostics = Vec::new();

    for arm in &site.arms {
        if let Some(reason) = covered.unreachable_reason(arm) {
            diagnostics.push(UnreachableArmDiagnostic {
                span: arm.span,
                file_span: arm.file_span,
                message: "catch arm is unreachable".to_string(),
                related: reason.related(),
            });
        }
        if arm.active && arm.guard_span.is_none() {
            covered.record_unconditional_arm(arm);
        }
    }

    diagnostics
}

#[derive(Default)]
struct PriorCatchCoverage {
    value_covers_all_span: Option<RecordedArmSpan>,
    effect_ops: HashMap<Path, RecordedArmSpan>,
}

enum CatchUnreachableReason {
    CoveredByValueArm { span: RecordedArmSpan },
    CoveredByEffectArm { span: RecordedArmSpan },
}

impl PriorCatchCoverage {
    fn unreachable_reason(&self, arm: &CatchArmCheckSite) -> Option<CatchUnreachableReason> {
        if !arm.active {
            return None;
        }
        match &arm.kind {
            CatchArmCheckKind::Value { .. } => self
                .value_covers_all_span
                .map(|span| CatchUnreachableReason::CoveredByValueArm { span }),
            CatchArmCheckKind::Effect { op_path, .. } => self
                .effect_ops
                .get(op_path)
                .copied()
                .map(|span| CatchUnreachableReason::CoveredByEffectArm { span }),
        }
    }

    fn record_unconditional_arm(&mut self, arm: &CatchArmCheckSite) {
        match &arm.kind {
            CatchArmCheckKind::Value {
                pattern_covers_all, ..
            } if *pattern_covers_all => {
                self.value_covers_all_span
                    .get_or_insert(recorded_catch_arm_span(arm));
            }
            CatchArmCheckKind::Effect {
                op_path,
                payload_covers_all,
                ..
            } if *payload_covers_all => {
                self.effect_ops
                    .entry(op_path.clone())
                    .or_insert(recorded_catch_arm_span(arm));
            }
            CatchArmCheckKind::Value { .. } | CatchArmCheckKind::Effect { .. } => {}
        }
    }
}

impl CatchUnreachableReason {
    fn related(self) -> Vec<RelatedDiagnostic> {
        match self {
            CatchUnreachableReason::CoveredByValueArm { span } => vec![RelatedDiagnostic {
                message: "previous value arm covers all normal completions".to_string(),
                span: Some(span.range),
                file_span: span.file_span,
            }],
            CatchUnreachableReason::CoveredByEffectArm { span } => vec![RelatedDiagnostic {
                message: "previous effect arm already handles this operation".to_string(),
                span: Some(span.range),
                file_span: span.file_span,
            }],
        }
    }
}

fn case_exhaustiveness_diagnostic(
    state: &LowerState,
    site: &CaseCheckSite,
) -> Option<CaseExhaustivenessDiagnostic> {
    let coverage = collect_enum_case_coverage(site)?;
    let declared = case_exhaustiveness_domain(state, site, &coverage)?;
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

fn case_exhaustiveness_domain(
    state: &LowerState,
    site: &CaseCheckSite,
    coverage: &EnumCaseCoverage,
) -> Option<Vec<Name>> {
    if let Some(CaseArmPattern::EnumVariant {
        enum_path, variant, ..
    }) = &site.scrutinee
        && enum_path == &coverage.enum_path
    {
        return Some(vec![variant.clone()]);
    }
    state
        .enum_variants_by_enum_path
        .get(&coverage.enum_path)
        .cloned()
}

struct EnumCaseCoverage {
    enum_path: Path,
    covered: HashSet<Name>,
    guarded: Vec<GuardedVariant>,
}

struct GuardedVariant {
    variant: Name,
    arm_span: TextRange,
    file_span: Option<FileSpan>,
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
                    file_span: arm.file_span,
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
            file_span: guarded.file_span,
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
