//! Compile imported and source-header operator declarations into a full-parse table.

use std::ops::Range;

use crate::{
    BindingPower as HeaderBindingPower, HeaderOperator,
    operator_table::{
        BindingPower, OperatorDeclaration, OperatorFixities, OperatorFixity, OperatorOrigin,
        OperatorTable, OperatorTableBuildError, OperatorTableBuilder,
    },
};

/// Compiles the immutable full-parse table without modifying the imported table.
#[cfg(test)]
pub(crate) fn compile_full_parse_operators(
    imported: &OperatorTable,
    local: &[HeaderOperator],
) -> Result<OperatorTable, OperatorTableBuildError> {
    let mut builder = OperatorTableBuilder::default();
    seed_imported(&mut builder, imported)?;
    builder.extend(local.iter().cloned().map(from_header_operator))?;
    Ok(builder.build())
}

/// The deterministic, degraded full-parse table and every rejected duplicate
/// capability encountered while building it.
pub(crate) struct FullParseOperatorCompilation {
    pub(crate) table: OperatorTable,
    pub(crate) rejected_conflicts: Vec<RejectedOperatorFixity>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct RejectedOperatorFixity {
    pub(crate) spelling: Box<str>,
    pub(crate) fixity: OperatorFixity,
    pub(crate) first_origin: OperatorOrigin,
    pub(crate) first_range: Range<usize>,
    pub(crate) second_origin: OperatorOrigin,
    pub(crate) second_range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum FullParseOperatorConstructionError {
    EmptySpelling {
        origin: OperatorOrigin,
        range: Range<usize>,
    },
}

/// Compiles the full-parse table in one builder pass, retaining the first
/// accepted capability for a duplicate fixity and recording the rejected one.
pub(crate) fn compile_full_parse_operators_recovering(
    imported: &OperatorTable,
    local: &[HeaderOperator],
) -> Result<FullParseOperatorCompilation, FullParseOperatorConstructionError> {
    let mut builder = OperatorTableBuilder::default();
    let mut rejected_conflicts = Vec::new();

    for (entry, sites) in imported.entries_with_sites() {
        for fixity in [
            OperatorFixity::Prefix,
            OperatorFixity::Infix,
            OperatorFixity::Suffix,
            OperatorFixity::Nullfix,
        ] {
            let Some(site) = sites.site(fixity) else {
                continue;
            };
            merge_full_parse_operator_recovering(
                &mut builder,
                OperatorDeclaration::from_site(
                    entry.spelling(),
                    fixities_for(entry.fixities(), fixity),
                    site,
                ),
                &mut rejected_conflicts,
            )?;
        }
    }
    for header in local.iter().cloned() {
        merge_full_parse_operator_recovering(
            &mut builder,
            from_header_operator(header),
            &mut rejected_conflicts,
        )?;
    }

    Ok(FullParseOperatorCompilation {
        table: builder.build(),
        rejected_conflicts,
    })
}

fn merge_full_parse_operator_recovering(
    builder: &mut OperatorTableBuilder,
    declaration: OperatorDeclaration,
    rejected_conflicts: &mut Vec<RejectedOperatorFixity>,
) -> Result<(), FullParseOperatorConstructionError> {
    let origin = declaration.origin();
    match builder.merge(declaration) {
        Ok(()) => Ok(()),
        Err(OperatorTableBuildError::ConflictingFixity {
            spelling,
            fixity,
            first_origin,
            first_range,
            second_origin,
            second_range,
        }) => {
            rejected_conflicts.push(RejectedOperatorFixity {
                spelling,
                fixity,
                first_origin,
                first_range,
                second_origin,
                second_range,
            });
            Ok(())
        }
        Err(OperatorTableBuildError::EmptySpelling { range }) => {
            Err(FullParseOperatorConstructionError::EmptySpelling { origin, range })
        }
    }
}

/// Compiles declaration-local header facts into spelling-level fixities.
#[cfg(test)]
pub(crate) fn from_header_operators(
    operators: impl IntoIterator<Item = HeaderOperator>,
) -> Result<OperatorTable, OperatorTableBuildError> {
    OperatorTable::from_declarations(operators.into_iter().map(from_header_operator))
}

fn from_header_operator(header: HeaderOperator) -> OperatorDeclaration {
    let fixities = match header.fixity() {
        OperatorFixity::Prefix => OperatorFixities::new().with_prefix(binding_power_from_header(
            header
                .binding_power()
                .right()
                .expect("prefix header facts require a right binding power"),
        )),
        OperatorFixity::Infix => OperatorFixities::new().with_infix(
            binding_power_from_header(
                header
                    .binding_power()
                    .left()
                    .expect("infix header facts require a left binding power"),
            ),
            binding_power_from_header(
                header
                    .binding_power()
                    .right()
                    .expect("infix header facts require a right binding power"),
            ),
        ),
        OperatorFixity::Suffix => OperatorFixities::new().with_suffix(binding_power_from_header(
            header
                .binding_power()
                .left()
                .expect("suffix header facts require a left binding power"),
        )),
        OperatorFixity::Nullfix => OperatorFixities::new().with_nullfix(),
    };
    OperatorDeclaration::at_range(header.name(), fixities, header.range().clone())
}

fn binding_power_from_header(power: &HeaderBindingPower) -> BindingPower {
    let (first, rest) = power
        .components()
        .split_first()
        .expect("header binding powers are never empty");
    BindingPower::new(*first, rest.iter().copied())
}

#[cfg(test)]
fn seed_imported(
    builder: &mut OperatorTableBuilder,
    imported: &OperatorTable,
) -> Result<(), OperatorTableBuildError> {
    for (entry, sites) in imported.entries_with_sites() {
        for fixity in [
            OperatorFixity::Prefix,
            OperatorFixity::Infix,
            OperatorFixity::Suffix,
            OperatorFixity::Nullfix,
        ] {
            let Some(site) = sites.site(fixity) else {
                continue;
            };
            let fixities = fixities_for(entry.fixities(), fixity);
            builder.merge(OperatorDeclaration::from_site(
                entry.spelling(),
                fixities,
                site,
            ))?;
        }
    }
    Ok(())
}

fn fixities_for(fixities: &OperatorFixities, fixity: OperatorFixity) -> OperatorFixities {
    match fixity {
        OperatorFixity::Prefix => OperatorFixities::new().with_prefix(
            fixities
                .prefix()
                .expect("operator site and fixity presence must agree")
                .right_binding_power()
                .clone(),
        ),
        OperatorFixity::Infix => {
            let infix = fixities
                .infix()
                .expect("operator site and fixity presence must agree");
            OperatorFixities::new().with_infix(
                infix.left_binding_power().clone(),
                infix.right_binding_power().clone(),
            )
        }
        OperatorFixity::Suffix => OperatorFixities::new().with_suffix(
            fixities
                .suffix()
                .expect("operator site and fixity presence must agree")
                .left_binding_power()
                .clone(),
        ),
        OperatorFixity::Nullfix => OperatorFixities::new().with_nullfix(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BindingPowers, SyntaxDependencySlot, Visibility, operator_table::OperatorKindSet};

    #[test]
    fn compiles_separate_header_declarations_into_one_full_fixity_entry() {
        let headers = [
            HeaderOperator::new(
                0..20,
                "..".to_owned(),
                OperatorFixity::Nullfix,
                Visibility::Public,
                false,
                BindingPowers::nullfix(),
            ),
            HeaderOperator::new(
                21..48,
                "..".to_owned(),
                OperatorFixity::Prefix,
                Visibility::Public,
                false,
                BindingPowers::prefix(HeaderBindingPower::from_components([8, 0, 0])),
            ),
            HeaderOperator::new(
                49..76,
                "..".to_owned(),
                OperatorFixity::Suffix,
                Visibility::Public,
                false,
                BindingPowers::suffix(HeaderBindingPower::from_components([8, 0, 0])),
            ),
            HeaderOperator::new(
                77..112,
                "..".to_owned(),
                OperatorFixity::Infix,
                Visibility::Public,
                false,
                BindingPowers::infix(
                    HeaderBindingPower::from_components([4, 0, 0]),
                    HeaderBindingPower::from_components([4, 0, 1]),
                ),
            ),
        ];

        let table = from_header_operators(headers)
            .expect("distinct fixities for one spelling should aggregate");
        let entry = table.get("..").expect("aggregated spelling should exist");
        assert!(entry.fixities().kinds().contains(
            OperatorKindSet::PREFIX
                | OperatorKindSet::INFIX
                | OperatorKindSet::SUFFIX
                | OperatorKindSet::NULLFIX
        ));
        assert_eq!(
            entry
                .fixities()
                .infix()
                .expect("infix capability")
                .right_binding_power()
                .components(),
            &[4, 0, 1]
        );
    }

    #[test]
    fn full_parse_merge_preserves_imported_sites_and_adds_local_fixities() {
        let dependency = SyntaxDependencySlot::from_index(0).expect("first slot fits");
        let imported = OperatorTable::from_declarations([OperatorDeclaration::imported_at_range(
            "<+>",
            OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
            dependency,
            8..21,
        )])
        .expect("imported prefix should build");
        let local = [HeaderOperator::new(
            30..48,
            "<+>".to_owned(),
            OperatorFixity::Infix,
            Visibility::Private,
            false,
            BindingPowers::infix(
                HeaderBindingPower::from_components([40]),
                HeaderBindingPower::from_components([41]),
            ),
        )];

        let merged = compile_full_parse_operators(&imported, &local)
            .expect("distinct imported and local fixities should aggregate");
        let entry = merged.get("<+>").expect("merged spelling should exist");
        assert_eq!(
            entry
                .fixities()
                .prefix()
                .expect("imported prefix")
                .right_binding_power(),
            &BindingPower::scalar(70)
        );
        assert_eq!(
            entry
                .fixities()
                .infix()
                .expect("local infix")
                .left_binding_power(),
            &BindingPower::scalar(40)
        );

        let (_, sites) = merged
            .entries_with_sites()
            .next()
            .expect("one merged entry");
        assert_eq!(
            sites
                .site(OperatorFixity::Prefix)
                .map(|site| (site.origin(), site.range().clone())),
            Some((OperatorOrigin::Imported(dependency), 8..21))
        );
        assert_eq!(
            sites
                .site(OperatorFixity::Infix)
                .map(|site| (site.origin(), site.range().clone())),
            Some((OperatorOrigin::Local, 30..48))
        );

        let (_, imported_sites) = imported
            .entries_with_sites()
            .next()
            .expect("imported entry remains available");
        assert_eq!(
            imported_sites
                .site(OperatorFixity::Prefix)
                .map(|site| (site.origin(), site.range().clone())),
            Some((OperatorOrigin::Imported(dependency), 8..21))
        );
        assert!(imported_sites.site(OperatorFixity::Infix).is_none());
    }

    #[test]
    fn full_parse_merge_reports_imported_fixity_before_local_conflict() {
        let dependency = SyntaxDependencySlot::from_index(0).expect("first slot fits");
        let imported = OperatorTable::from_declarations([OperatorDeclaration::imported_at_range(
            "<+>",
            OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
            dependency,
            8..21,
        )])
        .expect("imported prefix should build");
        let local = [HeaderOperator::new(
            30..47,
            "<+>".to_owned(),
            OperatorFixity::Prefix,
            Visibility::Private,
            false,
            BindingPowers::prefix(HeaderBindingPower::from_components([71])),
        )];

        let error = compile_full_parse_operators(&imported, &local)
            .expect_err("same fixity must retain imported declaration as first conflict");
        assert_eq!(
            error,
            OperatorTableBuildError::ConflictingFixity {
                spelling: "<+>".into(),
                fixity: OperatorFixity::Prefix,
                first_origin: OperatorOrigin::Imported(dependency),
                first_range: 8..21,
                second_origin: OperatorOrigin::Local,
                second_range: 30..47,
            }
        );
    }

    #[test]
    fn recovering_full_parse_merge_retains_first_local_fixity_and_later_capabilities() {
        let local = [
            HeaderOperator::new(
                0..15,
                "+".to_owned(),
                OperatorFixity::Prefix,
                Visibility::Private,
                false,
                BindingPowers::prefix(HeaderBindingPower::from_components([70])),
            ),
            HeaderOperator::new(
                16..31,
                "+".to_owned(),
                OperatorFixity::Prefix,
                Visibility::Private,
                false,
                BindingPowers::prefix(HeaderBindingPower::from_components([71])),
            ),
            HeaderOperator::new(
                32..49,
                "+".to_owned(),
                OperatorFixity::Infix,
                Visibility::Private,
                false,
                BindingPowers::infix(
                    HeaderBindingPower::from_components([40]),
                    HeaderBindingPower::from_components([41]),
                ),
            ),
        ];

        let compilation = compile_full_parse_operators_recovering(&OperatorTable::empty(), &local)
            .expect("duplicate fixity is recoverable");
        let entry = compilation.table.get("+").expect("accepted spelling");
        assert_eq!(
            entry
                .fixities()
                .prefix()
                .expect("first prefix remains accepted")
                .right_binding_power(),
            &BindingPower::scalar(70)
        );
        assert!(entry.fixities().infix().is_some());
        assert_eq!(
            compilation.rejected_conflicts,
            [RejectedOperatorFixity {
                spelling: "+".into(),
                fixity: OperatorFixity::Prefix,
                first_origin: OperatorOrigin::Local,
                first_range: 0..15,
                second_origin: OperatorOrigin::Local,
                second_range: 16..31,
            }]
        );
    }

    #[test]
    fn recovering_full_parse_merge_retains_imported_first_fixity() {
        let dependency = SyntaxDependencySlot::from_index(0).expect("slot fits");
        let imported = OperatorTable::from_declarations([OperatorDeclaration::imported_at_range(
            "+",
            OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
            dependency,
            4..18,
        )])
        .expect("imported table");
        let local = [HeaderOperator::new(
            20..35,
            "+".to_owned(),
            OperatorFixity::Prefix,
            Visibility::Private,
            false,
            BindingPowers::prefix(HeaderBindingPower::from_components([71])),
        )];

        let compilation = compile_full_parse_operators_recovering(&imported, &local)
            .expect("duplicate fixity is recoverable");
        assert_eq!(
            compilation.rejected_conflicts[0].first_origin,
            OperatorOrigin::Imported(dependency)
        );
        assert_eq!(compilation.rejected_conflicts[0].first_range, 4..18);
        assert_eq!(compilation.rejected_conflicts[0].second_range, 20..35);
    }
}
