//! Selected imported syntax inputs and their dependency provenance.

use std::{ops::Range, sync::Arc};

use crate::{
    OperatorFixity,
    operator_table::{OperatorOrigin, OperatorTable},
};

/// Syntax facts selected for one full parse.
#[derive(Clone, Debug)]
pub struct SyntaxEnvironment {
    key: SyntaxEnvironmentKey,
    operators: Arc<OperatorTable>,
    provenance: Arc<[SyntaxDependencyProvenance]>,
}

impl SyntaxEnvironment {
    /// Construct an environment with no imported dynamic operators.
    pub fn empty() -> Self {
        Self {
            key: SyntaxEnvironmentKey::EMPTY,
            operators: Arc::new(OperatorTable::empty()),
            provenance: Arc::from([]),
        }
    }

    /// Validates and stores the imported-only syntax facts selected for one consumer file.
    pub fn from_imported(
        key: SyntaxEnvironmentKey,
        operators: Arc<OperatorTable>,
        provenance: Arc<[SyntaxDependencyProvenance]>,
    ) -> Result<Self, SyntaxEnvironmentBuildError> {
        for (entry, sites) in operators.entries_with_sites() {
            for fixity in [
                OperatorFixity::Prefix,
                OperatorFixity::Infix,
                OperatorFixity::Suffix,
                OperatorFixity::Nullfix,
            ] {
                let Some(site) = sites.site(fixity) else {
                    continue;
                };
                match site.origin() {
                    OperatorOrigin::Local => {
                        return Err(
                            SyntaxEnvironmentBuildError::ImportedTableContainsLocalOrigin {
                                spelling: entry.spelling().into(),
                                fixity,
                                range: site.range().clone(),
                            },
                        );
                    }
                    OperatorOrigin::Imported(dependency)
                        if provenance.get(dependency.index()).is_none() =>
                    {
                        return Err(SyntaxEnvironmentBuildError::MissingDependencyProvenance {
                            spelling: entry.spelling().into(),
                            fixity,
                            dependency,
                            range: site.range().clone(),
                        });
                    }
                    OperatorOrigin::Imported(_) => {}
                }
            }
        }

        Ok(Self {
            key,
            operators,
            provenance,
        })
    }

    pub fn key(&self) -> SyntaxEnvironmentKey {
        self.key
    }

    pub fn operators(&self) -> &OperatorTable {
        &self.operators
    }

    pub fn provenance(&self) -> &[SyntaxDependencyProvenance] {
        &self.provenance
    }

    pub fn dependency(&self, slot: SyntaxDependencySlot) -> Option<&SyntaxDependencyProvenance> {
        self.provenance.get(slot.index())
    }
}

impl Default for SyntaxEnvironment {
    fn default() -> Self {
        Self::empty()
    }
}

/// Opaque identity of the syntax inputs selected for a parse.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct SyntaxEnvironmentKey(u64);

impl SyntaxEnvironmentKey {
    pub const EMPTY: Self = Self(0);

    #[cfg(test)]
    pub(crate) const fn from_raw(value: u64) -> Self {
        Self(value)
    }
}

/// Environment-local ordinal identifying a syntax dependency provenance record.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct SyntaxDependencySlot(u32);

impl SyntaxDependencySlot {
    pub fn from_index(index: usize) -> Option<Self> {
        u32::try_from(index).ok().map(Self)
    }

    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// Provenance for one syntax dependency selected by syntax planning.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SyntaxDependencyProvenance {
    module_label: Arc<str>,
    revision: SourceRevision,
}

impl SyntaxDependencyProvenance {
    pub fn new(module_label: Arc<str>, revision: SourceRevision) -> Self {
        Self {
            module_label,
            revision,
        }
    }

    pub fn module_label(&self) -> &str {
        &self.module_label
    }

    pub fn revision(&self) -> SourceRevision {
        self.revision
    }
}

/// Rejection from the imported syntax-environment construction boundary.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SyntaxEnvironmentBuildError {
    ImportedTableContainsLocalOrigin {
        spelling: Box<str>,
        fixity: OperatorFixity,
        range: Range<usize>,
    },
    MissingDependencyProvenance {
        spelling: Box<str>,
        fixity: OperatorFixity,
        dependency: SyntaxDependencySlot,
        range: Range<usize>,
    },
}

/// Identity of the source snapshot represented by a phase product.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct SourceRevision(u64);

impl SourceRevision {
    /// Placeholder used until revision allocation is owned by compiler queries.
    pub const UNTRACKED: Self = Self(0);
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::{
        BindingPower as HeaderBindingPower, BindingPowers, HeaderOperator, Visibility,
        operator_compilation::compile_full_parse_operators,
        operator_table::{BindingPower, OperatorDeclaration, OperatorFixities},
    };

    #[test]
    fn imported_environment_rejects_a_full_table_with_local_sites() {
        let operators = Arc::new(
            OperatorTable::from_declarations([OperatorDeclaration::at_range(
                "+",
                OperatorFixities::new()
                    .with_prefix(crate::operator_table::BindingPower::scalar(70)),
                4..12,
            )])
            .expect("local full table should build"),
        );

        let error =
            SyntaxEnvironment::from_imported(SyntaxEnvironmentKey(1), operators, Arc::from([]))
                .expect_err("a different file's full table must not become imported input");

        assert_eq!(
            error,
            SyntaxEnvironmentBuildError::ImportedTableContainsLocalOrigin {
                spelling: "+".into(),
                fixity: OperatorFixity::Prefix,
                range: 4..12,
            }
        );
    }

    #[test]
    fn imported_environment_rejects_an_out_of_range_dependency_slot() {
        let missing_dependency = SyntaxDependencySlot::from_index(1).expect("slot fits");
        let operators = Arc::new(
            OperatorTable::from_declarations([OperatorDeclaration::imported_at_range(
                "+",
                OperatorFixities::new()
                    .with_prefix(crate::operator_table::BindingPower::scalar(70)),
                missing_dependency,
                4..12,
            )])
            .expect("imported table should build"),
        );
        let provenance = Arc::from([SyntaxDependencyProvenance::new(
            Arc::from("dependency"),
            SourceRevision::UNTRACKED,
        )]);

        let error =
            SyntaxEnvironment::from_imported(SyntaxEnvironmentKey(1), operators, provenance)
                .expect_err("missing dependency provenance must be rejected");

        assert_eq!(
            error,
            SyntaxEnvironmentBuildError::MissingDependencyProvenance {
                spelling: "+".into(),
                fixity: OperatorFixity::Prefix,
                dependency: missing_dependency,
                range: 4..12,
            }
        );
    }

    #[test]
    fn imported_environment_keeps_received_arcs_and_unused_provenance() {
        let operators = Arc::new(OperatorTable::empty());
        let provenance = Arc::from([SyntaxDependencyProvenance::new(
            Arc::from("dependency without operators"),
            SourceRevision::UNTRACKED,
        )]);

        let environment = SyntaxEnvironment::from_imported(
            SyntaxEnvironmentKey(1),
            Arc::clone(&operators),
            Arc::clone(&provenance),
        )
        .expect("unused dependency provenance is valid");

        assert!(Arc::ptr_eq(&operators, &environment.operators));
        assert!(Arc::ptr_eq(&provenance, &environment.provenance));
        assert_eq!(
            environment
                .dependency(SyntaxDependencySlot::from_index(0).expect("first slot fits"))
                .expect("stored dependency")
                .module_label(),
            "dependency without operators"
        );
    }

    #[test]
    fn full_parse_merge_does_not_mutate_environment_operator_sites() {
        let dependency = SyntaxDependencySlot::from_index(0).expect("first slot fits");
        let operators = Arc::new(
            OperatorTable::from_declarations([OperatorDeclaration::imported_at_range(
                "+",
                OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
                dependency,
                4..12,
            )])
            .expect("imported table should build"),
        );
        let provenance = Arc::from([SyntaxDependencyProvenance::new(
            Arc::from("dependency"),
            SourceRevision::UNTRACKED,
        )]);
        let environment = SyntaxEnvironment::from_imported(
            SyntaxEnvironmentKey(1),
            Arc::clone(&operators),
            provenance,
        )
        .expect("validated imported environment");
        let (_, before_sites) = environment
            .operators()
            .entries_with_sites()
            .next()
            .expect("imported entry");
        let before_prefix = before_sites
            .site(OperatorFixity::Prefix)
            .cloned()
            .expect("imported prefix site");
        let local = [HeaderOperator::new(
            20..36,
            "+".to_owned(),
            OperatorFixity::Infix,
            Visibility::Private,
            false,
            BindingPowers::infix(
                HeaderBindingPower::from_components([40]),
                HeaderBindingPower::from_components([41]),
            ),
        )];

        let merged = compile_full_parse_operators(environment.operators(), &local)
            .expect("merge builds a separate full parse table");

        assert!(Arc::ptr_eq(&operators, &environment.operators));
        let (_, after_sites) = environment
            .operators()
            .entries_with_sites()
            .next()
            .expect("imported entry remains unchanged");
        assert_eq!(
            after_sites.site(OperatorFixity::Prefix),
            Some(&before_prefix)
        );
        assert!(after_sites.site(OperatorFixity::Infix).is_none());
        assert!(
            merged
                .get("+")
                .expect("merged entry")
                .fixities()
                .infix()
                .is_some()
        );
    }
}
