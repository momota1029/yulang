//! Immutable constraint collection from resolved HIR.

use std::sync::Arc;

#[cfg(test)]
use std::{cell::RefCell, rc::Rc};

use yu_hir::{DefId, HirBinding, HirExprId, HirItem, HirModule, NameResolution, ResolvedExpr};
use yu_types::CanonicalType;

#[cfg(test)]
macro_rules! count_collection {
    ($field:ident += $value:expr) => {
        COLLECTION_COUNTERS.with(|active| {
            if let Some(counters) = active.borrow().as_ref() {
                counters.borrow_mut().$field += $value;
            }
        });
    };
}

#[cfg(not(test))]
macro_rules! count_collection {
    ($field:ident += $value:expr) => {};
}

/// One immutable, source-ordered collection of HIR type constraints.
#[derive(Debug)]
pub struct ConstraintBatch {
    module: Arc<HirModule>,
    constraints: Vec<Constraint>,
}

impl ConstraintBatch {
    /// Collects the first-slice constraints while retaining the exact input module.
    pub fn collect(module: Arc<HirModule>) -> Self {
        Self::collect_impl(module)
    }

    pub fn module(&self) -> &Arc<HirModule> {
        &self.module
    }

    pub fn constraints(&self) -> &[Constraint] {
        &self.constraints
    }

    fn collect_impl(module: Arc<HirModule>) -> Self {
        let mut constraints = Vec::new();
        for item in module.items() {
            count_collection!(item_visits += 1);
            match item {
                HirItem::Binding(binding) => collect_binding(binding, &mut constraints),
                HirItem::Expression(expression) => collect_expression(expression, &mut constraints),
                HirItem::Error { .. } => {}
            }
        }
        Self {
            module,
            constraints,
        }
    }
}

/// A normalized equality emitted during constraint collection.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Constraint {
    left: TypeTerm,
    right: TypeTerm,
    origin: ConstraintOrigin,
}

impl Constraint {
    pub fn left(&self) -> &TypeTerm {
        &self.left
    }

    pub fn right(&self) -> &TypeTerm {
        &self.right
    }

    pub fn origin(&self) -> &ConstraintOrigin {
        &self.origin
    }
}

/// One term in a first-slice type equality.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum TypeTerm {
    Expression(HirExprId),
    Definition(DefId),
    Canonical(CanonicalType),
}

/// The occurrence responsible for one emitted equality.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ConstraintOrigin {
    Expression(HirExprId),
    Definition(DefId),
}

fn collect_binding(binding: &HirBinding, constraints: &mut Vec<Constraint>) {
    let expression = binding.value();
    if !matches!(
        expression,
        ResolvedExpr::Integer { .. }
            | ResolvedExpr::Name {
                resolution: NameResolution::Resolved(_),
                ..
            }
    ) {
        return;
    }
    constraints.push(Constraint {
        left: TypeTerm::Definition(binding.id().clone()),
        right: TypeTerm::Expression(expression.id()),
        origin: ConstraintOrigin::Definition(binding.id().clone()),
    });
    collect_expression(expression, constraints);
}

fn collect_expression(expression: &ResolvedExpr, constraints: &mut Vec<Constraint>) {
    match expression {
        ResolvedExpr::Integer { id, .. } => constraints.push(Constraint {
            left: TypeTerm::Expression(*id),
            right: TypeTerm::Canonical(CanonicalType::Int),
            origin: ConstraintOrigin::Expression(*id),
        }),
        ResolvedExpr::Name {
            id,
            resolution: NameResolution::Resolved(definition),
            ..
        } => constraints.push(Constraint {
            left: TypeTerm::Expression(*id),
            right: TypeTerm::Definition(definition.clone()),
            origin: ConstraintOrigin::Expression(*id),
        }),
        ResolvedExpr::Name { .. } | ResolvedExpr::Error { .. } => {}
    }
}

#[cfg(test)]
#[derive(Default)]
struct CollectionCounters {
    item_visits: usize,
}

#[cfg(test)]
thread_local! {
    static COLLECTION_COUNTERS: RefCell<Option<Rc<RefCell<CollectionCounters>>>> = const { RefCell::new(None) };
}

#[cfg(test)]
struct CollectionCounterScope {
    previous: Option<Rc<RefCell<CollectionCounters>>>,
}

#[cfg(test)]
impl CollectionCounterScope {
    fn enter(counters: Rc<RefCell<CollectionCounters>>) -> Self {
        let previous = COLLECTION_COUNTERS.with(|active| active.replace(Some(counters)));
        Self { previous }
    }
}

#[cfg(test)]
impl Drop for CollectionCounterScope {
    fn drop(&mut self) {
        COLLECTION_COUNTERS.with(|active| {
            active.replace(self.previous.take());
        });
    }
}

#[cfg(test)]
fn collect_with_counters(module: Arc<HirModule>) -> (ConstraintBatch, CollectionCounters) {
    let counters = Rc::new(RefCell::new(CollectionCounters::default()));
    let scope = CollectionCounterScope::enter(Rc::clone(&counters));
    let batch = ConstraintBatch::collect_impl(module);
    drop(scope);
    let counters = Rc::into_inner(counters)
        .expect("the test-only counter scope releases its sole handle")
        .into_inner();
    (batch, counters)
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;
    use yu_hir::{FileId, FileKey, ModuleIdentity, SemanticImports, lower_module};
    use yu_syntax::{ParsedFile, SourceText, SyntaxEnvironment, parse_file, scan_header};

    fn parsed(source: &str) -> ParsedFile {
        let source: Arc<SourceText> = Arc::from(source);
        let header = Arc::new(scan_header(source.clone()));
        parse_file(source, header, Arc::new(SyntaxEnvironment::empty()))
    }

    fn module(source: &str) -> Arc<HirModule> {
        Arc::new(
            lower_module(
                ModuleIdentity::source_root(FileId::new(FileKey::new("test", "collect.yu"))),
                &parsed(source),
                SemanticImports::empty(),
            )
            .expect("first-slice HIR remains available"),
        )
    }

    #[test]
    fn collects_ordered_binding_and_intrinsic_occurrences() {
        let module = module("my x = 1; my y = x");
        let [HirItem::Binding(x), HirItem::Binding(y)] = module.items() else {
            panic!("two bindings");
        };
        let x_expression = x.value().id();
        let y_expression = y.value().id();

        let batch = ConstraintBatch::collect(Arc::clone(&module));
        assert_eq!(
            batch.constraints(),
            &[
                Constraint {
                    left: TypeTerm::Definition(x.id().clone()),
                    right: TypeTerm::Expression(x_expression),
                    origin: ConstraintOrigin::Definition(x.id().clone()),
                },
                Constraint {
                    left: TypeTerm::Expression(x_expression),
                    right: TypeTerm::Canonical(CanonicalType::Int),
                    origin: ConstraintOrigin::Expression(x_expression),
                },
                Constraint {
                    left: TypeTerm::Definition(y.id().clone()),
                    right: TypeTerm::Expression(y_expression),
                    origin: ConstraintOrigin::Definition(y.id().clone()),
                },
                Constraint {
                    left: TypeTerm::Expression(y_expression),
                    right: TypeTerm::Definition(x.id().clone()),
                    origin: ConstraintOrigin::Expression(y_expression),
                },
            ]
        );
    }

    #[test]
    fn retains_the_moved_input_arc_and_visits_items_once() {
        let input = module("1; my x = 2; missing; f 1");
        let expected = Arc::clone(&input);
        let (batch, counters) = collect_with_counters(input);

        assert!(Arc::ptr_eq(batch.module(), &expected));
        assert_eq!(Arc::strong_count(&expected), 2);
        assert_eq!(counters.item_visits, expected.items().len());
    }

    #[test]
    fn collects_resolved_direct_roots_without_binding_value_edges() {
        let module = module("x; my x = 1");
        let [HirItem::Expression(name), HirItem::Binding(binding)] = module.items() else {
            panic!("direct name before one binding");
        };
        let (name_id, definition) = match name {
            ResolvedExpr::Name { id, resolution, .. } => (*id, resolution.clone()),
            _ => panic!("direct root resolves as a name"),
        };
        let NameResolution::Resolved(definition) = definition else {
            panic!("direct root resolves uniquely");
        };
        let binding_id = binding.id().clone();
        let binding_expression = binding.value().id();

        let batch = ConstraintBatch::collect(module);
        assert_eq!(
            batch.constraints(),
            &[
                Constraint {
                    left: TypeTerm::Expression(name_id),
                    right: TypeTerm::Definition(definition.clone()),
                    origin: ConstraintOrigin::Expression(name_id),
                },
                Constraint {
                    left: TypeTerm::Definition(binding_id.clone()),
                    right: TypeTerm::Expression(binding_expression),
                    origin: ConstraintOrigin::Definition(binding_id),
                },
                Constraint {
                    left: TypeTerm::Expression(binding_expression),
                    right: TypeTerm::Canonical(CanonicalType::Int),
                    origin: ConstraintOrigin::Expression(binding_expression),
                },
            ]
        );
    }

    #[test]
    fn omits_error_unresolved_ambiguous_and_error_items_without_stopping() {
        let module = module("my x = 1; my x = 2; my y = x; my bad = @; missing; f 1; 42");
        let [
            HirItem::Binding(first_x),
            HirItem::Binding(second_x),
            HirItem::Binding(ambiguous_y),
            HirItem::Binding(omitted_bad),
            HirItem::Expression(unresolved),
            HirItem::Expression(error),
            HirItem::Expression(trailing_integer),
        ] = module.items()
        else {
            panic!("the omission fixture retains each independent later item")
        };
        assert!(matches!(
            ambiguous_y.value(),
            ResolvedExpr::Name {
                resolution: NameResolution::Ambiguous,
                ..
            }
        ));
        assert!(matches!(omitted_bad.value(), ResolvedExpr::Error { .. }));
        assert!(matches!(
            unresolved,
            ResolvedExpr::Name {
                resolution: NameResolution::Unresolved,
                ..
            }
        ));
        assert!(matches!(error, ResolvedExpr::Error { .. }));
        let ResolvedExpr::Integer {
            id: trailing_integer,
            ..
        } = trailing_integer
        else {
            panic!("the independent valid item remains collectable")
        };

        let batch = ConstraintBatch::collect(Arc::clone(&module));
        assert_eq!(
            batch.constraints(),
            &[
                Constraint {
                    left: TypeTerm::Definition(first_x.id().clone()),
                    right: TypeTerm::Expression(first_x.value().id()),
                    origin: ConstraintOrigin::Definition(first_x.id().clone()),
                },
                Constraint {
                    left: TypeTerm::Expression(first_x.value().id()),
                    right: TypeTerm::Canonical(CanonicalType::Int),
                    origin: ConstraintOrigin::Expression(first_x.value().id()),
                },
                Constraint {
                    left: TypeTerm::Definition(second_x.id().clone()),
                    right: TypeTerm::Expression(second_x.value().id()),
                    origin: ConstraintOrigin::Definition(second_x.id().clone()),
                },
                Constraint {
                    left: TypeTerm::Expression(second_x.value().id()),
                    right: TypeTerm::Canonical(CanonicalType::Int),
                    origin: ConstraintOrigin::Expression(second_x.value().id()),
                },
                Constraint {
                    left: TypeTerm::Expression(*trailing_integer),
                    right: TypeTerm::Canonical(CanonicalType::Int),
                    origin: ConstraintOrigin::Expression(*trailing_integer),
                },
            ]
        );
    }
}
