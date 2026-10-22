//! Constructor-owned positive RootComp certificates. Unknown inherited coverage
//! is retained; absence of a local certificate never proves nonprotection.
use super::{
    machine::{ExecutionOwner, InvocationDescriptor, ValueHandle},
    program::SourceSite,
};
use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};
use yu_hir::{
    HirParameterId,
    shadow::{LocalSourceParameter, SourceAnnotationValue, SourceEffectId},
};

#[derive(Clone)]
pub(super) struct RootCompSchema {
    pub lambda: SourceSite,
    pub formal: LocalSourceParameter,
}
impl RootCompSchema {
    /// Primitive completion permits the ground-result projection used by the
    /// original narrow protocol. This constructor retains that contract.
    pub fn from_parameter(lambda: &SourceSite, formal: &LocalSourceParameter) -> Option<Arc<Self>> {
        let annotation = formal.annotation.as_ref()?;
        if !matches!(annotation.ty.value, SourceAnnotationValue::Unit | SourceAnnotationValue::Int
            | SourceAnnotationValue::Bool | SourceAnnotationValue::Str)
        {
            return None;
        }
        Self::original_parameter(lambda, formal)
    }
    /// General RootComp entry requires completion to preserve the actual
    /// result view. The outer permission never supplies a future-result grant.
    pub fn from_parameter_with_result_view(
        lambda: &SourceSite,
        formal: &LocalSourceParameter,
    ) -> Option<Arc<Self>> {
        match formal.annotation.as_ref()?.ty.value {
            SourceAnnotationValue::Variable(_) | SourceAnnotationValue::Hole(_) | SourceAnnotationValue::Function { .. } | SourceAnnotationValue::Tuple(_) =>
                Self::original_parameter(lambda, formal),
            _ => Self::from_parameter(lambda, formal),
        }
    }
    fn original_parameter(lambda: &SourceSite, formal: &LocalSourceParameter) -> Option<Arc<Self>> {
        let annotation = formal.annotation.as_ref()?;
        if annotation.owner != lambda.source_root
            || formal.id.source_root() != &lambda.source_root
            || annotation.ty.effects.is_none()
        {
            return None;
        }
        Some(Arc::new(Self {
            lambda: lambda.clone(),
            formal: formal.clone(),
        }))
    }
}
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub(super) struct ViewHandle(usize);
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ReceiptHandle(usize);
#[derive(Clone, Copy)]
pub(super) struct ExecutionView {
    pub view: ViewHandle,
    pub receipt: ReceiptHandle,
    pub occurrence: usize,
}
#[derive(Clone)]
pub(super) struct Observation {
    execution: ExecutionView,
    observer: usize,
    event: usize,
}
struct View {
    value: ValueHandle,
    image: Option<usize>,
    // No current consumer interprets unknown coverage as a negative certificate.
    unknown: bool,
}
struct Image {
    boundary: usize,
    parent: Option<usize>,
}
struct Boundary {
    receiver: usize,
    schema: Arc<RootCompSchema>,
}
struct Receipt {
    owner: ExecutionOwner,
    view: ViewHandle,
    #[allow(
        dead_code,
        reason = "original executed read/entry source slot retained for correspondence"
    )]
    slot: SourceSite,
    formal: Option<HirParameterId>,
}
#[derive(Default)]
pub(super) struct Receiving {
    views: Vec<View>,
    images: Vec<Image>,
    boundaries: Vec<Boundary>,
    receipts: Vec<Receipt>,
    receipt_index: HashMap<(ExecutionOwner, ViewHandle, Option<HirParameterId>), ReceiptHandle>,
    next_observer: usize,
    executions: Vec<(ViewHandle, ReceiptHandle)>,
    #[cfg(test)]
    query_visits: std::cell::RefCell<Vec<usize>>,
}
impl Receiving {
    pub fn opaque(&mut self, value: ValueHandle) -> ViewHandle {
        let handle = ViewHandle(self.views.len());
        self.views.push(View {
            value,
            image: None,
            unknown: true,
        });
        handle
    }
    pub fn ground(&mut self, value: ValueHandle) -> ViewHandle {
        let handle = ViewHandle(self.views.len());
        self.views.push(View {
            value,
            image: None,
            unknown: false,
        });
        handle
    }
    /// The original direct formal-Name map is identity at RootComp; the new
    /// Delay has its own value identity and retains exactly that image dependency.
    pub fn delay(&mut self, value: ValueHandle, inherited: Option<ViewHandle>) -> ViewHandle {
        let handle = ViewHandle(self.views.len());
        let (image, unknown) = inherited
            .map(|view| {
                let view = &self.views[view.0];
                (view.image, view.unknown)
            })
            .unwrap_or((None, true));
        self.views.push(View {
            value,
            image,
            unknown,
        });
        handle
    }
    pub fn enter(
        &mut self,
        value: ValueHandle,
        inherited: ViewHandle,
        receiver: usize,
        schema: Arc<RootCompSchema>,
    ) -> ViewHandle {
        // A genuine Comp entry runs once per freshly minted invocation. Every
        // inherited image predates that entry, including captured older views.
        debug_assert!(
            self.boundaries
                .last()
                .is_none_or(|boundary| boundary.receiver < receiver)
        );
        debug_assert!(
            self.views[inherited.0]
                .image
                .is_none_or(
                    |image| self.boundaries[self.images[image].boundary].receiver < receiver
                )
        );
        let boundary = self.boundaries.len();
        self.boundaries.push(Boundary { receiver, schema });
        let image = self.images.len();
        self.images.push(Image {
            boundary,
            parent: self.views[inherited.0].image,
        });
        let view = ViewHandle(self.views.len());
        self.views.push(View {
            value,
            image: Some(image),
            unknown: self.views[inherited.0].unknown,
        });
        view
    }
    pub fn receipt(
        &mut self,
        owner: ExecutionOwner,
        view: ViewHandle,
        slot: &SourceSite,
        formal: Option<HirParameterId>,
    ) -> ReceiptHandle {
        let receipt = ReceiptHandle(self.receipts.len());
        // Index only genuine entry/read construction. Querying a view neither
        // creates a receipt nor changes any original receiver or source route.
        self.receipt_index
            .insert((owner, view, formal.clone()), receipt);
        self.receipts.push(Receipt {
            owner,
            view,
            slot: slot.clone(),
            formal,
        });
        receipt
    }
    pub fn matches_value(&self, view: ViewHandle, value: ValueHandle) -> bool {
        self.views[view.0].value == value
    }
    pub fn has_root(&self, view: ViewHandle) -> bool {
        self.views[view.0].image.is_some()
    }
    pub fn execution(&mut self, view: ViewHandle, receipt: ReceiptHandle) -> Option<ExecutionView> {
        if self.receipts.get(receipt.0)?.view != view {
            return None;
        }
        let occurrence = self.executions.len();
        self.executions.push((view, receipt));
        Some(ExecutionView {
            view,
            receipt,
            occurrence,
        })
    }
    fn authentic_execution(&self, execution: ExecutionView) -> bool {
        self.executions.get(execution.occurrence) == Some(&(execution.view, execution.receipt))
    }
    pub fn observe(
        &mut self,
        event: usize,
        executing: &[ExecutionView],
    ) -> Option<Vec<Observation>> {
        let mut observations = Vec::with_capacity(executing.len());
        for execution in executing {
            if !self.authentic_execution(*execution) {
                return None;
            }
            let observer = self.next_observer;
            self.next_observer = observer.checked_add(1)?;
            observations.push(Observation {
                execution: *execution,
                observer,
                event,
            });
        }
        Some(observations)
    }
    /// Positive disjunction only: any authentic local Grant suffices despite
    /// unknown older profiles. Historical observers/receipts need not stay active.
    pub fn local_grant(
        &self,
        observations: &[Observation],
        event: usize,
        owner: ExecutionOwner,
        invocations: &[InvocationDescriptor],
        family: &SourceEffectId,
    ) -> bool {
        #[cfg(test)]
        self.query_visits.borrow_mut().clear();
        let ExecutionOwner::Invocation(receiver) = owner else {
            return false;
        };
        // A resumed span may borrow an owner below its resumer. Activity is
        // exact live membership, independently of current executable attribution.
        if !invocations
            .get(receiver)
            .is_some_and(InvocationDescriptor::is_active)
        {
            return false;
        }
        let Ok(target) = self
            .boundaries
            .binary_search_by_key(&receiver, |boundary| boundary.receiver)
        else {
            return false;
        };
        let schema = &self.boundaries[target].schema;
        if !schema.formal.annotation.as_ref().is_some_and(|annotation| {
            annotation.owner == schema.lambda.source_root
                && annotation
                    .ty
                    .effects
                    .as_ref()
                    .is_some_and(|row| row.concrete.contains(family))
        }) {
            return false;
        }
        // Each Invoke constructs at most one boundary; receivers are minted in
        // increasing order, and an entry's inherited image already exists. Thus
        // boundary receivers are unique/ordered and image parents are older.
        // This set memoizes image reachability only after receipt authentication,
        // never a negative Grant verdict tied to a mismatching receipt/formal.
        let mut visited = HashSet::new();
        for observation in observations {
            if observation.event != event
                || observation.observer >= self.next_observer
                || !self.authentic_execution(observation.execution)
            {
                continue;
            }
            let observing_receipt = &self.receipts[observation.execution.receipt.0];
            if observing_receipt.view != observation.execution.view {
                continue;
            }
            // Observe may run in a helper that has since unwound. The source
            // Path joins ANY genuine candidate-owner receipt of this exact view,
            // not necessarily the receipt that opened the observing execution.
            let view = observation.execution.view;
            let candidate = self.receipt_index.get(&(owner, view, None)).or_else(|| {
                self.receipt_index
                    .get(&(owner, view, Some(schema.formal.id.clone())))
            });
            let Some(candidate) = candidate.map(|receipt| &self.receipts[receipt.0]) else {
                continue;
            };
            if candidate.owner != owner
                || candidate.view != view
                || candidate
                    .formal
                    .as_ref()
                    .is_some_and(|formal| *formal != schema.formal.id)
            {
                continue;
            }
            let mut image = self.views[view.0].image;
            while let Some(index) = image {
                if !visited.insert(index) {
                    break;
                }
                #[cfg(test)]
                self.query_visits.borrow_mut().push(index);
                let node = &self.images[index];
                let boundary = &self.boundaries[node.boundary];
                if boundary.receiver == receiver {
                    return true;
                }
                if boundary.receiver < receiver {
                    break;
                }
                image = node.parent;
            }
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::runtime::{RuntimeEvidence, RuntimeOutcome, RuntimeProgram};
    use yu_hir::shadow::{LocalSourceForm, lower_module_with_local_source};
    use yu_hir::{FileId, FileKey, HirItem, ModuleIdentity, SemanticImports};
    use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

    fn source_operands() -> (
        Arc<RootCompSchema>,
        Arc<RootCompSchema>,
        SourceEffectId,
        ValueHandle,
    ) {
        let text: Arc<SourceText> = Arc::from(
            "act io:\n    our tick: int -> int\nmy first (input:[io] int) = input\nmy second (different:[io] int) = different\nmy main = 0",
        );
        let parsed = parse_file(
            text.clone(),
            Arc::new(scan_header(text)),
            Arc::new(SyntaxEnvironment::empty()),
        );
        assert!(parsed.syntax_diagnostics().unwrap().is_empty());
        let hir = Arc::new(
            lower_module_with_local_source(
                ModuleIdentity::source_root(FileId::new(FileKey::new(
                    "receiving-cost",
                    "schema.yu",
                ))),
                &parsed,
                SemanticImports::empty(),
            )
            .unwrap(),
        );
        let family = hir.source_effect_declarations()[0].id.clone();
        let mut schemas = Vec::new();
        for item in hir.items() {
            let HirItem::Binding(binding) = item else {
                continue;
            };
            let local = hir
                .local_source(binding.definition_root())
                .unwrap()
                .unwrap();
            for expression in local.expressions() {
                if let LocalSourceForm::Lambda { parameter, .. } = &expression.form {
                    schemas.push(
                        RootCompSchema::from_parameter(
                            &SourceSite {
                                source_root: yu_hir::SourceRootId::Definition(
                                    binding.definition_root().clone(),
                                ),
                                occurrence: expression.occurrence.clone(),
                                range: expression.range.clone(),
                            },
                            parameter,
                        )
                        .unwrap(),
                    );
                }
            }
        }
        let program = RuntimeProgram::from_hir(hir, RuntimeEvidence::default()).unwrap();
        let roots = program.execution_roots().unwrap();
        let mut machine = program
            .start(program.definition_named("main").unwrap(), &roots)
            .unwrap();
        let RuntimeOutcome::Completed(value) = machine.run(100) else {
            panic!("ground source value");
        };
        (schemas[0].clone(), schemas[1].clone(), family, value)
    }

    #[test]
    fn primitive_schema_matcher_preserves_outer_effect_and_source_owner_guards() {
        let (schema, different, _, _) = source_operands();
        let mut formal = schema.formal.clone();
        for value in [
            SourceAnnotationValue::Unit,
            SourceAnnotationValue::Int,
            SourceAnnotationValue::Bool,
            SourceAnnotationValue::Str,
        ] {
            formal.annotation.as_mut().unwrap().ty.value = value;
            assert!(RootCompSchema::from_parameter(&schema.lambda, &formal).is_some());
        }
        let ty = schema.formal.annotation.as_ref().unwrap().ty.clone();
        for value in [
            SourceAnnotationValue::Variable("a".into()),
            SourceAnnotationValue::Function {
                argument: Box::new(ty.clone()),
                result: Box::new(ty),
            },
        ] {
            formal.annotation.as_mut().unwrap().ty.value = value;
            assert!(RootCompSchema::from_parameter(&schema.lambda, &formal).is_none());
        }
        let mut formal = schema.formal.clone();
        formal.annotation.as_mut().unwrap().ty.effects = None;
        assert!(RootCompSchema::from_parameter(&schema.lambda, &formal).is_none());
        let mut formal = schema.formal.clone();
        formal.annotation.as_mut().unwrap().owner = different.lambda.source_root.clone();
        assert!(RootCompSchema::from_parameter(&schema.lambda, &formal).is_none());
        assert!(RootCompSchema::from_parameter(&different.lambda, &schema.formal).is_none());
        let mut formal = different.formal.clone();
        formal.annotation.as_mut().unwrap().owner = schema.lambda.source_root.clone();
        assert!(RootCompSchema::from_parameter(&schema.lambda, &formal).is_none());
        let mut formal = schema.formal.clone();
        formal.annotation = None;
        assert!(RootCompSchema::from_parameter(&schema.lambda, &formal).is_none());
    }

    #[test]
    fn actual_result_view_schema_keeps_source_guards_for_symbolic_and_function_results() {
        let (schema, different, _, _) = source_operands();
        let ty = schema.formal.annotation.as_ref().unwrap().ty.clone();
        for value in [
            SourceAnnotationValue::Variable("a".into()),
            SourceAnnotationValue::Hole(schema.formal.annotation.as_ref().unwrap().position.clone()),
            SourceAnnotationValue::Function { argument: Box::new(ty.clone()), result: Box::new(ty.clone()) },
        ] {
            let mut formal = schema.formal.clone();
            formal.annotation.as_mut().unwrap().ty.value = value;
            assert!(RootCompSchema::from_parameter(&schema.lambda, &formal).is_none(),
                "the original ground-completion constructor retains its own contract");
            let retained = RootCompSchema::from_parameter_with_result_view(&schema.lambda, &formal).unwrap();
            assert_eq!(retained.formal.id, formal.id);
            assert_eq!(retained.formal.source, formal.source);
            assert_eq!(retained.lambda.occurrence, schema.lambda.occurrence);
            let original = formal.annotation.as_ref().unwrap();
            let actual = retained.formal.annotation.as_ref().unwrap();
            assert_eq!(actual.owner, original.owner);
            assert_eq!(actual.position, original.position);
            assert_eq!(actual.ty.effects.as_ref().unwrap().position, original.ty.effects.as_ref().unwrap().position);
            assert_eq!(actual.ty.effects.as_ref().unwrap().concrete, original.ty.effects.as_ref().unwrap().concrete);
            assert_eq!(actual.ty.effects.as_ref().unwrap().variables, original.ty.effects.as_ref().unwrap().variables);
            assert!(RootCompSchema::from_parameter_with_result_view(&different.lambda, &formal).is_none());
            let mut wrong = formal.clone();
            wrong.annotation.as_mut().unwrap().owner = different.lambda.source_root.clone();
            assert!(RootCompSchema::from_parameter_with_result_view(&schema.lambda, &wrong).is_none());
            let mut wrong = formal.clone();
            wrong.annotation.as_mut().unwrap().ty.effects = None;
            assert!(RootCompSchema::from_parameter_with_result_view(&schema.lambda, &wrong).is_none());
            let mut wrong = different.formal.clone();
            wrong.annotation = formal.annotation.clone();
            assert!(RootCompSchema::from_parameter_with_result_view(&schema.lambda, &wrong).is_none());
            formal.annotation = None;
            assert!(RootCompSchema::from_parameter_with_result_view(&schema.lambda, &formal).is_none());
        }
    }

    fn assert_constructor_order(receiving: &Receiving) {
        assert!(
            receiving
                .boundaries
                .windows(2)
                .all(|pair| pair[0].receiver < pair[1].receiver)
        );
        for (index, image) in receiving.images.iter().enumerate() {
            if let Some(parent) = image.parent {
                assert!(parent < index);
                assert!(
                    receiving.boundaries[receiving.images[parent].boundary].receiver
                        < receiving.boundaries[image.boundary].receiver
                );
            }
        }
    }

    fn query_inventory(receiving: &Receiving, observations: &[Observation]) -> HashSet<usize> {
        let mut reachable = HashSet::new();
        for observation in observations {
            let mut image = receiving.views[observation.execution.view.0].image;
            while let Some(index) = image {
                if !reachable.insert(index) {
                    break;
                }
                image = receiving.images[index].parent;
            }
        }
        reachable
    }

    // Direct positive relation before the shared-ancestry optimization: every
    // authenticated observation independently asks for its target boundary.
    fn reference_grant(
        receiving: &Receiving,
        observations: &[Observation],
        event: usize,
        owner: usize,
        family: &SourceEffectId,
    ) -> bool {
        observations.iter().any(|observation| {
            if observation.event != event
                || observation.observer >= receiving.next_observer
                || !receiving.authentic_execution(observation.execution)
            {
                return false;
            }
            let observing_receipt = &receiving.receipts[observation.execution.receipt.0];
            if observing_receipt.view != observation.execution.view {
                return false;
            }
            let mut image = receiving.views[observation.execution.view.0].image;
            while let Some(index) = image {
                let node = &receiving.images[index];
                let boundary = &receiving.boundaries[node.boundary];
                if boundary.receiver == owner
                    && receiving.receipts.iter().any(|candidate| {
                        candidate.owner == ExecutionOwner::Invocation(owner)
                            && candidate.view == observation.execution.view
                            && candidate
                                .formal
                                .as_ref()
                                .is_none_or(|formal| *formal == boundary.schema.formal.id)
                    })
                    && boundary
                        .schema
                        .formal
                        .annotation
                        .as_ref()
                        .unwrap()
                        .ty
                        .effects
                        .as_ref()
                        .unwrap()
                        .concrete
                        .contains(family)
                {
                    return true;
                }
                image = node.parent;
            }
            false
        })
    }

    fn assert_query_work(receiving: &Receiving, observations: &[Observation]) {
        let reachable = query_inventory(receiving, observations);
        let visits = receiving.query_visits.borrow();
        let distinct = visits.iter().copied().collect::<HashSet<_>>();
        assert_eq!(
            visits.len(),
            distinct.len(),
            "one examination per image per query"
        );
        assert!(distinct.is_subset(&reachable));
        assert!(visits.len() <= reachable.len());
    }

    #[test]
    fn shared_negative_ancestry_is_examined_once_per_query() {
        let (schema, _, family, value) = source_operands();
        for depth in [16, 32] {
            let mut receiving = Receiving::default();
            let base = receiving.opaque(value);
            // Target exists, but its image is deliberately absent from every
            // queried root. Retained inventory is larger than query inventory.
            receiving.enter(value, base, 0, schema.clone());
            let mut view = base;
            let mut views = Vec::new();
            for receiver in 1..=depth {
                view = receiving.enter(value, view, receiver, schema.clone());
                views.push(view);
            }
            let executions = views
                .into_iter()
                .rev()
                .map(|view| {
                    let receipt = receiving.receipt(
                        ExecutionOwner::Invocation(0),
                        view,
                        &schema.lambda,
                        None,
                    );
                    receiving.execution(view, receipt).unwrap()
                })
                .collect::<Vec<_>>();
            let observations = receiving.observe(1, &executions).unwrap();
            assert_constructor_order(&receiving);
            assert_eq!(query_inventory(&receiving, &observations).len(), depth);
            let expected = reference_grant(&receiving, &observations, 1, 0, &family);
            assert!(!expected);
            assert_eq!(
                receiving.local_grant(
                    &observations,
                    1,
                    ExecutionOwner::Invocation(0),
                    &[InvocationDescriptor::active_for_test(schema.lambda.clone())],
                    &family
                ),
                expected
            );
            assert_query_work(&receiving, &observations);
        }
    }

    #[test]
    fn wrong_formal_receipt_cannot_poison_shared_positive_ancestry() {
        let (schema, different, family, value) = source_operands();
        for depth in [16, 32] {
            let mut receiving = Receiving::default();
            let base = receiving.opaque(value);
            let mut view = receiving.enter(value, base, 0, schema.clone());
            for receiver in 1..=depth {
                view = receiving.enter(value, view, receiver, schema.clone());
            }
            let wrong = receiving.receipt(
                ExecutionOwner::Invocation(0),
                view,
                &different.lambda,
                Some(different.formal.id.clone()),
            );
            // Another exact view shares the image. Its candidate-owner receipt
            // is genuine, while its observing read belongs to an expired helper.
            // The first view has only a wrong-formal candidate receipt, so its
            // failed join must not poison shared image reachability.
            let forwarded = receiving.delay(value, Some(view));
            receiving.receipt(
                ExecutionOwner::Invocation(0),
                forwarded,
                &schema.lambda,
                None,
            );
            let observing = receiving.receipt(
                ExecutionOwner::Invocation(depth + 1),
                forwarded,
                &schema.lambda,
                None,
            );
            let first_execution = receiving.execution(view, wrong).unwrap();
            let second_execution = receiving.execution(forwarded, observing).unwrap();
            let observations = receiving
                .observe(2, &[first_execution, second_execution])
                .unwrap();
            assert_constructor_order(&receiving);
            assert_eq!(query_inventory(&receiving, &observations).len(), depth + 1);
            let expected = reference_grant(&receiving, &observations, 2, 0, &family);
            assert!(expected);
            assert_eq!(
                receiving.local_grant(
                    &observations,
                    2,
                    ExecutionOwner::Invocation(0),
                    &[InvocationDescriptor::active_for_test(schema.lambda.clone())],
                    &family
                ),
                expected
            );
            assert_query_work(&receiving, &observations);
        }
    }
}
