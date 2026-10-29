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

/// Source-owned permission on the result port of a Value callback. This
/// deliberately accepts only the reviewed `() -> [E] int` shape: the outer
/// function is a Value, while the resolved concrete row lives at Result.
#[derive(Clone)]
pub(super) struct CallbackResultSchema {
    pub lambda: SourceSite,
    pub formal: LocalSourceParameter,
    pub families: Arc<[SourceEffectId]>,
}
impl CallbackResultSchema {
    pub fn from_parameter(
        lambda: &SourceSite,
        formal: &LocalSourceParameter,
    ) -> Option<Arc<Self>> {
        let annotation = formal.annotation.as_ref()?;
        if annotation.owner != lambda.source_root
            || formal.id.source_root() != &lambda.source_root
            || annotation.ty.effects.is_some()
            || formal.unit_pattern
            || formal.record_pattern.is_some()
        {
            return None;
        }
        let SourceAnnotationValue::Function { argument, result } = &annotation.ty.value else {
            return None;
        };
        if argument.effects.is_some()
            || !matches!(argument.value, SourceAnnotationValue::Unit)
            || !matches!(result.value, SourceAnnotationValue::Int)
        {
            return None;
        }
        let row = result.effects.as_ref()?;
        if row.concrete.is_empty() || !row.variables.is_empty() {
            return None;
        }
        Some(Arc::new(Self {
            lambda: lambda.clone(),
            formal: formal.clone(),
            families: Arc::from(row.concrete.clone()),
        }))
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub(super) struct ViewHandle(usize);
impl ViewHandle {
    pub(super) fn index(self) -> usize { self.0 }
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ReceiptHandle(usize);
impl ReceiptHandle { pub(super) fn index(self) -> usize { self.0 } }
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub(super) struct CallbackEntryHandle(usize);
impl CallbackEntryHandle { pub(super) fn index(self) -> usize { self.0 } }
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub(super) struct CallbackUseHandle(usize);
impl CallbackUseHandle { pub(super) fn index(self) -> usize { self.0 } }
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
    kind: ViewKind,
}
#[derive(Clone, Copy)]
enum ViewKind {
    Ordinary,
    RootComp,
    CallbackEntry(CallbackEntryHandle),
    CallbackResult(CallbackUseHandle),
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
struct CallbackEntry {
    schema: Arc<CallbackResultSchema>,
    receiver: usize,
    value: ValueHandle,
    incoming_view: ViewHandle,
    view: ViewHandle,
    formal_receipt: ReceiptHandle,
}
struct CallbackUse {
    entry: CallbackEntryHandle,
    source_view: ViewHandle,
    apply: SourceSite,
    result_view: ViewHandle,
    receipt: ReceiptHandle,
}
#[derive(Default)]
pub(super) struct Receiving {
    views: Vec<View>,
    images: Vec<Image>,
    boundaries: Vec<Boundary>,
    receipts: Vec<Receipt>,
    receipt_index: HashMap<(ExecutionOwner, ViewHandle, Option<HirParameterId>), ReceiptHandle>,
    callback_entries: Vec<CallbackEntry>,
    callback_uses: Vec<CallbackUse>,
    next_observer: usize,
    executions: Vec<(ViewHandle, ReceiptHandle)>,
    #[cfg(test)]
    query_visits: std::cell::RefCell<Vec<usize>>,
}
impl Receiving {
    #[cfg(test)]
    pub(super) fn callback_entry_observation(
        &self,
        entry: CallbackEntryHandle,
    ) -> Option<(usize, HirParameterId, usize, usize, usize, usize, SourceSite, Vec<SourceEffectId>)> {
        let record = self.callback_entries.get(entry.0)?;
        Some((record.receiver, record.schema.formal.id.clone(), record.value.0,
            record.incoming_view.0, record.view.0, record.formal_receipt.0,
            record.schema.lambda.clone(), record.schema.families.to_vec()))
    }

    #[cfg(test)]
    pub(super) fn callback_use_observation(
        &self,
        use_handle: CallbackUseHandle,
    ) -> Option<(usize, usize, HirParameterId, usize, usize, usize, usize, SourceSite)> {
        let record = self.callback_uses.get(use_handle.0)?;
        let entry = self.callback_entries.get(record.entry.0)?;
        Some((record.entry.0, entry.receiver, entry.schema.formal.id.clone(), entry.value.0,
            record.source_view.0, record.result_view.0, record.receipt.0, record.apply.clone()))
    }

    #[cfg(test)]
    pub(super) fn callback_use_for_execution(&self, execution: &ExecutionView) -> Option<usize> {
        let ViewKind::CallbackResult(use_handle) = self.views.get(execution.view.0)?.kind else {
            return None;
        };
        let record = self.callback_uses.get(use_handle.0)?;
        (record.result_view == execution.view && record.receipt == execution.receipt)
            .then_some(use_handle.0)
    }

    #[cfg(test)]
    pub(super) fn root_entry_observation(
        &self,
        view: ViewHandle,
    ) -> Option<(usize, HirParameterId, usize, usize, usize, SourceSite, Vec<SourceEffectId>)> {
        let image = self.views.get(view.0)?.image?;
        let boundary = self.images.get(image)?.boundary;
        let record = self.boundaries.get(boundary)?;
        let receipt = self.receipt_index.get(&(
            ExecutionOwner::Invocation(record.receiver), view, Some(record.schema.formal.id.clone())
        ))?;
        Some((record.receiver, record.schema.formal.id.clone(), self.views[view.0].value.0,
            view.0, receipt.0, record.schema.lambda.clone(),
            record.schema.formal.annotation.as_ref()?.ty.effects.as_ref()?.concrete.clone()))
    }

    pub(super) fn next_receipt_index(&self) -> usize {
        self.receipts.len()
    }

    pub fn opaque(&mut self, value: ValueHandle) -> ViewHandle {
        let handle = ViewHandle(self.views.len());
        self.views.push(View {
            value,
            image: None,
            unknown: true,
            kind: ViewKind::Ordinary,
        });
        handle
    }
    pub fn ground(&mut self, value: ValueHandle) -> ViewHandle {
        let handle = ViewHandle(self.views.len());
        self.views.push(View {
            value,
            image: None,
            unknown: false,
            kind: ViewKind::Ordinary,
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
            kind: ViewKind::Ordinary,
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
            kind: ViewKind::RootComp,
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
    /// The current structural constructors have no positive parent image.
    /// Keep the child's exact image and all unknown inherited coverage.
    pub fn project_record(&mut self, parent: ViewHandle, child: ViewHandle, value: ValueHandle) -> Option<ViewHandle> {
        let parent = self.views.get(parent.0)?;
        let child_view = self.views.get(child.0)?;
        if parent.image.is_some() || child_view.value != value { return None; }
        if !parent.unknown || child_view.unknown { return Some(child); }
        let view = View { value, image: child_view.image, unknown: true, kind: child_view.kind };
        let handle = ViewHandle(self.views.len());
        self.views.push(view);
        Some(handle)
    }
    pub fn matches_value(&self, view: ViewHandle, value: ValueHandle) -> bool {
        self.views[view.0].value == value
    }

    /// Publish the genuine Value-entry receiver for one source-annotated
    /// callback formal. The inherited image/unknown coverage is copied, while
    /// this receiver remains separate from RootComp's ordered boundaries.
    pub fn callback_entry(
        &mut self,
        schema: Arc<CallbackResultSchema>,
        owner: ExecutionOwner,
        value: ValueHandle,
        incoming_view: ViewHandle,
    ) -> Option<(ViewHandle, CallbackEntryHandle)> {
        let ExecutionOwner::Invocation(receiver) = owner else { return None; };
        if self.views.get(incoming_view.0)?.value != value {
            return None;
        }
        let entry = CallbackEntryHandle(self.callback_entries.len());
        let inherited_image = self.views[incoming_view.0].image;
        let inherited_unknown = self.views[incoming_view.0].unknown;
        let view = ViewHandle(self.views.len());
        self.views.push(View {
            value,
            image: inherited_image,
            unknown: inherited_unknown,
            kind: ViewKind::CallbackEntry(entry),
        });
        let formal_receipt = self.receipt(
            owner,
            view,
            &schema.lambda,
            Some(schema.formal.id.clone()),
        );
        self.callback_entries.push(CallbackEntry {
            schema,
            receiver,
            value,
            incoming_view,
            view,
            formal_receipt,
        });
        Some((view, entry))
    }

    pub fn callback_entry_for_apply(
        &self,
        value: ValueHandle,
        view: ViewHandle,
        formal: &HirParameterId,
        owner: ExecutionOwner,
        callee: &SourceSite,
    ) -> Option<CallbackEntryHandle> {
        let ExecutionOwner::Invocation(receiver) = owner else { return None; };
        let entry = match self.views.get(view.0)?.kind {
            ViewKind::CallbackEntry(entry) => entry,
            _ => return None,
        };
        let entry = self.callback_entries.get(entry.0)?;
        let formal_receipt = self.receipts.get(entry.formal_receipt.0)?;
        let name_receipt = self.receipt_index.get(&(owner, view, None))?;
        let name_receipt = self.receipts.get(name_receipt.0)?;
        (entry.receiver == receiver
            && entry.value == value
            && entry.view == view
            && self.views.get(entry.incoming_view.0).is_some_and(|incoming|
                incoming.value == entry.value)
            && entry.schema.formal.id == *formal
            && formal_receipt.owner == owner
            && formal_receipt.view == view
            && formal_receipt.formal.as_ref() == Some(formal)
            && formal_receipt.slot.occurrence == entry.schema.lambda.occurrence
            && name_receipt.owner == owner
            && name_receipt.view == view
            && name_receipt.formal.is_none()
            && name_receipt.slot.source_root == callee.source_root
            && name_receipt.slot.occurrence == callee.occurrence)
            .then_some(match self.views[view.0].kind {
                ViewKind::CallbackEntry(handle) => handle,
                _ => return None,
            })
    }

    /// Select a callback only at the actual direct parameter-name Apply. The
    /// Result view and receipt are minted here, before the operation invocation.
    pub fn callback_use(
        &mut self,
        entry: CallbackEntryHandle,
        value: ValueHandle,
        source_view: ViewHandle,
        apply: &SourceSite,
        owner: ExecutionOwner,
    ) -> Option<CallbackUseHandle> {
        let (entry_receiver, entry_value, entry_view) = {
            let entry_record = self.callback_entries.get(entry.0)?;
            (entry_record.receiver, entry_record.value, entry_record.view)
        };
        let ExecutionOwner::Invocation(receiver) = owner else { return None; };
        if entry_receiver != receiver
            || entry_value != value
            || entry_view != source_view
            || self.views.get(source_view.0)?.value != value
        {
            return None;
        }
        let use_handle = CallbackUseHandle(self.callback_uses.len());
        let source_image = self.views[source_view.0].image;
        let source_unknown = self.views[source_view.0].unknown;
        let result_view = ViewHandle(self.views.len());
        self.views.push(View {
            value,
            image: source_image,
            unknown: source_unknown,
            kind: ViewKind::CallbackResult(use_handle),
        });
        let receipt = self.receipt(owner, result_view, apply, None);
        self.callback_uses.push(CallbackUse {
            entry,
            source_view,
            apply: apply.clone(),
            result_view,
            receipt,
        });
        Some(use_handle)
    }

    pub fn callback_execution(&mut self, use_handle: CallbackUseHandle) -> Option<ExecutionView> {
        let (result_view, receipt) = {
            let use_record = self.callback_uses.get(use_handle.0)?;
            (use_record.result_view, use_record.receipt)
        };
        self.execution(result_view, receipt)
    }
    pub fn has_root(&self, view: ViewHandle) -> bool {
        self.views[view.0].image.is_some()
    }
    pub fn execution(&mut self, view: ViewHandle, receipt: ReceiptHandle) -> Option<ExecutionView> {
        if self.receipts.get(receipt.0)?.view != view {
            return None;
        }
        match self.views.get(view.0)?.kind {
            ViewKind::CallbackEntry(_) => return None,
            ViewKind::CallbackResult(use_handle) => {
                let use_record = self.callback_uses.get(use_handle.0)?;
                let use_receipt = self.receipts.get(use_record.receipt.0)?;
                if use_record.result_view != view
                    || use_record.receipt != receipt
                    || use_receipt.view != view
                    || use_receipt.owner != self.receipts[receipt.0].owner
                    || use_receipt.formal.is_some()
                    || use_receipt.slot.source_root != use_record.apply.source_root
                    || use_receipt.slot.occurrence != use_record.apply.occurrence
                {
                    return None;
                }
            }
            ViewKind::Ordinary | ViewKind::RootComp => {}
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
        for observation in observations {
            if observation.event != event
                || observation.observer >= self.next_observer
                || !self.authentic_execution(observation.execution)
            {
                continue;
            }
            let Some(view) = self.views.get(observation.execution.view.0) else { continue; };
            let ViewKind::CallbackResult(use_handle) = view.kind else { continue; };
            if self.callback_grant(
                use_handle,
                observation.execution,
                owner,
                receiver,
                family,
            ) {
                return true;
            }
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
            // Callback Result views retain inherited images for provenance,
            // but they are a distinct port and never satisfy a RootComp query.
            if matches!(self.views[observation.execution.view.0].kind, ViewKind::CallbackResult(_) | ViewKind::CallbackEntry(_)) {
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

    fn callback_grant(
        &self,
        use_handle: CallbackUseHandle,
        execution: ExecutionView,
        owner: ExecutionOwner,
        receiver: usize,
        family: &SourceEffectId,
    ) -> bool {
        let Some(use_record) = self.callback_uses.get(use_handle.0) else { return false; };
        let Some(entry) = self.callback_entries.get(use_record.entry.0) else { return false; };
        let Some(use_receipt) = self.receipts.get(use_record.receipt.0) else { return false; };
        let Some(formal_receipt) = self.receipts.get(entry.formal_receipt.0) else { return false; };
        let Some(entry_view) = self.views.get(entry.view.0) else { return false; };
        let Some(result_view) = self.views.get(use_record.result_view.0) else { return false; };
        use_record.result_view == execution.view
            && use_record.receipt == execution.receipt
            && use_record.source_view == entry.view
            && entry.receiver == receiver
            && owner == ExecutionOwner::Invocation(receiver)
            && self.views.get(entry.view.0).is_some_and(|view|
                matches!(view.kind, ViewKind::CallbackEntry(handle) if handle == use_record.entry))
            && entry.value == entry_view.value
            && entry.value == result_view.value
            && use_receipt.owner == owner
            && use_receipt.view == use_record.result_view
            && use_receipt.formal.is_none()
            && use_receipt.slot.source_root == use_record.apply.source_root
            && use_receipt.slot.occurrence == use_record.apply.occurrence
            && formal_receipt.owner == owner
            && formal_receipt.view == entry.view
            && formal_receipt.formal.as_ref() == Some(&entry.schema.formal.id)
            && formal_receipt.slot.source_root == entry.schema.lambda.source_root
            && formal_receipt.slot.occurrence == entry.schema.lambda.occurrence
            && entry.schema.families.contains(family)
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
