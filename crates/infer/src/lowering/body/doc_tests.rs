use super::*;

#[derive(Clone)]
struct DocFenceCandidate {
    name: String,
    module: ModuleId,
    order: ModuleOrder,
    file: Path,
    fence: Cst,
    source_range_offset: isize,
    comment_span: SourceSpan,
    fence_ordinal: usize,
    range_in_fence: sources::SourceRange,
}

impl BodyLowerer {
    pub(super) fn lower_doc_comment_tests(&mut self) -> Vec<LoweredDocTest> {
        let mut candidates = self.doc_fence_candidates();
        candidates.sort_by(|left, right| candidate_key(left).cmp(&candidate_key(right)));
        candidates.dedup_by(|right, left| fence_identity(left) == fence_identity(right));

        candidates
            .into_iter()
            .filter_map(|candidate| self.lower_doc_fence(candidate))
            .collect()
    }

    fn doc_fence_candidates(&self) -> Vec<DocFenceCandidate> {
        let mut candidates = Vec::new();
        for (def, doc) in self.modules.def_doc_comments() {
            let item = self
                .labels
                .def_label(def)
                .map(|label| label.replace('.', "::"))
                .unwrap_or_else(|| format!("d{}", def.0));
            collect_doc_fences(doc, &item, &mut candidates);
        }
        for (id, doc) in self.modules.type_doc_comments() {
            let Some(decl) = self.modules.type_decl_by_id(id) else {
                continue;
            };
            let item = self
                .modules
                .type_decl_path(&decl)
                .segments
                .into_iter()
                .map(|name| name.0)
                .collect::<Vec<_>>()
                .join("::");
            collect_doc_fences(doc, &item, &mut candidates);
        }
        candidates
    }

    fn lower_doc_fence(&mut self, candidate: DocFenceCandidate) -> Option<LoweredDocTest> {
        let parent = self.session.poly.defs.fresh();
        self.labels.set_def_label(parent, candidate.name.clone());
        let previous_level = self.session.infer.enter_child_level();
        let root = self.session.infer.fresh_type_var();
        self.session
            .enqueue(AnalysisWork::Scc(SccInput::RegisterDef {
                def: parent,
                root,
            }));

        let items = candidate
            .fence
            .children()
            .filter(|child| child.kind() != SyntaxKind::YmCodeFenceInfo)
            .collect::<Vec<_>>();
        let lowered = ExprLowerer::with_labels(
            &mut self.session,
            &self.modules,
            candidate.module,
            candidate.order,
            parent,
            &mut self.labels,
        )
        .with_source_file(candidate.file.clone())
        .with_source_range_offset(candidate.source_range_offset)
        .with_source_spans(self.record_source_spans)
        .with_local_method_scope(self.local_method_scope)
        .lower_block_items(&items);

        let result = match lowered {
            Ok(computation) => {
                self.session.poly.root_exprs.push(computation.expr);
                self.session
                    .poly
                    .runtime_roots
                    .push(poly::expr::RuntimeRoot::Expr(computation.expr));
                Some(LoweredDocTest {
                    name: candidate.name,
                    root: computation.expr,
                    comment_span: candidate.comment_span,
                    fence_ordinal: candidate.fence_ordinal,
                    range_in_fence: candidate.range_in_fence,
                })
            }
            Err(error) => {
                self.errors.push(BodyLoweringError::RootExpr {
                    file: candidate.file,
                    error,
                });
                None
            }
        };
        self.session
            .enqueue(AnalysisWork::Scc(SccInput::DefFinished { def: parent }));
        self.session.infer.restore_level(previous_level);
        result
    }
}

fn collect_doc_fences(
    doc: &crate::DocComment,
    documented_item: &str,
    candidates: &mut Vec<DocFenceCandidate>,
) {
    let mut fence_index = 0usize;
    for unit in doc.units() {
        for (fence_ordinal, fence) in unit
            .node()
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::YmCodeFence)
            .enumerate()
        {
            if !is_yulang_fence(&fence) {
                continue;
            }
            fence_index += 1;
            let range = assertion_range(&fence)
                .unwrap_or_else(|| crate::source_range_from_text_range(fence.text_range()));
            let fence_start = usize::from(fence.text_range().start());
            let source_range_offset = unit
                .fence_source_start(fence_ordinal)
                .map(|source_start| source_start as isize - fence_start as isize)
                .unwrap_or_default();
            candidates.push(DocFenceCandidate {
                name: format!("doc::{documented_item}#{fence_index}"),
                module: unit.module(),
                order: unit.order(),
                file: unit.source_span().file.clone(),
                fence,
                source_range_offset,
                comment_span: unit.source_span().clone(),
                fence_ordinal,
                range_in_fence: sources::SourceRange {
                    start: range.start.saturating_sub(fence_start),
                    end: range.end.saturating_sub(fence_start),
                },
            });
        }
    }
}

fn is_yulang_fence(fence: &Cst) -> bool {
    fence
        .children()
        .find(|child| child.kind() == SyntaxKind::YmCodeFenceInfo)
        .is_some_and(|info| info.text().to_string().trim() == "yulang")
}

fn assertion_range(fence: &Cst) -> Option<sources::SourceRange> {
    fence
        .descendants_with_tokens()
        .filter_map(|item| item.into_token())
        .find(|token| token.text() == "assert")
        .map(|token| crate::token_source_range(&token))
}

fn candidate_key(candidate: &DocFenceCandidate) -> (String, usize, usize, String) {
    let file = candidate
        .file
        .segments
        .iter()
        .map(|segment| segment.0.as_str())
        .collect::<Vec<_>>()
        .join("::");
    let range = candidate.fence.text_range();
    (
        file,
        usize::from(range.start()),
        usize::from(range.end()),
        candidate.name.clone(),
    )
}

fn fence_identity(candidate: &DocFenceCandidate) -> (Path, rowan::TextRange) {
    (candidate.file.clone(), candidate.fence.text_range())
}
