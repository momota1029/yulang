//! Immutable source contexts; nodes own no store or active-configuration snapshot.
use super::{
    machine::{ExecutionOwner, Frame},
    program::Code,
    receiving::ExecutionView,
};
use std::sync::Arc;
use yu_hir::shadow::SourceOperationDeclaration;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct TemplateHandle(pub(super) usize);

pub(super) struct ResumeTemplate {
    pub nodes: Vec<TemplateNode>,
    pub root: usize,
    pub declaration: Arc<SourceOperationDeclaration>,
    #[allow(
        dead_code,
        reason = "original request event retained as lineage, never replayed as a new event"
    )]
    pub original_event: usize,
}
#[derive(Clone)]
pub(super) enum TemplateNode {
    Hole,
    Bind {
        inner: usize,
        frame: Frame,
    },
    Owner {
        inner: usize,
        original: ExecutionOwner,
    },
    ForwardHandler {
        inner: usize,
        handler: Arc<Code>,
        environment: usize,
        owner: ExecutionOwner,
    },
    View {
        inner: usize,
        original: ExecutionView,
    },
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::runtime::program::SourceSite;
    use yu_hir::shadow::lower_module_with_local_source;
    use yu_hir::{FileId, FileKey, HirItem, ModuleIdentity, SemanticImports};
    use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

    #[test]
    fn nested_resume_arguments_retain_only_flat_template_handles() {
        let text: Arc<SourceText> = Arc::from("act signal:\n    our ping: () -> int\nmy main = ()");
        let parsed = parse_file(
            text.clone(),
            Arc::new(scan_header(text)),
            Arc::new(SyntaxEnvironment::empty()),
        );
        assert!(parsed.syntax_diagnostics().unwrap().is_empty());
        let hir = lower_module_with_local_source(
            ModuleIdentity::source_root(FileId::new(FileKey::new("resume-storage", "test.yu"))),
            &parsed,
            SemanticImports::empty(),
        )
        .unwrap();
        let declaration = hir.source_effect_declarations()[0].operations[0].clone();
        let binding = hir
            .items()
            .iter()
            .find_map(|item| {
                if let HirItem::Binding(binding) = item {
                    Some(binding)
                } else {
                    None
                }
            })
            .unwrap();
        let local = hir
            .local_source(binding.definition_root())
            .unwrap()
            .unwrap();
        let expression = local.expression(local.body()).unwrap();
        let source = SourceSite {
            source_root: yu_hir::SourceRootId::Definition(binding.definition_root().clone()),
            occurrence: expression.occurrence.clone(),
            range: expression.range.clone(),
        };
        let mut arena = vec![ResumeTemplate {
            nodes: vec![TemplateNode::Hole],
            root: 0,
            declaration: declaration.clone(),
            original_event: 0,
        }];
        for index in 1..=1024 {
            arena.push(ResumeTemplate {
                nodes: vec![
                    TemplateNode::Hole,
                    TemplateNode::Bind {
                        inner: 0,
                        frame: Frame::ResumeArgument {
                            template: TemplateHandle(index - 1),
                            source: source.clone(),
                        },
                    },
                ],
                root: 1,
                declaration: declaration.clone(),
                original_event: index,
            });
        }
        for (index, template) in arena.iter().enumerate().skip(1) {
            let TemplateNode::Bind {
                inner,
                frame:
                    Frame::ResumeArgument {
                        template: previous, ..
                    },
            } = &template.nodes[template.root]
            else {
                panic!("expected a handle-only pending resume argument");
            };
            assert_eq!(*inner, 0);
            assert_eq!(previous.0, index - 1);
        }
        let retained_frame = arena.last().unwrap().nodes[1].clone();
        // Vec owns every template exactly once. Dropping it traverses its flat
        // elements; the retained Bind frame owns only an ordinal, never a chain.
        drop(arena);
        let TemplateNode::Bind {
            frame: Frame::ResumeArgument { template, .. },
            ..
        } = retained_frame
        else {
            panic!("expected retained frame");
        };
        assert_eq!(template.0, 1023);
    }
}
