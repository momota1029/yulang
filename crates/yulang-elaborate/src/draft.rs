use yulang_erased_ir::{ErasedBlock, ErasedExpr, ErasedStmt};

use crate::ErasedExprKind;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ElaborationDraft {
    pub(crate) root: DraftExprId,
    pub(crate) root_expr: usize,
    pub(crate) exprs: Vec<DraftExpr>,
    pub(crate) force_thunk_boundaries: Vec<ForceThunkBoundaryDraft>,
}

impl ElaborationDraft {
    pub(crate) fn from_root_expr(root_expr: usize, expr: &ErasedExpr) -> Self {
        let mut builder = DraftBuilder::default();
        let root = builder.expr(expr);
        Self {
            root,
            root_expr,
            exprs: builder.exprs,
            force_thunk_boundaries: builder.force_thunk_boundaries,
        }
    }

    pub(crate) fn expr(&self, id: DraftExprId) -> &DraftExpr {
        &self.exprs[id.0 as usize]
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct DraftExprId(pub(crate) u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct DraftComputationId(pub(crate) u32);

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DraftExpr {
    pub(crate) id: DraftExprId,
    pub(crate) kind: ErasedExprKind,
    pub(crate) computation: DraftComputationId,
    pub(crate) children: Vec<DraftExprId>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ForceThunkBoundaryDraft {
    pub(crate) site: DraftExprId,
    pub(crate) thunk: DraftExprId,
}

#[derive(Default)]
struct DraftBuilder {
    exprs: Vec<DraftExpr>,
    force_thunk_boundaries: Vec<ForceThunkBoundaryDraft>,
}

impl DraftBuilder {
    fn expr(&mut self, expr: &ErasedExpr) -> DraftExprId {
        let id = DraftExprId(self.exprs.len() as u32);
        let computation = DraftComputationId(id.0);
        let kind = ErasedExprKind::from_expr(expr);
        self.exprs.push(DraftExpr {
            id,
            kind,
            computation,
            children: Vec::new(),
        });

        let children = match expr {
            ErasedExpr::Def(_)
            | ErasedExpr::Ref(_)
            | ErasedExpr::PrimitiveOp(_)
            | ErasedExpr::Lit(_) => Vec::new(),
            ErasedExpr::Lambda { body, .. } | ErasedExpr::Pack { expr: body, .. } => {
                vec![self.expr(body)]
            }
            ErasedExpr::BindHere { expr } => {
                let thunk = self.expr(expr);
                self.force_thunk_boundaries
                    .push(ForceThunkBoundaryDraft { site: id, thunk });
                vec![thunk]
            }
            ErasedExpr::Apply { callee, arg } => vec![self.expr(callee), self.expr(arg)],
            ErasedExpr::RefSet { reference, value } => {
                vec![self.expr(reference), self.expr(value)]
            }
            ErasedExpr::Tuple(items) => items.iter().map(|item| self.expr(item)).collect(),
            ErasedExpr::Record { fields, spread } => {
                let mut children = fields
                    .iter()
                    .map(|field| self.expr(&field.value))
                    .collect::<Vec<_>>();
                if let Some(spread) = spread {
                    children.push(match spread {
                        yulang_erased_ir::RecordSpreadExpr::Head(expr)
                        | yulang_erased_ir::RecordSpreadExpr::Tail(expr) => self.expr(expr),
                    });
                }
                children
            }
            ErasedExpr::Variant { value, .. } => {
                value.iter().map(|value| self.expr(value)).collect()
            }
            ErasedExpr::Select { base, .. } => vec![self.expr(base)],
            ErasedExpr::Match { scrutinee, arms } => {
                let mut children = vec![self.expr(scrutinee)];
                for arm in arms {
                    if let Some(guard) = &arm.guard {
                        children.push(self.expr(guard));
                    }
                    children.push(self.expr(&arm.body));
                }
                children
            }
            ErasedExpr::Handle { body, arms } => {
                let mut children = vec![self.expr(body)];
                for arm in arms {
                    if let Some(guard) = &arm.guard {
                        children.push(self.expr(guard));
                    }
                    children.push(self.expr(&arm.body));
                }
                children
            }
            ErasedExpr::Block(block) => self.block(block),
        };

        self.exprs[id.0 as usize].children = children;
        id
    }

    fn block(&mut self, block: &ErasedBlock) -> Vec<DraftExprId> {
        let mut children = Vec::new();
        for stmt in &block.stmts {
            match stmt {
                ErasedStmt::Let { value, .. } | ErasedStmt::Expr(value) => {
                    children.push(self.expr(value));
                }
                ErasedStmt::Module { body, .. } => {
                    children.extend(self.block(body));
                }
            }
        }
        if let Some(tail) = &block.tail {
            children.push(self.expr(tail));
        }
        children
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn draft_assigns_computation_slot_to_each_expr_node() {
        let draft = ElaborationDraft::from_root_expr(
            0,
            &ErasedExpr::Tuple(vec![
                ErasedExpr::Lit(yulang_erased_ir::Lit::Int("1".to_string())),
                ErasedExpr::Lit(yulang_erased_ir::Lit::Int("2".to_string())),
            ]),
        );

        assert_eq!(draft.root_expr, 0);
        assert_eq!(draft.exprs.len(), 3);
        assert_eq!(draft.expr(draft.root).kind, ErasedExprKind::Tuple);
        assert_eq!(draft.expr(draft.root).children.len(), 2);
        assert_eq!(
            draft
                .exprs
                .iter()
                .map(|expr| expr.computation)
                .collect::<Vec<_>>(),
            vec![
                DraftComputationId(0),
                DraftComputationId(1),
                DraftComputationId(2)
            ]
        );
    }

    #[test]
    fn draft_marks_bind_here_as_force_thunk_boundary() {
        let draft = ElaborationDraft::from_root_expr(
            0,
            &ErasedExpr::BindHere {
                expr: Box::new(ErasedExpr::Ref(yulang_erased_ir::RefId(7))),
            },
        );

        assert_eq!(draft.expr(draft.root).kind, ErasedExprKind::BindHere);
        assert_eq!(
            draft.force_thunk_boundaries,
            vec![ForceThunkBoundaryDraft {
                site: DraftExprId(0),
                thunk: DraftExprId(1),
            }]
        );
    }
}
