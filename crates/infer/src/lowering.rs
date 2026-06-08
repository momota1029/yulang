//! CST expression を `poly` IR と推論用 computation slot へ落とす。
//!
//! この module は pass2 の小さな入口として、式 node から `ExprId` と
//! `typing::Computation` を同時に作る。式そのものに型 table は残さず、lowering 中に必要な
//! value/effect slot だけを `Computation` として返す。
//!
//! 名前参照は `RefId` を発行して `AnalysisSession` の queue に解決結果を渡す。これにより、
//! `poly` への `RefId -> DefId` 書き戻しと SCC edge 追加は、lowering 本体から分離された
//! event routing 側に残る。

use rowan::{NodeOrToken, SyntaxNode};
use sources::Name;
use yulang_parser::lex::SyntaxKind;
use yulang_parser::sink::YulangLanguage;

use poly::expr::{Expr, Lit};
use poly::types::{Neg, NegId, Pos, TypeVar};

use crate::analysis::{AnalysisSession, AnalysisWork};
use crate::uses::RefUse;
use crate::{ModuleId, ModuleOrder, ModuleTable};

type Cst = SyntaxNode<YulangLanguage>;

/// expression lowering の入口。
///
/// 1つの owner def の body を lower する間だけ作る。`module` / `site` は module-level lookup の
/// 基準で、`parent` は参照 use-site から SCC edge を張る元になる。
pub struct ExprLowerer<'a> {
    session: &'a mut AnalysisSession,
    modules: &'a ModuleTable,
    module: ModuleId,
    site: ModuleOrder,
    parent: poly::expr::DefId,
}

impl<'a> ExprLowerer<'a> {
    pub fn new(
        session: &'a mut AnalysisSession,
        modules: &'a ModuleTable,
        module: ModuleId,
        site: ModuleOrder,
        parent: poly::expr::DefId,
    ) -> Self {
        Self {
            session,
            modules,
            module,
            site,
            parent,
        }
    }

    /// CST expression を `poly::Expr` と `Computation` に lower する。
    ///
    /// まだ対応していない suffix / atom は `LoweringError::UnsupportedSyntax` として返す。
    /// fallback の unit 化で IR を捏造しないため、未対応範囲は呼び出し側が診断へ変換する。
    pub fn lower_expr(&mut self, node: &Cst) -> Result<Computation, LoweringError> {
        match node.kind() {
            SyntaxKind::Expr => self.lower_expr_chain(node),
            _ => self.lower_atom(node),
        }
    }

    fn lower_expr_chain(&mut self, node: &Cst) -> Result<Computation, LoweringError> {
        let mut items = node
            .children_with_tokens()
            .filter(|item| !item_is_trivia(item));
        let Some(head) = items.next() else {
            return Ok(self.unit_expr());
        };

        let mut acc = self.lower_head(head)?;
        for item in items {
            match item {
                NodeOrToken::Node(child)
                    if matches!(child.kind(), SyntaxKind::ApplyML | SyntaxKind::ApplyC) =>
                {
                    acc = self.apply_arguments(acc, &child)?;
                }
                NodeOrToken::Node(child) => {
                    return Err(LoweringError::UnsupportedSyntax { kind: child.kind() });
                }
                NodeOrToken::Token(token) => {
                    return Err(LoweringError::UnsupportedSyntax { kind: token.kind() });
                }
            }
        }
        Ok(acc)
    }

    fn lower_head(
        &mut self,
        head: NodeOrToken<Cst, rowan::SyntaxToken<YulangLanguage>>,
    ) -> Result<Computation, LoweringError> {
        match head {
            NodeOrToken::Token(token) => match token.kind() {
                SyntaxKind::Ident => self.lower_name(Name(token.text().to_string())),
                SyntaxKind::Number => self.lower_number(token.text()),
                _ => Err(LoweringError::UnsupportedSyntax { kind: token.kind() }),
            },
            NodeOrToken::Node(node) => self.lower_atom(&node),
        }
    }

    fn lower_atom(&mut self, node: &Cst) -> Result<Computation, LoweringError> {
        match node.kind() {
            SyntaxKind::Expr => self.lower_expr_chain(node),
            SyntaxKind::Number => self.lower_number(&node.text().to_string()),
            SyntaxKind::Paren => self.lower_paren(node),
            _ => Err(LoweringError::UnsupportedSyntax { kind: node.kind() }),
        }
    }

    fn lower_paren(&mut self, node: &Cst) -> Result<Computation, LoweringError> {
        let exprs = node
            .children()
            .filter(|child| child.kind() == SyntaxKind::Expr)
            .collect::<Vec<_>>();
        match exprs.as_slice() {
            [] => Ok(self.unit_expr()),
            [expr] => self.lower_expr(expr),
            _ => {
                let item_lowers = exprs
                    .iter()
                    .map(|expr| self.lower_expr(expr))
                    .collect::<Result<Vec<_>, _>>()?;
                let items = item_lowers
                    .iter()
                    .map(|computation| computation.expr)
                    .collect::<Vec<_>>();
                let value = self.fresh_type_var();
                let expansive = item_lowers.iter().any(|item| item.is_expansive());
                let effect = if expansive {
                    self.fresh_type_var()
                } else {
                    self.fresh_exact_pure_effect()
                };
                let expr = self.session.poly.add_expr(Expr::Tuple(items));
                let item_values = item_lowers
                    .iter()
                    .map(|item| self.alloc_pos(Pos::Var(item.value)))
                    .collect::<Vec<_>>();
                for item in &item_lowers {
                    self.subtype_var_to_var(item.effect, effect);
                }
                self.constrain_lower(value, Pos::Tuple(item_values));
                Ok(Computation::new(
                    expr,
                    value,
                    effect,
                    if expansive {
                        Evaluation::Computation
                    } else {
                        Evaluation::Value
                    },
                ))
            }
        }
    }

    fn lower_number(&mut self, text: &str) -> Result<Computation, LoweringError> {
        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        let (lit, primitive) = if integer_number_token(text) {
            let parsed = text
                .parse::<i64>()
                .map_err(|_| LoweringError::InvalidNumber {
                    text: text.to_string(),
                })?;
            (Lit::Int(parsed), "int")
        } else {
            let parsed = text
                .parse::<f64>()
                .map_err(|_| LoweringError::InvalidNumber {
                    text: text.to_string(),
                })?;
            (Lit::Float(parsed), "float")
        };

        self.constrain_lower(value, primitive_type(primitive));
        let expr = self.session.poly.add_expr(Expr::Lit(lit));
        Ok(Computation::value(expr, value, effect))
    }

    fn lower_name(&mut self, name: Name) -> Result<Computation, LoweringError> {
        let Some(target) = self.modules.lexical_value_at(self.module, &name, self.site) else {
            return Err(LoweringError::UnresolvedName { name });
        };
        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        let reference = self.session.poly.add_ref();
        self.session.refs.insert(
            reference,
            RefUse {
                parent: self.parent,
                value,
            },
        );
        self.session.enqueue(AnalysisWork::ApplyRefResolution {
            ref_id: reference,
            target,
        });

        let expr = self.session.poly.add_expr(Expr::Var(reference));
        Ok(Computation::value(expr, value, effect))
    }

    fn apply_arguments(
        &mut self,
        mut callee: Computation,
        node: &Cst,
    ) -> Result<Computation, LoweringError> {
        let args = node
            .children()
            .filter(|child| child.kind() == SyntaxKind::Expr)
            .collect::<Vec<_>>();
        if args.is_empty() {
            let unit = self.unit_expr();
            return Ok(self.make_app(callee, unit));
        }
        for arg in args {
            let lowered_arg = self.lower_expr(&arg)?;
            callee = self.make_app(callee, lowered_arg);
        }
        Ok(callee)
    }

    fn make_app(&mut self, callee: Computation, arg: Computation) -> Computation {
        let result_value = self.fresh_type_var();
        let result_effect = self.fresh_type_var();
        let call_effect = self.fresh_type_var();

        let arg_value = self.alloc_pos(Pos::Var(arg.value));
        let arg_effect = self.alloc_pos(Pos::Var(arg.effect));
        let return_effect = self.alloc_neg(Neg::Var(call_effect));
        let return_value = self.alloc_neg(Neg::Var(result_value));
        let callee_upper = self.alloc_neg(Neg::Fun {
            arg: arg_value,
            arg_eff: arg_effect,
            ret_eff: return_effect,
            ret: return_value,
        });
        self.subtype(Pos::Var(callee.value), callee_upper);
        self.subtype_var_to_var(callee.effect, result_effect);
        self.subtype_var_to_var(arg.effect, result_effect);
        self.subtype_var_to_var(call_effect, result_effect);

        let expr = self.session.poly.add_expr(Expr::App(callee.expr, arg.expr));
        Computation::computation(expr, result_value, result_effect)
    }

    fn unit_expr(&mut self) -> Computation {
        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        self.constrain_lower(value, primitive_type("unit"));
        let expr = self.session.poly.add_expr(Expr::Lit(Lit::Unit));
        Computation::value(expr, value, effect)
    }

    fn fresh_type_var(&mut self) -> TypeVar {
        self.session.infer.fresh_type_var()
    }

    fn fresh_exact_pure_effect(&mut self) -> TypeVar {
        let effect = self.fresh_type_var();
        let bot = self.alloc_pos(Pos::Bot);
        let empty = self.empty_neg_row();
        let effect_upper = self.alloc_neg(Neg::Var(effect));
        let effect_lower = self.alloc_pos(Pos::Var(effect));
        self.session.infer.subtype(bot, effect_upper);
        self.session.infer.subtype(effect_lower, empty);
        effect
    }

    fn empty_neg_row(&mut self) -> NegId {
        let top = self.alloc_neg(Neg::Top);
        self.alloc_neg(Neg::Row(Vec::new(), top))
    }

    fn constrain_lower(&mut self, var: TypeVar, lower: Pos) {
        let lower = self.alloc_pos(lower);
        let upper = self.alloc_neg(Neg::Var(var));
        self.session.infer.subtype(lower, upper);
    }

    fn subtype_var_to_var(&mut self, lower: TypeVar, upper: TypeVar) {
        let upper = self.alloc_neg(Neg::Var(upper));
        self.subtype(Pos::Var(lower), upper);
    }

    fn subtype(&mut self, lower: Pos, upper: NegId) {
        let lower = self.alloc_pos(lower);
        self.session.infer.subtype(lower, upper);
    }

    fn alloc_pos(&mut self, pos: Pos) -> poly::types::PosId {
        self.session.infer.alloc_pos(pos)
    }

    fn alloc_neg(&mut self, neg: Neg) -> NegId {
        self.session.infer.alloc_neg(neg)
    }
}

pub use crate::typing::{Computation, Evaluation};

#[derive(Debug, Clone, PartialEq, Eq)]
/// expression lowering が構造化して返す失敗。
pub enum LoweringError {
    UnsupportedSyntax { kind: SyntaxKind },
    UnresolvedName { name: Name },
    InvalidNumber { text: String },
}

fn item_is_trivia(item: &NodeOrToken<Cst, rowan::SyntaxToken<YulangLanguage>>) -> bool {
    item.as_token()
        .is_some_and(|token| matches!(token.kind(), SyntaxKind::Space | SyntaxKind::LineComment))
}

fn integer_number_token(text: &str) -> bool {
    text.chars().all(|ch| ch.is_ascii_digit())
}

fn primitive_type(name: &str) -> Pos {
    Pos::Con(vec![name.into()], Vec::new())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lower_module_map;
    use crate::scc::SccEvent;
    use poly::expr::{DefId, RefId};

    fn parse(src: &str) -> Cst {
        SyntaxNode::new_root(yulang_parser::parse_module_to_green(src))
    }

    fn binding_expr(root: &Cst, name: &str) -> Cst {
        root.children()
            .find(|child| {
                child.kind() == SyntaxKind::Binding && binding_name(child).as_deref() == Some(name)
            })
            .and_then(|binding| {
                binding
                    .children()
                    .find(|child| child.kind() == SyntaxKind::BindingBody)
            })
            .and_then(|body| {
                body.children()
                    .find(|child| child.kind() == SyntaxKind::Expr)
            })
            .expect("binding body expr")
    }

    fn binding_name(binding: &Cst) -> Option<String> {
        binding
            .children()
            .find(|child| child.kind() == SyntaxKind::BindingHeader)?
            .children()
            .find(|child| child.kind() == SyntaxKind::Pattern)?
            .children_with_tokens()
            .filter_map(|item| item.into_token())
            .find(|token| token.kind() == SyntaxKind::Ident)
            .map(|token| token.text().to_string())
    }

    fn binding_def_and_order(
        modules: &ModuleTable,
        module: ModuleId,
        name: &str,
    ) -> (DefId, ModuleOrder) {
        let decl = modules.value_decls(module, &Name(name.into()))[0].clone();
        (decl.def, decl.order)
    }

    #[test]
    fn lowers_int_literal_with_primitive_lower_bound() {
        let root = parse("my a = 1\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (owner, site) = binding_def_and_order(&lower.modules, module, "a");
        let expr = binding_expr(&root, "a");
        let mut session = AnalysisSession::new(lower.arena);

        let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
            .lower_expr(&expr)
            .unwrap();

        assert!(matches!(
            session.poly.expr(computation.expr),
            Expr::Lit(Lit::Int(1))
        ));
        let bounds = session
            .infer
            .constraints()
            .bounds()
            .of(computation.value)
            .expect("literal value should receive a lower bound");
        assert!(bounds.lowers().iter().any(|bound| {
            matches!(
                session.infer.constraints().types().pos(bound.pos),
                Pos::Con(path, args) if path == &vec!["int".to_string()] && args.is_empty()
            )
        }));
    }

    #[test]
    fn reference_lowering_queues_resolution_and_scc_edge() {
        let root = parse("my a = 1\nmy b = a\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (target, _) = binding_def_and_order(&lower.modules, module, "a");
        let (owner, site) = binding_def_and_order(&lower.modules, module, "b");
        let expr = binding_expr(&root, "b");
        let mut session = AnalysisSession::new(lower.arena);

        let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
            .lower_expr(&expr)
            .unwrap();
        let reference = match session.poly.expr(computation.expr) {
            Expr::Var(reference) => *reference,
            _ => panic!("expected var expr"),
        };

        assert_eq!(session.poly.ref_target(reference), None);
        session.drain_work();

        assert_eq!(session.poly.ref_target(reference), Some(target));
        assert_eq!(
            session.take_scc_events(),
            vec![SccEvent::ComponentEdgeAdded {
                from: vec![owner],
                to: vec![target]
            }]
        );
    }

    #[test]
    fn application_lowers_to_app_and_constrains_callee_as_function() {
        let root = parse("my f = 1\nmy x = 2\nmy y = f x\n");
        let lower = lower_module_map(&root);
        let module = lower.modules.root_id();
        let (owner, site) = binding_def_and_order(&lower.modules, module, "y");
        let expr = binding_expr(&root, "y");
        let mut session = AnalysisSession::new(lower.arena);

        let computation = ExprLowerer::new(&mut session, &lower.modules, module, site, owner)
            .lower_expr(&expr)
            .unwrap();
        let (callee, arg) = match session.poly.expr(computation.expr) {
            Expr::App(callee, arg) => (*callee, *arg),
            _ => panic!("expected app expr"),
        };
        let callee_ref = expr_ref(&session, callee);
        let arg_ref = expr_ref(&session, arg);
        let callee_value = session
            .refs
            .value(callee_ref)
            .expect("callee ref value slot");
        assert!(session.refs.value(arg_ref).is_some());

        let bounds = session
            .infer
            .constraints()
            .bounds()
            .of(callee_value)
            .expect("callee should have function upper bound");
        assert!(bounds.uppers().iter().any(|bound| {
            matches!(
                session.infer.constraints().types().neg(bound.neg),
                Neg::Fun { .. }
            )
        }));
    }

    fn expr_ref(session: &AnalysisSession, expr: poly::expr::ExprId) -> RefId {
        match session.poly.expr(expr) {
            Expr::Var(reference) => *reference,
            _ => panic!("expected var expr"),
        }
    }
}
