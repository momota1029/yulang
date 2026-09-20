//! The first, deliberately narrow, HIR-adjacent association product.

use std::{cmp::Ordering, ops::Range};

use yu_syntax::{ParsedFile, SyntaxKind, SyntaxNode, SyntaxToken};

mod module;

pub use module::{
    DefId, DefinitionRootId, FileId, FileKey, HirAvailabilityError, HirBinding, HirDiagnostic,
    HirDiagnosticId, HirError, HirErrorAttachment, HirErrorId, HirErrorKind, HirErrorOrigin,
    HirItem, HirModule, HirName, HirOccurrenceId, HirVisibility, ModuleId, ModuleIdentity,
    NameResolution, ResolvedExpr, SemanticImports, lower_module,
};

/// Every top-level operator chain associated from one parsed file, in source order.
///
/// This is a pre-HIR product: it deliberately has no declaration, name, type,
/// or `DefId` model yet.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AssociatedChains {
    chains: Vec<AssociatedChain>,
}

impl AssociatedChains {
    pub fn chains(&self) -> &[AssociatedChain] {
        &self.chains
    }
}

/// One precedence-associated `OperatorChain` and its original source extent.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AssociatedChain {
    range: Range<usize>,
    expression: HirExpr,
}

impl AssociatedChain {
    pub fn range(&self) -> &Range<usize> {
        &self.range
    }

    pub fn expression(&self) -> &HirExpr {
        &self.expression
    }
}

/// A source-provenance-preserving associated expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum HirExpr {
    /// A syntax expression that this slice intentionally does not lower.
    Value {
        kind: SyntaxKind,
        range: Range<usize>,
        children: Vec<HirExpr>,
    },
    /// A `Missing`, `Error`, or otherwise malformed operand position.
    Error {
        kind: SyntaxKind,
        range: Range<usize>,
        children: Vec<HirExpr>,
    },
    /// One dynamic operator application, shaped by the accepted table's powers.
    Apply {
        operator: HirOperator,
        operands: Box<[HirExpr]>,
        range: Range<usize>,
    },
}

impl HirExpr {
    pub fn range(&self) -> &Range<usize> {
        match self {
            Self::Value { range, .. } | Self::Error { range, .. } | Self::Apply { range, .. } => {
                range
            }
        }
    }
}

/// The exact dynamic operator use that produced an [`HirExpr::Apply`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HirOperator {
    spelling: String,
    fixity: OperatorFixity,
    range: Range<usize>,
}

impl HirOperator {
    pub fn spelling(&self) -> &str {
        &self.spelling
    }

    pub fn fixity(&self) -> OperatorFixity {
        self.fixity
    }

    pub fn range(&self) -> &Range<usize> {
        &self.range
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum OperatorFixity {
    Prefix,
    Infix,
    Suffix,
}

/// Associates every `OperatorChain` in `parsed` without changing its CST.
pub fn associate_operator_chains(parsed: &ParsedFile) -> AssociatedChains {
    let root = SyntaxNode::new_root(parsed.green().clone());
    let mut chains = Vec::new();
    visit_node(&root, parsed, &mut chains);
    AssociatedChains { chains }
}

fn visit_node(node: &SyntaxNode, parsed: &ParsedFile, chains: &mut Vec<AssociatedChain>) {
    for child in node.children() {
        if child.kind() == SyntaxKind::OperatorChain {
            chains.push(AssociatedChain {
                range: range_of(&child),
                expression: associate_chain_owned(parsed, child)
                    .expect("parser-associated operator chain satisfies its exact invariants")
                    .into_hir(),
            });
        } else {
            visit_node(&child, parsed, chains);
        }
    }
}

/// The one crate-private association seam used by both the legacy public
/// adapter and module lowering. It retains atom text only for the owned result
/// being consumed, never by slicing the source or rebuilding an environment.
fn associate_chain_owned(
    parsed: &ParsedFile,
    node: SyntaxNode,
) -> Result<OwnedAssociatedExpr, AssociationError> {
    let atom = direct_atom(&node);
    Ok(OwnedAssociatedExpr {
        expression: associate_chain_expression(&node, parsed)?,
        atom,
    })
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum AssociationError {
    ExactOperatorEnvironment,
    StructuralInvariant,
}

#[derive(Debug)]
struct OwnedAssociatedExpr {
    expression: HirExpr,
    atom: Option<OwnedAtom>,
}

impl OwnedAssociatedExpr {
    fn into_hir(self) -> HirExpr {
        self.expression
    }

    fn into_parts(self) -> (HirExpr, Option<OwnedAtom>) {
        (self.expression, self.atom)
    }
}

#[derive(Debug)]
struct OwnedAtom {
    kind: SyntaxKind,
    spelling: String,
    range: Range<usize>,
}

fn direct_atom(node: &SyntaxNode) -> Option<OwnedAtom> {
    let mut children = node.children();
    let child = children.next()?;
    if children.next().is_some()
        || !matches!(
            child.kind(),
            SyntaxKind::IntegerLiteral | SyntaxKind::IdentifierExpression
        )
    {
        return None;
    }
    let mut tokens = child
        .children_with_tokens()
        .filter_map(|element| element.into_token())
        .filter(|token| matches!(token.kind(), SyntaxKind::Integer | SyntaxKind::Identifier));
    let token = tokens.next()?;
    if tokens.next().is_some() {
        return None;
    }
    Some(OwnedAtom {
        kind: child.kind(),
        spelling: token.text().to_owned(),
        range: range_of_token(&token),
    })
}

fn associate_chain_expression(
    node: &SyntaxNode,
    parsed: &ParsedFile,
) -> Result<HirExpr, AssociationError> {
    let children = node
        .children_with_tokens()
        .filter_map(|child| {
            if let Some(node) = child.as_node() {
                return Some(ChainItem::Node(node.clone()));
            }
            child
                .into_token()
                .filter(|token| token.kind() == SyntaxKind::Error)
                .map(ChainItem::Error)
        })
        .collect::<Vec<_>>();
    let mut parser = ChainParser {
        children: &children,
        cursor: 0,
        parsed,
    };
    let expression = parser.expression(None)?;
    (parser.cursor == children.len())
        .then_some(expression)
        .ok_or(AssociationError::StructuralInvariant)
}

struct ChainParser<'a> {
    children: &'a [ChainItem],
    cursor: usize,
    parsed: &'a ParsedFile,
}

#[derive(Clone)]
enum ChainItem {
    Node(SyntaxNode),
    Error(SyntaxToken),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum DirectChainItem {
    Recovery,
    Prefix,
    Infix,
    Suffix,
    Value,
}

impl DirectChainItem {
    fn is_retry_operand(self) -> bool {
        matches!(self, Self::Prefix | Self::Value)
    }
}

#[derive(Clone, Copy)]
enum OperatorUseRole {
    Prefix,
    Infix,
    Suffix,
    Nullfix,
}

impl ChainItem {
    fn kind(&self) -> SyntaxKind {
        match self {
            Self::Node(node) => node.kind(),
            Self::Error(token) => token.kind(),
        }
    }

    fn node(&self) -> Result<&SyntaxNode, AssociationError> {
        match self {
            Self::Node(node) => Ok(node),
            Self::Error(_) => Err(AssociationError::StructuralInvariant),
        }
    }
}

impl ChainParser<'_> {
    fn expression(&mut self, minimum: Option<&[i8]>) -> Result<HirExpr, AssociationError> {
        let Some(item) = self.take() else {
            return Ok(Self::error(SyntaxKind::Missing, 0..0));
        };
        let mut left = match self.classify_direct_item(&item)? {
            DirectChainItem::Recovery => self.recovered_operand(item, minimum)?,
            DirectChainItem::Prefix => {
                let node = item.node()?;
                let (_, right) = self.operator(node, OperatorFixity::Prefix)?;
                let operator = self.hir_operator(node, OperatorFixity::Prefix)?;
                let operand = self.expression(Some(&right))?;
                apply(operator, vec![operand])
            }
            DirectChainItem::Infix | DirectChainItem::Suffix | DirectChainItem::Value => {
                self.item_expression(&item)?
            }
        };

        while let Some(next) = self.peek() {
            match next.kind() {
                kind if is_fixed_postfix(kind) || kind == SyntaxKind::MlArgument => {
                    let item = self.take().ok_or(AssociationError::StructuralInvariant)?;
                    left = self.structural_continuation(left, item.node()?)?;
                }
                SyntaxKind::TypeAnnotationTail => {
                    // An annotation is an outer association barrier. A recursive
                    // dynamic right operand leaves it for the caller, which first
                    // reduces its entire pending dynamic segment.
                    if minimum.is_some() {
                        break;
                    }
                    let item = self.take().ok_or(AssociationError::StructuralInvariant)?;
                    left = self.structural_continuation(left, item.node()?)?;
                }
                kind if is_terminal_outer_tail(kind) => {
                    // Like annotations, terminal tails apply after the complete
                    // pending dynamic segment. They finish this flat chain; any
                    // residual direct child is recovery provenance, not a second
                    // semantic continuation.
                    if minimum.is_some() {
                        break;
                    }
                    let item = self.take().ok_or(AssociationError::StructuralInvariant)?;
                    left = self.structural_continuation(left, item.node()?)?;
                    while let Some(residual) = self.take() {
                        let residual = match self.classify_direct_item(&residual)? {
                            DirectChainItem::Recovery => {
                                self.recovered_operand(residual, minimum)?
                            }
                            DirectChainItem::Prefix
                            | DirectChainItem::Infix
                            | DirectChainItem::Suffix
                            | DirectChainItem::Value => self.item_expression(&residual)?,
                        };
                        left = Self::recovery_sequence(left, residual);
                    }
                    break;
                }
                SyntaxKind::SuffixOperatorUse => {
                    let (_, left_power) = self.operator(next.node()?, OperatorFixity::Suffix)?;
                    if below_minimum(&left_power, minimum) {
                        break;
                    }
                    let item = self.take().ok_or(AssociationError::StructuralInvariant)?;
                    let operator = self.hir_operator(item.node()?, OperatorFixity::Suffix)?;
                    left = apply(operator, vec![left]);
                }
                SyntaxKind::InfixOperatorUse => {
                    let (left_power, _) = self.operator(next.node()?, OperatorFixity::Infix)?;
                    if below_minimum(&left_power, minimum) {
                        break;
                    }
                    let item = self.take().ok_or(AssociationError::StructuralInvariant)?;
                    let node = item.node()?;
                    let (_, right_power) = self.operator(node, OperatorFixity::Infix)?;
                    let operator = self.hir_operator(node, OperatorFixity::Infix)?;
                    let right = self.expression(Some(&right_power))?;
                    left = apply(operator, vec![left, right]);
                }
                // The parser normally prevents a second operand at a completed
                // chain cursor. Recovery can retain one, though. Keep every such
                // item in source order without inventing a dynamic application or
                // treating a retry operand as a second operand of the error.
                _ => {
                    let item = self.take().ok_or(AssociationError::StructuralInvariant)?;
                    let item = match self.classify_direct_item(&item)? {
                        DirectChainItem::Recovery => self.recovered_operand(item, minimum)?,
                        DirectChainItem::Prefix
                        | DirectChainItem::Infix
                        | DirectChainItem::Suffix
                        | DirectChainItem::Value => self.item_expression(&item)?,
                    };
                    left = Self::recovery_sequence(left, item);
                }
            }
        }
        Ok(left)
    }

    fn classify_direct_item(&self, item: &ChainItem) -> Result<DirectChainItem, AssociationError> {
        Ok(match item.kind() {
            SyntaxKind::Missing | SyntaxKind::Error | SyntaxKind::Invalid => {
                DirectChainItem::Recovery
            }
            SyntaxKind::PrefixOperatorUse => DirectChainItem::Prefix,
            SyntaxKind::InfixOperatorUse => DirectChainItem::Infix,
            SyntaxKind::SuffixOperatorUse => DirectChainItem::Suffix,
            SyntaxKind::NullfixOperatorUse => {
                self.definition(item.node()?, OperatorUseRole::Nullfix)?;
                DirectChainItem::Value
            }
            _ => DirectChainItem::Value,
        })
    }

    fn recovered_operand(
        &mut self,
        item: ChainItem,
        minimum: Option<&[i8]>,
    ) -> Result<HirExpr, AssociationError> {
        let recovery = self.item_expression(&item)?;
        let retry_operand = match self.peek() {
            Some(next) => self.classify_direct_item(next)?.is_retry_operand(),
            None => false,
        };
        if retry_operand {
            Ok(Self::recovery_sequence(recovery, self.expression(minimum)?))
        } else {
            Ok(recovery)
        }
    }

    fn item_expression(&mut self, item: &ChainItem) -> Result<HirExpr, AssociationError> {
        Ok(match item {
            ChainItem::Error(token) => Self::error(token.kind(), range_of_token(token)),
            ChainItem::Node(node) => match node.kind() {
                SyntaxKind::Invalid => self.invalid_expression(node)?,
                SyntaxKind::Missing | SyntaxKind::Error => Self::error(node.kind(), range_of(node)),
                SyntaxKind::PrefixOperatorUse => {
                    self.definition(node, OperatorUseRole::Prefix)?;
                    Self::error(node.kind(), range_of(node))
                }
                SyntaxKind::InfixOperatorUse => {
                    self.definition(node, OperatorUseRole::Infix)?;
                    Self::error(node.kind(), range_of(node))
                }
                SyntaxKind::SuffixOperatorUse => {
                    self.definition(node, OperatorUseRole::Suffix)?;
                    Self::error(node.kind(), range_of(node))
                }
                SyntaxKind::NullfixOperatorUse => {
                    self.definition(node, OperatorUseRole::Nullfix)?;
                    self.value(node)?
                }
                _ => self.value(node)?,
            },
        })
    }

    fn error(kind: SyntaxKind, range: Range<usize>) -> HirExpr {
        HirExpr::Error {
            kind,
            range,
            children: Vec::new(),
        }
    }

    fn invalid_expression(&mut self, node: &SyntaxNode) -> Result<HirExpr, AssociationError> {
        let mut children = Vec::new();
        self.collect_nested_items(node, &mut children)?;
        Ok(HirExpr::Error {
            kind: SyntaxKind::Invalid,
            range: range_of(node),
            children,
        })
    }

    fn structural_continuation(
        &mut self,
        left: HirExpr,
        node: &SyntaxNode,
    ) -> Result<HirExpr, AssociationError> {
        let HirExpr::Value {
            children: tail_children,
            ..
        } = self.value(node)?
        else {
            return Err(AssociationError::StructuralInvariant);
        };
        let mut children = Vec::with_capacity(tail_children.len() + 1);
        children.push(left);
        children.extend(tail_children);
        Ok(HirExpr::Value {
            kind: node.kind(),
            range: span(
                children
                    .first()
                    .ok_or(AssociationError::StructuralInvariant)?,
                node,
            ),
            children,
        })
    }

    fn recovery_sequence(left: HirExpr, item: HirExpr) -> HirExpr {
        let range =
            left.range().start.min(item.range().start)..left.range().end.max(item.range().end);
        HirExpr::Value {
            kind: SyntaxKind::OperatorChain,
            range,
            children: vec![left, item],
        }
    }

    fn value(&mut self, node: &SyntaxNode) -> Result<HirExpr, AssociationError> {
        let mut children = Vec::new();
        self.collect_nested_items(node, &mut children)?;
        Ok(HirExpr::Value {
            kind: node.kind(),
            range: range_of(node),
            children,
        })
    }

    fn collect_nested_items(
        &mut self,
        node: &SyntaxNode,
        output: &mut Vec<HirExpr>,
    ) -> Result<(), AssociationError> {
        for child in node.children_with_tokens() {
            if let Some(child) = child.as_node() {
                match child.kind() {
                    SyntaxKind::OperatorChain => {
                        output.push(associate_chain_owned(self.parsed, child.clone())?.into_hir());
                    }
                    SyntaxKind::Invalid => output.push(self.invalid_expression(child)?),
                    SyntaxKind::Missing | SyntaxKind::Error => {
                        output.push(Self::error(child.kind(), range_of(child)));
                    }
                    _ => self.collect_nested_items(child, output)?,
                }
            } else if let Some(token) = child.into_token()
                && token.kind() == SyntaxKind::Error
            {
                output.push(Self::error(token.kind(), range_of_token(&token)));
            }
        }
        Ok(())
    }

    fn peek(&self) -> Option<&ChainItem> {
        self.children.get(self.cursor)
    }

    fn take(&mut self) -> Option<ChainItem> {
        let node = self.peek()?.clone();
        self.cursor += 1;
        Some(node)
    }

    fn operator(
        &self,
        node: &SyntaxNode,
        fixity: OperatorFixity,
    ) -> Result<(Vec<i8>, Vec<i8>), AssociationError> {
        let definition = self.definition(
            node,
            match fixity {
                OperatorFixity::Prefix => OperatorUseRole::Prefix,
                OperatorFixity::Infix => OperatorUseRole::Infix,
                OperatorFixity::Suffix => OperatorUseRole::Suffix,
            },
        )?;
        Ok(match fixity {
            OperatorFixity::Prefix => (
                Vec::new(),
                definition
                    .prefix_right_binding_power()
                    .map(|power| power.to_vec())
                    .ok_or(AssociationError::ExactOperatorEnvironment)?,
            ),
            OperatorFixity::Infix => definition
                .infix_binding_powers()
                .map(|(left, right)| (left.to_vec(), right.to_vec()))
                .ok_or(AssociationError::ExactOperatorEnvironment)?,
            OperatorFixity::Suffix => (
                definition
                    .suffix_left_binding_power()
                    .map(|power| power.to_vec())
                    .ok_or(AssociationError::ExactOperatorEnvironment)?,
                Vec::new(),
            ),
        })
    }

    fn hir_operator(
        &self,
        node: &SyntaxNode,
        fixity: OperatorFixity,
    ) -> Result<HirOperator, AssociationError> {
        let definition = self.definition(
            node,
            match fixity {
                OperatorFixity::Prefix => OperatorUseRole::Prefix,
                OperatorFixity::Infix => OperatorUseRole::Infix,
                OperatorFixity::Suffix => OperatorUseRole::Suffix,
            },
        )?;
        Ok(HirOperator {
            spelling: definition.spelling().to_owned(),
            fixity,
            range: range_of(node),
        })
    }

    fn definition(
        &self,
        node: &SyntaxNode,
        role: OperatorUseRole,
    ) -> Result<yu_syntax::OperatorDefinition<'_>, AssociationError> {
        let spelling = node
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .find(|token| token.kind() == SyntaxKind::Operator)
            .map(|token| token.text().to_owned())
            .ok_or(AssociationError::StructuralInvariant)?;
        let definition = self
            .parsed
            .operators()
            .definition(&spelling)
            .ok_or(AssociationError::ExactOperatorEnvironment)?;
        let present = match role {
            OperatorUseRole::Prefix => definition.prefix_right_binding_power().is_some(),
            OperatorUseRole::Infix => definition.infix_binding_powers().is_some(),
            OperatorUseRole::Suffix => definition.suffix_left_binding_power().is_some(),
            OperatorUseRole::Nullfix => definition.is_nullfix(),
        };
        present
            .then_some(definition)
            .ok_or(AssociationError::ExactOperatorEnvironment)
    }
}

fn apply(operator: HirOperator, operands: Vec<HirExpr>) -> HirExpr {
    let start = operator.range.start.min(
        operands
            .first()
            .map_or(operator.range.start, |expr| expr.range().start),
    );
    let end = operator.range.end.max(
        operands
            .last()
            .map_or(operator.range.end, |expr| expr.range().end),
    );
    HirExpr::Apply {
        operator,
        operands: operands.into_boxed_slice(),
        range: start..end,
    }
}

fn below_minimum(power: &[i8], minimum: Option<&[i8]>) -> bool {
    minimum.is_some_and(|minimum| compare_power(power, minimum) == Ordering::Less)
}

fn compare_power(left: &[i8], right: &[i8]) -> Ordering {
    (0..left.len().max(right.len()))
        .map(|index| {
            left.get(index)
                .copied()
                .unwrap_or(0)
                .cmp(&right.get(index).copied().unwrap_or(0))
        })
        .find(|ordering| *ordering != Ordering::Equal)
        .unwrap_or(Ordering::Equal)
}

fn is_fixed_postfix(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::CallTail
            | SyntaxKind::IndexTail
            | SyntaxKind::ProjectionTupleTail
            | SyntaxKind::ProjectionRecordTail
            | SyntaxKind::FieldTail
            | SyntaxKind::PathTail
    )
}

fn is_terminal_outer_tail(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::ColonApplicationTail | SyntaxKind::AssignmentTail | SyntaxKind::WithBodyTail
    )
}

fn span(left: &HirExpr, tail: &SyntaxNode) -> Range<usize> {
    left.range().start.min(range_of(tail).start)..left.range().end.max(range_of(tail).end)
}

fn range_of(node: &SyntaxNode) -> Range<usize> {
    let range = node.text_range();
    u32::from(range.start()) as usize..u32::from(range.end()) as usize
}

fn range_of_token(token: &SyntaxToken) -> Range<usize> {
    let range = token.text_range();
    u32::from(range.start()) as usize..u32::from(range.end()) as usize
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;
    use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

    const FIXTURE: &str = include_str!(
        "../../../tests/contracts/phase2-parser/v0/cases/header-operator-order-plus-then-star/main.yu"
    );

    fn parsed(source: &str) -> ParsedFile {
        let source: Arc<SourceText> = Arc::from(source);
        let header = Arc::new(scan_header(source.clone()));
        parse_file(source, header, Arc::new(SyntaxEnvironment::empty()))
    }

    fn parse(source: &str) -> AssociatedChains {
        associate_operator_chains(&parsed(source))
    }

    #[test]
    fn associates_the_approved_header_operator_fixture() {
        let source: Arc<SourceText> = Arc::from(FIXTURE);
        let header = Arc::new(scan_header(source.clone()));
        let parsed = parse_file(source, header, Arc::new(SyntaxEnvironment::empty()));
        let associated = associate_operator_chains(&parsed);

        // The two operator-definition bodies are top-level chains too. The
        // source body is last because the product preserves source order.
        assert_eq!(associated.chains().len(), 3);
        let HirExpr::Apply {
            operator, operands, ..
        } = associated
            .chains()
            .last()
            .expect("source body chain")
            .expression()
        else {
            panic!("outer plus application")
        };
        assert_eq!(operator.spelling(), "<+>");
        assert_eq!(operator.fixity(), OperatorFixity::Infix);
        assert_eq!(operands.len(), 2);
        let HirExpr::Apply {
            operator, operands, ..
        } = &operands[1]
        else {
            panic!("star binds inside plus right operand")
        };
        assert_eq!(operator.spelling(), "<*>");
        assert_eq!(operands.len(), 2);
    }

    fn value(expression: &HirExpr) -> (SyntaxKind, &[HirExpr]) {
        let HirExpr::Value { kind, children, .. } = expression else {
            panic!("expected structural value, got {expression:?}")
        };
        (*kind, children)
    }

    #[test]
    fn associates_structural_postfixes_before_the_enclosing_chain() {
        let associated = parse("f(x)[y].field::name arg as Int");
        assert_eq!(
            associated.chains().len(),
            1,
            "only the enclosing top-level chain is retained"
        );

        let (kind, children) = value(associated.chains().last().unwrap().expression());
        assert_eq!(kind, SyntaxKind::TypeAnnotationTail);
        let (kind, children) = value(&children[0]);
        assert_eq!(kind, SyntaxKind::MlArgument);
        let (kind, children) = value(&children[0]);
        assert_eq!(kind, SyntaxKind::PathTail);
        let (kind, children) = value(&children[0]);
        assert_eq!(kind, SyntaxKind::FieldTail);
        let (kind, children) = value(&children[0]);
        assert_eq!(kind, SyntaxKind::IndexTail);
        let (kind, children) = value(&children[0]);
        assert_eq!(kind, SyntaxKind::CallTail);
        assert_eq!(children.len(), 2, "target then nested call argument");
        assert_eq!(value(&children[0]).0, SyntaxKind::IdentifierExpression);
        assert_eq!(value(&children[1]).0, SyntaxKind::IdentifierExpression);
    }

    #[test]
    fn associates_projection_tails_as_structural_continuations() {
        let associated = parse("f.(x).{y}.field::name");
        assert_eq!(
            associated.chains().len(),
            1,
            "only the enclosing top-level chain is retained"
        );

        let (kind, children) = value(associated.chains().last().unwrap().expression());
        assert_eq!(kind, SyntaxKind::PathTail);
        let (kind, children) = value(&children[0]);
        assert_eq!(kind, SyntaxKind::FieldTail);
        let (kind, children) = value(&children[0]);
        assert_eq!(kind, SyntaxKind::ProjectionRecordTail);
        assert_eq!(value(&children[0]).0, SyntaxKind::ProjectionTupleTail);
    }

    #[test]
    fn preserves_recovery_provenance_without_double_operandization() {
        let associated = parse("infix (<+>) 40 41 = left\nf <+> @ g");
        let HirExpr::Apply { operands, .. } = associated.chains().last().unwrap().expression()
        else {
            panic!("infix application")
        };
        assert_eq!(operands.len(), 2);
        let (kind, children) = value(&operands[1]);
        assert_eq!(kind, SyntaxKind::OperatorChain);
        assert!(matches!(
            children,
            [
                HirExpr::Error {
                    kind: SyntaxKind::Error,
                    range,
                    ..
                },
                HirExpr::Value {
                    kind: SyntaxKind::IdentifierExpression,
                    range: retry_range,
                    ..
                },
            ] if range == &(31..32) && retry_range == &(32..34)
        ));

        let missing = parse("f =");
        let (kind, children) = value(missing.chains().last().unwrap().expression());
        assert_eq!(kind, SyntaxKind::AssignmentTail);
        assert!(matches!(
            children.last(),
            Some(HirExpr::Error {
                kind: SyntaxKind::Missing,
                range,
                ..
            }) if range == &(3..3)
        ));
    }

    #[test]
    fn associates_a_prefix_retry_after_direct_recovery_noise() {
        let associated =
            parse("infix (<+>) 40 41 = left\nprefix (<~>) 70 = right\nf <+> @ <~> value");
        let HirExpr::Apply { operands, .. } = associated.chains().last().unwrap().expression()
        else {
            panic!("infix application")
        };
        let (kind, children) = value(&operands[1]);
        assert_eq!(kind, SyntaxKind::OperatorChain);
        assert!(matches!(
            children,
            [
                HirExpr::Error {
                    kind: SyntaxKind::Error,
                    children: recovery_children,
                    ..
                },
                HirExpr::Apply {
                    operator,
                    operands,
                    ..
                },
            ] if recovery_children.is_empty()
                && operator.spelling() == "<~>"
                && operator.fixity() == OperatorFixity::Prefix
                && matches!(operands.as_ref(), [HirExpr::Value {
                    kind: SyntaxKind::IdentifierExpression,
                    ..
                }])
        ));
    }

    #[test]
    fn validates_nullfix_uses_against_the_exact_parsed_operator_table() {
        let parsed = parsed("nullfix (?) = body\n?");
        assert!(
            parsed
                .operators()
                .definition("?")
                .is_some_and(|definition| definition.is_nullfix())
        );
        let associated = associate_operator_chains(&parsed);
        assert!(matches!(
            associated.chains().last().unwrap().expression(),
            HirExpr::Value {
                kind: SyntaxKind::NullfixOperatorUse,
                children,
                ..
            } if children.is_empty()
        ));
    }

    #[test]
    fn keeps_structured_invalid_and_its_nested_recovery_inside_the_outer_chain() {
        let associated = parse("f as :{123::}");
        assert_eq!(associated.chains().len(), 1);
        let (kind, children) = value(associated.chains().last().unwrap().expression());
        assert_eq!(kind, SyntaxKind::TypeAnnotationTail);
        let invalid = children
            .iter()
            .find(|child| {
                matches!(
                    child,
                    HirExpr::Error {
                        kind: SyntaxKind::Invalid,
                        ..
                    }
                )
            })
            .expect("the structured Invalid stays inside the type annotation");
        let HirExpr::Error {
            kind: SyntaxKind::Invalid,
            children: invalid_children,
            ..
        } = invalid
        else {
            unreachable!("the filter requires structured Invalid")
        };
        assert!(matches!(
            invalid_children.as_slice(),
            [HirExpr::Error {
                kind: SyntaxKind::Missing,
                children,
                ..
            }] if children.is_empty()
        ));
    }

    #[test]
    fn direct_structured_invalid_item_retains_its_nested_recovery() {
        let parsed = parsed("f as :{123::}");
        let root = SyntaxNode::new_root(parsed.green().clone());
        let invalid = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::Invalid)
            .expect("structured Invalid from accepted recovery syntax");
        let children = [ChainItem::Node(invalid)];
        let mut parser = ChainParser {
            children: &children,
            cursor: 0,
            parsed: &parsed,
        };
        let expression = parser
            .expression(None)
            .expect("accepted recovery syntax keeps association invariants");
        assert_eq!(parser.cursor, children.len());
        assert!(matches!(
            expression,
            HirExpr::Error {
                kind: SyntaxKind::Invalid,
                children,
                ..
            } if matches!(children.as_slice(), [HirExpr::Error {
                kind: SyntaxKind::Missing,
                children,
                ..
            }] if children.is_empty())
        ));
    }

    #[test]
    fn terminal_tail_receives_the_reduced_dynamic_segment() {
        let associated = parse("infix (<+>) 40 41 = left\nf <+> g = h");
        let (kind, children) = value(associated.chains().last().unwrap().expression());
        assert_eq!(kind, SyntaxKind::AssignmentTail);
        assert!(matches!(
            children.first(),
            Some(HirExpr::Apply { operator, .. }) if operator.spelling() == "<+>"
        ));
    }

    #[test]
    fn type_annotation_receives_the_reduced_dynamic_segment() {
        let associated = parse("infix (<+>) 40 41 = left\nf <+> g as Int");
        let (kind, children) = value(associated.chains().last().unwrap().expression());
        assert_eq!(kind, SyntaxKind::TypeAnnotationTail);
        assert!(matches!(
            children.first(),
            Some(HirExpr::Apply { operator, .. }) if operator.spelling() == "<+>"
        ));
    }
}
