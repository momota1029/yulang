//! The first, deliberately narrow, HIR-adjacent association product.

use std::{cmp::Ordering, ops::Range};

use yu_syntax::{ParsedFile, SyntaxKind, SyntaxNode, SyntaxToken};

mod module;

#[cfg(any(feature = "shadow", test))]
pub mod shadow;

pub use module::{
    DefId, DefinitionRootId, FileId, FileKey, HirAvailabilityError, HirBinding, HirDiagnostic,
    HirDiagnosticId, HirError, HirErrorAttachment, HirErrorId, HirErrorKind, HirErrorOrigin,
    HirItem, HirModule, HirName, HirOccurrenceId, HirParameter, HirParameterId, HirVisibility,
    ModuleId, ModuleIdentity, NameResolution, ResolvedExpr, SemanticImports, lower_module,
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
    #[cfg(any(feature = "shadow", test))]
    source: SyntaxNode,
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
        #[cfg(any(feature = "shadow", test))]
        source: child.clone(),
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
    mod shadow_annotation_positions;
    mod shadow_call_source_occurrences;
    mod shadow_call_use_source_inputs;
    mod shadow_resolved_call_incidence;
    mod shadow_source_core;

    use std::{collections::HashMap, sync::Arc};

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

    fn collect_call_stage_ranges(
        expression: &HirExpr,
        expected_stage: SyntaxKind,
        calls: &mut Vec<Range<usize>>,
        arguments: &mut Vec<Range<usize>>,
    ) {
        let (kind, children) = value(expression);
        if kind == SyntaxKind::IdentifierExpression {
            assert!(children.is_empty());
            return;
        }
        assert_eq!(kind, expected_stage, "every stage uses the source form");
        assert_eq!(children.len(), 2, "one target and one argument stage");
        collect_call_stage_ranges(&children[0], expected_stage, calls, arguments);
        assert_eq!(
            value(&children[1]).0,
            SyntaxKind::IdentifierExpression,
            "the bounded argument is a name leaf"
        );
        assert!(value(&children[1]).1.is_empty());
        arguments.push(children[1].range().clone());
        calls.push(expression.range().clone());
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
    fn research_call_surface_retains_left_associated_stages() {
        for (stage_kind, parenthesized) in [
            (SyntaxKind::CallTail, true),
            (SyntaxKind::MlArgument, false),
        ] {
            for stage_count in 1..=4 {
                let mut source = "f".to_owned();
                let mut expected_call_ranges = Vec::new();
                let mut expected_argument_ranges = Vec::new();
                for index in 0..stage_count {
                    let argument = char::from(b'a' + index);
                    if parenthesized {
                        source.push('(');
                        let start = source.len();
                        source.push(argument);
                        expected_argument_ranges.push(start..source.len());
                        source.push(')');
                    } else {
                        source.push(' ');
                        let start = source.len();
                        source.push(argument);
                        expected_argument_ranges.push(start..source.len());
                    }
                    expected_call_ranges.push(0..source.len());
                }

                let associated = parse(&source);
                assert_eq!(associated.chains().len(), 1, "{source}");
                let expression = associated.chains()[0].expression();
                assert_eq!(
                    value(expression).0,
                    stage_kind,
                    "the outer node is one ordinary argument stage"
                );
                let mut actual_call_ranges = Vec::new();
                let mut actual_argument_ranges = Vec::new();
                collect_call_stage_ranges(
                    expression,
                    stage_kind,
                    &mut actual_call_ranges,
                    &mut actual_argument_ranges,
                );
                assert_eq!(actual_call_ranges, expected_call_ranges, "{source}");
                assert_eq!(actual_argument_ranges, expected_argument_ranges, "{source}");
            }
        }
    }

    #[derive(Clone, Debug, Eq, PartialEq)]
    enum ResearchApply {
        Atom {
            name: String,
            range: Range<usize>,
        },
        Group {
            range: Range<usize>,
            children: Vec<ResearchApply>,
        },
        Apply {
            occurrence: u32,
            form: SyntaxKind,
            range: Range<usize>,
            callee: Box<ResearchApply>,
            argument: Box<ResearchApply>,
        },
    }

    #[derive(Clone, Debug, Eq, PartialEq)]
    enum ResearchScopedExpr {
        Lambda {
            binder: u32,
            body: Box<ResearchScopedExpr>,
        },
        Variable {
            binder: u32,
        },
        Apply {
            occurrence: u32,
            callee: Box<ResearchScopedExpr>,
            argument: Box<ResearchScopedExpr>,
        },
    }

    fn research_identifier(node: &SyntaxNode, source: &str) -> (String, Range<usize>) {
        assert_eq!(node.kind(), SyntaxKind::IdentifierPattern);
        let tokens = node
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .collect::<Vec<_>>();
        let [token] = tokens.as_slice() else {
            panic!("research binder is one identifier token")
        };
        assert_eq!(token.kind(), SyntaxKind::Identifier);
        let range = range_of_token(token);
        (source[range.clone()].to_owned(), range)
    }

    fn research_binding_parameters(
        statement: &SyntaxNode,
        source: &str,
    ) -> Vec<(String, Range<usize>)> {
        let headers = statement
            .children()
            .filter(|node| node.kind() == SyntaxKind::BindingHeader)
            .collect::<Vec<_>>();
        assert_eq!(headers.len(), 1);
        let targets = headers[0]
            .children()
            .filter(|node| node.kind() == SyntaxKind::Pattern)
            .collect::<Vec<_>>();
        assert_eq!(targets.len(), 1);
        let parts = targets[0].children().collect::<Vec<_>>();
        assert!(parts.len() >= 2, "research case has a name and parameters");
        assert_eq!(parts[0].kind(), SyntaxKind::IdentifierPattern);

        let mut parameters = Vec::new();
        for tail in &parts[1..] {
            assert_eq!(tail.kind(), SyntaxKind::PatternMlApplicationTail);
            let arguments = tail.children().collect::<Vec<_>>();
            let [argument] = arguments.as_slice() else {
                panic!("each bounded source tail has one pattern")
            };
            assert_eq!(argument.kind(), SyntaxKind::Pattern);
            let binders = argument.children().collect::<Vec<_>>();
            let [binder] = binders.as_slice() else {
                panic!("each bounded parameter pattern is atomic")
            };
            parameters.push(research_identifier(binder, source));
        }
        assert!(!parameters.is_empty());
        assert_eq!(
            parameters
                .iter()
                .map(|(name, _)| name)
                .collect::<std::collections::HashSet<_>>()
                .len(),
            parameters.len(),
            "the bounded candidates use distinct parameter names"
        );
        parameters
    }

    fn research_resolve_scoped_apply(
        expression: &ResearchApply,
        environment: &[(String, u32)],
    ) -> ResearchScopedExpr {
        match expression {
            ResearchApply::Atom { name, .. } => ResearchScopedExpr::Variable {
                binder: environment
                    .iter()
                    .rev()
                    .find_map(|(bound, binder)| (bound == name).then_some(*binder))
                    .unwrap_or_else(|| panic!("unbound research name {name}")),
            },
            ResearchApply::Group { children, .. } => {
                let [inner] = children.as_slice() else {
                    panic!("one grouped research expression")
                };
                research_resolve_scoped_apply(inner, environment)
            }
            ResearchApply::Apply {
                occurrence,
                callee,
                argument,
                ..
            } => ResearchScopedExpr::Apply {
                occurrence: *occurrence,
                callee: Box::new(research_resolve_scoped_apply(callee, environment)),
                argument: Box::new(research_resolve_scoped_apply(argument, environment)),
            },
        }
    }

    fn research_lower_binding_candidate(
        statement: &SyntaxNode,
        parsed: &ParsedFile,
        source: &str,
    ) -> (Vec<(String, Range<usize>)>, ResearchScopedExpr) {
        let parameters = research_binding_parameters(statement, source);
        let bodies = statement
            .children()
            .filter(|node| node.kind() == SyntaxKind::BindingBody)
            .collect::<Vec<_>>();
        assert_eq!(bodies.len(), 1);
        let chains = bodies[0]
            .children()
            .filter(|node| node.kind() == SyntaxKind::OperatorChain)
            .collect::<Vec<_>>();
        assert_eq!(chains.len(), 1);
        let associated = associate_chain_owned(parsed, chains[0].clone())
            .expect("use the source's retained operator environment")
            .into_hir();
        assert!(
            research_expression_is_valid(&associated),
            "{source}: {associated:#?}"
        );
        let mut next_occurrence = 0;
        let body = research_lower_apply(&associated, source, &mut next_occurrence);
        let mut environment = Vec::new();
        for (binder, (name, _)) in parameters.iter().enumerate() {
            environment.push((name.clone(), binder as u32));
        }
        let mut expression = research_resolve_scoped_apply(&body, &environment);
        for binder in (0..parameters.len()).rev() {
            expression = ResearchScopedExpr::Lambda {
                binder: binder as u32,
                body: Box::new(expression),
            };
        }
        (parameters, expression)
    }

    fn research_lower_apply(expression: &HirExpr, source: &str, next: &mut u32) -> ResearchApply {
        let HirExpr::Value {
            kind,
            range,
            children,
        } = expression
        else {
            panic!("the candidate handles only valid source expressions: {expression:?}");
        };
        match *kind {
            SyntaxKind::MlArgument | SyntaxKind::CallTail => {
                assert_eq!(children.len(), 2, "one target and one whole argument");
                let occurrence = *next;
                *next += 1;
                ResearchApply::Apply {
                    occurrence,
                    form: *kind,
                    range: range.clone(),
                    callee: Box::new(research_lower_apply(&children[0], source, next)),
                    argument: Box::new(research_lower_apply(&children[1], source, next)),
                }
            }
            SyntaxKind::ParenthesizedExpression => ResearchApply::Group {
                range: range.clone(),
                children: children
                    .iter()
                    .map(|child| research_lower_apply(child, source, next))
                    .collect(),
            },
            SyntaxKind::IdentifierExpression => {
                assert!(children.is_empty(), "identifier leaf");
                ResearchApply::Atom {
                    name: source[range.clone()].to_owned(),
                    range: range.clone(),
                }
            }
            _ => panic!("unsupported research Apply operand: {kind:?}"),
        }
    }

    fn research_expression_is_valid(expression: &HirExpr) -> bool {
        match expression {
            HirExpr::Error { .. } => false,
            HirExpr::Value { children, .. } => children.iter().all(research_expression_is_valid),
            HirExpr::Apply { operands, .. } => operands.iter().all(research_expression_is_valid),
        }
    }

    fn research_apply_spine(expression: &ResearchApply) -> Vec<(SyntaxKind, Range<usize>)> {
        match expression {
            ResearchApply::Atom { .. } => Vec::new(),
            ResearchApply::Group { children, .. } => {
                children.iter().flat_map(research_apply_spine).collect()
            }
            ResearchApply::Apply {
                form,
                range,
                callee,
                argument,
                ..
            } => {
                let mut result = research_apply_spine(callee);
                result.push((*form, range.clone()));
                result.extend(research_apply_spine(argument));
                result
            }
        }
    }

    fn research_apply_arguments_are_atoms(expression: &ResearchApply) -> bool {
        match expression {
            ResearchApply::Atom { .. } => true,
            ResearchApply::Group { children, .. } => {
                children.iter().all(research_apply_arguments_are_atoms)
            }
            ResearchApply::Apply {
                callee, argument, ..
            } => {
                matches!(argument.as_ref(), ResearchApply::Atom { .. })
                    && research_apply_arguments_are_atoms(callee)
            }
        }
    }

    fn research_apply_atoms(expression: &ResearchApply, into: &mut Vec<(String, Range<usize>)>) {
        match expression {
            ResearchApply::Atom { name, range } => into.push((name.clone(), range.clone())),
            ResearchApply::Group { children, .. } => {
                for child in children {
                    research_apply_atoms(child, into);
                }
            }
            ResearchApply::Apply {
                callee, argument, ..
            } => {
                research_apply_atoms(callee, into);
                research_apply_atoms(argument, into);
            }
        }
    }

    fn expected_research_atoms(source: &str) -> Vec<(String, Range<usize>)> {
        let mut atoms = Vec::new();
        let mut start = None;
        for (index, character) in source.char_indices() {
            if character.is_ascii_alphabetic() {
                start.get_or_insert(index);
            } else if let Some(atom_start) = start.take() {
                atoms.push((source[atom_start..index].to_owned(), atom_start..index));
            }
        }
        if let Some(atom_start) = start {
            atoms.push((source[atom_start..].to_owned(), atom_start..source.len()));
        }
        atoms
    }

    // A test-only notation mirror of typed-core §6, not an executable core API.
    // Effect strings are labels only: this model omits port profiles, K,D,
    // invocation/subtraction evidence, and complete application constraints.
    #[derive(Clone, Debug, Eq, PartialEq)]
    enum ResearchInterface {
        Value { value: String },
        Computation { effect: String, value: String },
    }

    impl ResearchInterface {
        fn value_endpoint(&self) -> &str {
            match self {
                Self::Value { value } | Self::Computation { value, .. } => value,
            }
        }
    }

    #[derive(Clone, Debug, Eq, PartialEq)]
    enum ResearchData {
        Name(String),
        ReifiedCall {
            callee: Box<ResearchComputation>,
            argument: Box<ResearchComputation>,
        },
    }

    #[derive(Clone, Debug, Eq, PartialEq)]
    enum ResearchComputation {
        Result(Box<ResearchData>),
        Eliminate {
            effect: String,
            data: Box<ResearchData>,
        },
    }

    #[derive(Clone, Debug, Eq, PartialEq)]
    struct ResearchSynthesis {
        interface: ResearchInterface,
        data: ResearchData,
        normalized: ResearchComputation,
    }

    #[derive(Clone, Debug, Eq, PartialEq)]
    struct ResearchApplicationProjection {
        // This is only the structural endpoint triple from the pure shadow;
        // it does not assert or solve a concrete Function inequality.
        occurrence: u32,
        callee_value: String,
        argument_value: String,
        result_value: String,
    }

    fn research_normalize(
        interface: &ResearchInterface,
        data: ResearchData,
    ) -> ResearchComputation {
        match interface {
            ResearchInterface::Value { .. } => ResearchComputation::Result(Box::new(data)),
            ResearchInterface::Computation { effect, .. } => ResearchComputation::Eliminate {
                effect: effect.clone(),
                data: Box::new(data),
            },
        }
    }

    fn research_synthesize(
        expression: &ResearchApply,
        gamma: &HashMap<String, ResearchInterface>,
        projections: &mut Vec<ResearchApplicationProjection>,
    ) -> ResearchSynthesis {
        match expression {
            ResearchApply::Atom { name, .. } => {
                let interface = gamma
                    .get(name)
                    .unwrap_or_else(|| panic!("unknown research name {name}"))
                    .clone();
                let data = ResearchData::Name(name.clone());
                let normalized = research_normalize(&interface, data.clone());
                ResearchSynthesis {
                    interface,
                    data,
                    normalized,
                }
            }
            ResearchApply::Group { children, .. } => {
                let [inner] = children.as_slice() else {
                    panic!("a source grouping denotes exactly one research expression");
                };
                research_synthesize(inner, gamma, projections)
            }
            ResearchApply::Apply {
                occurrence,
                callee,
                argument,
                ..
            } => {
                let callee = research_synthesize(callee, gamma, projections);
                let argument = research_synthesize(argument, gamma, projections);
                let result_value = format!("call{occurrence}.value");
                let effect = format!("call{occurrence}.effect");
                projections.push(ResearchApplicationProjection {
                    occurrence: *occurrence,
                    callee_value: callee.interface.value_endpoint().to_owned(),
                    argument_value: argument.interface.value_endpoint().to_owned(),
                    result_value: result_value.clone(),
                });
                let interface = ResearchInterface::Computation {
                    effect,
                    value: result_value,
                };
                let data = ResearchData::ReifiedCall {
                    callee: Box::new(callee.normalized),
                    argument: Box::new(argument.normalized),
                };
                let normalized = research_normalize(&interface, data.clone());
                ResearchSynthesis {
                    interface,
                    data,
                    normalized,
                }
            }
        }
    }

    #[test]
    fn research_apply_lowering_preserves_mixed_unary_call_spines() {
        // This is a test-only candidate for the reviewed ResolvedExpr::Apply
        // shape. It consumes actual parser/associator output; production HIR
        // lowering and constraint generation remain unchanged.
        let mut valid_cases = 0;
        let mut valid_patterns = Vec::new();
        for stage_count in 1..=4 {
            for forms in 0..(1 << stage_count) {
                let mut source = String::from("f");
                let mut expected_forms = Vec::new();
                for index in 0..stage_count {
                    if forms & (1 << index) == 0 {
                        source.push(' ');
                        source.push(char::from(b'a' + index as u8));
                        expected_forms.push(SyntaxKind::MlArgument);
                    } else {
                        if index > 0 {
                            source = format!("({source})");
                        }
                        source.push('(');
                        source.push(char::from(b'a' + index as u8));
                        source.push(')');
                        expected_forms.push(SyntaxKind::CallTail);
                    }
                }
                let associated = parse(&source);
                assert_eq!(associated.chains().len(), 1, "{source}");
                if !research_expression_is_valid(associated.chains()[0].expression()) {
                    continue;
                }
                valid_cases += 1;
                valid_patterns.push((stage_count, forms));
                let mut next = 0;
                let candidate =
                    research_lower_apply(associated.chains()[0].expression(), &source, &mut next);
                assert!(
                    research_apply_arguments_are_atoms(&candidate),
                    "generated grouped-spine stages keep atomic operands: {source}"
                );
                let spine = research_apply_spine(&candidate);
                assert_eq!(spine.len(), stage_count, "{source}");
                assert_eq!(
                    spine.iter().map(|(form, _)| *form).collect::<Vec<_>>(),
                    expected_forms,
                    "{source}"
                );
                assert_eq!(spine.last().unwrap().1, *associated.chains()[0].range());
                let mut occurrences = Vec::new();
                fn gather_occurrences(expression: &ResearchApply, into: &mut Vec<u32>) {
                    match expression {
                        ResearchApply::Atom { .. } => {}
                        ResearchApply::Group { children, .. } => {
                            for child in children {
                                gather_occurrences(child, into);
                            }
                        }
                        ResearchApply::Apply {
                            occurrence,
                            callee,
                            argument,
                            ..
                        } => {
                            into.push(*occurrence);
                            gather_occurrences(callee, into);
                            gather_occurrences(argument, into);
                        }
                    }
                }
                gather_occurrences(&candidate, &mut occurrences);
                occurrences.sort_unstable();
                occurrences.dedup();
                assert_eq!(
                    occurrences.len(),
                    stage_count,
                    "unique Apply occurrence ids"
                );
                assert_eq!(next as usize, stage_count);
            }
        }
        assert_eq!(
            valid_cases, 14,
            "fixed subset of generated sources is recovery-free"
        );
        assert_eq!(
            valid_patterns,
            [
                (1, 0),
                (1, 1),
                (2, 0),
                (2, 1),
                (2, 3),
                (3, 0),
                (3, 1),
                (3, 3),
                (3, 7),
                (4, 0),
                (4, 1),
                (4, 3),
                (4, 7),
                (4, 15),
            ],
            "the enumerated recovery-free subset is fixed"
        );
    }

    #[test]
    fn research_binding_body_cst_flows_to_apply_candidate() {
        // This consumes the exact body node retained by the parser for the
        // principal-type fixture. It stops before production declaration
        // admission and resolved-HIR construction.
        let source = "my call f x = f x";
        let parsed = parsed(source);
        let root = SyntaxNode::new_root(parsed.green().clone());
        let bindings = root
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::BindingStatement)
            .collect::<Vec<_>>();
        assert_eq!(bindings.len(), 1);
        let bodies = bindings[0]
            .children()
            .filter(|node| node.kind() == SyntaxKind::BindingBody)
            .collect::<Vec<_>>();
        assert_eq!(bodies.len(), 1);
        let chains = bodies[0]
            .children()
            .filter(|node| node.kind() == SyntaxKind::OperatorChain)
            .collect::<Vec<_>>();
        assert_eq!(chains.len(), 1);
        assert_eq!(range_of(&chains[0]), 14..17);

        let associated = associate_chain_owned(&parsed, chains[0].clone())
            .expect("the original parser operator environment is retained")
            .into_hir();
        assert!(research_expression_is_valid(&associated));
        let mut next = 0;
        let candidate = research_lower_apply(&associated, source, &mut next);
        assert_eq!(next, 1);
        assert_eq!(
            candidate,
            ResearchApply::Apply {
                occurrence: 0,
                form: SyntaxKind::MlArgument,
                range: 14..17,
                callee: Box::new(ResearchApply::Atom {
                    name: "f".to_owned(),
                    range: 14..15,
                }),
                argument: Box::new(ResearchApply::Atom {
                    name: "x".to_owned(),
                    range: 16..17,
                }),
            }
        );
    }

    fn research_scoped_shape(expression: &ResearchScopedExpr) -> String {
        match expression {
            ResearchScopedExpr::Lambda { binder, body } => {
                format!("λ{binder}.{}", research_scoped_shape(body))
            }
            ResearchScopedExpr::Variable { binder } => format!("v{binder}"),
            ResearchScopedExpr::Apply {
                callee, argument, ..
            } => format!(
                "({} {})",
                research_scoped_shape(callee),
                research_scoped_shape(argument)
            ),
        }
    }

    fn research_scoped_call_count(expression: &ResearchScopedExpr) -> usize {
        match expression {
            ResearchScopedExpr::Lambda { body, .. } => research_scoped_call_count(body),
            ResearchScopedExpr::Variable { .. } => 0,
            ResearchScopedExpr::Apply {
                callee, argument, ..
            } => 1 + research_scoped_call_count(callee) + research_scoped_call_count(argument),
        }
    }

    // Structural §6 characterization only: these symbolic endpoints and lambda
    // bodies neither define complete Function membership nor solve effects,
    // comparison direction, principal schemes, or source/core execution adequacy.
    #[derive(Clone, Debug, Eq, PartialEq)]
    enum ResearchScopedValue {
        Endpoint {
            fiber: u32,
            binder: u32,
        },
        CallEndpoint {
            fiber: u32,
            occurrence: u32,
        },
        Function {
            parameter: Box<ResearchScopedValue>,
            result: Box<ResearchScopedResult>,
        },
    }

    #[derive(Clone, Debug, Eq, PartialEq)]
    struct ResearchScopedResult {
        // None is the empty effect of Result(Value(A)); Some is symbolic E_call.
        effect: Option<(u32, u32)>,
        value: ResearchScopedValue,
    }

    #[derive(Clone, Debug, Eq, PartialEq)]
    enum ResearchScopedData {
        Name(u32),
        Lambda {
            binder: u32,
            parameter: ResearchScopedValue,
            body: Box<ResearchScopedCore>,
        },
        ReifiedCall {
            occurrence: u32,
            callee: Box<ResearchScopedCore>,
            argument: Box<ResearchScopedCore>,
        },
    }

    #[derive(Clone, Debug, Eq, PartialEq)]
    struct ResearchScopedCore {
        result: ResearchScopedResult,
        data: ResearchScopedData,
        // false denotes result(d), true denotes eliminate_p(d). This records
        // construction of consumption, never execution of the derivation.
        eliminate: bool,
    }

    #[derive(Clone, Debug, Eq, PartialEq)]
    struct ResearchScopedCallEvidence {
        occurrence: u32,
        scope: Vec<u32>,
        argument: ResearchScopedResult,
        result: ResearchScopedResult,
    }

    fn research_synthesize_scoped(
        expression: &ResearchScopedExpr,
        fiber: u32,
        scope: &mut Vec<u32>,
        calls: &mut Vec<ResearchScopedCallEvidence>,
    ) -> ResearchScopedCore {
        match expression {
            ResearchScopedExpr::Variable { binder } => {
                assert!(
                    scope.contains(binder),
                    "name must resolve in its lambda scope"
                );
                ResearchScopedCore {
                    result: ResearchScopedResult {
                        effect: None,
                        value: ResearchScopedValue::Endpoint {
                            fiber,
                            binder: *binder,
                        },
                    },
                    data: ResearchScopedData::Name(*binder),
                    eliminate: false,
                }
            }
            ResearchScopedExpr::Lambda { binder, body } => {
                assert!(!scope.contains(binder));
                let parameter = ResearchScopedValue::Endpoint {
                    fiber,
                    binder: *binder,
                };
                scope.push(*binder);
                let body = research_synthesize_scoped(body, fiber, scope, calls);
                assert_eq!(scope.pop(), Some(*binder));
                ResearchScopedCore {
                    result: ResearchScopedResult {
                        effect: None,
                        value: ResearchScopedValue::Function {
                            parameter: Box::new(parameter.clone()),
                            result: Box::new(body.result.clone()),
                        },
                    },
                    data: ResearchScopedData::Lambda {
                        binder: *binder,
                        parameter,
                        body: Box::new(body),
                    },
                    eliminate: false,
                }
            }
            ResearchScopedExpr::Apply {
                occurrence,
                callee,
                argument,
            } => {
                let callee = research_synthesize_scoped(callee, fiber, scope, calls);
                let argument = research_synthesize_scoped(argument, fiber, scope, calls);
                let result = ResearchScopedResult {
                    effect: Some((fiber, *occurrence)),
                    value: ResearchScopedValue::CallEndpoint {
                        fiber,
                        occurrence: *occurrence,
                    },
                };
                assert!(!calls.iter().any(|call| call.occurrence == *occurrence));
                calls.push(ResearchScopedCallEvidence {
                    occurrence: *occurrence,
                    scope: scope.clone(),
                    argument: argument.result.clone(),
                    result: result.clone(),
                });
                ResearchScopedCore {
                    result,
                    data: ResearchScopedData::ReifiedCall {
                        occurrence: *occurrence,
                        callee: Box::new(callee),
                        argument: Box::new(argument),
                    },
                    eliminate: true,
                }
            }
        }
    }

    // Finite operational characterization only: supplied Int -> Int primitives,
    // one possible request, no inference, typed-flow solving, or handler semantics.
    #[test]
    fn research_parsed_scoped_call_compose_execution_bridge() {
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        enum Value {
            Int(i32),
            Function(bool, bool),
        }
        #[derive(Clone, Debug, Eq, PartialEq)]
        enum Event {
            Construct(u32),
            Receipt(u32),
            Force(u32),
            Rebind(u32, i32),
            Body(u32),
            Result(u32, i32),
            Request(u32, i32),
            Resume(i32, i32),
            Suffix(i32),
        }
        #[derive(Clone, Debug, Eq, PartialEq)]
        struct Run {
            state: i32,
            trace: Vec<Event>,
            // Request snapshots expose the exact pending outer-call suffix.
            pending: Vec<(u32, i32, Vec<u32>)>,
        }
        fn source(
            e: &ResearchScopedExpr,
            env: &[Value],
            run: &mut Run,
            response: (i32, i32),
            outer: &mut Vec<u32>,
        ) -> Value {
            match e {
                ResearchScopedExpr::Variable { binder } => env[*binder as usize],
                ResearchScopedExpr::Lambda { .. } => panic!("entry binders stripped"),
                ResearchScopedExpr::Apply {
                    occurrence,
                    callee,
                    argument,
                } => {
                    let Value::Function(observe, request) =
                        source(callee, env, run, response, outer)
                    else {
                        panic!("bounded callee is Int -> Int")
                    };
                    run.trace.push(Event::Construct(*occurrence));
                    run.trace.push(Event::Receipt(*occurrence));
                    run.trace.push(Event::Force(*occurrence));
                    outer.push(*occurrence);
                    let Value::Int(arg) = source(argument, env, run, response, outer) else {
                        panic!("typed Int rebind")
                    };
                    assert_eq!(outer.pop(), Some(*occurrence));
                    run.trace.push(Event::Rebind(*occurrence, arg));
                    run.trace.push(Event::Body(*occurrence));
                    let value = if request {
                        run.trace.push(Event::Request(*occurrence, run.state));
                        run.pending.push((*occurrence, run.state, outer.clone()));
                        run.state = response.1;
                        run.trace.push(Event::Resume(response.0, run.state));
                        response.0
                    } else if observe {
                        run.state
                    } else {
                        arg ^ run.state
                    };
                    run.trace.push(Event::Result(*occurrence, value));
                    Value::Int(value)
                }
            }
        }
        #[derive(Clone, Copy)]
        enum Instruction<'a> {
            Eval(&'a ResearchScopedCore),
            Enter(u32, &'a ResearchScopedCore),
            Force(u32),
            Receipt(u32),
            Finish(u32, Value),
            Suffix,
        }
        fn machine(
            core: &ResearchScopedCore,
            env: &[Value],
            initial: i32,
            response: (i32, i32),
            mutant: u8,
        ) -> (Value, Run) {
            let mut run = Run {
                state: initial,
                trace: vec![],
                pending: vec![],
            };
            let mut stack = vec![Instruction::Suffix, Instruction::Eval(core)];
            let mut values = Vec::new();
            while let Some(instruction) = stack.pop() {
                match instruction {
                    Instruction::Eval(core) => match &core.data {
                        ResearchScopedData::Name(binder) => {
                            assert!(!core.eliminate);
                            assert_eq!(core.result.effect, None);
                            values.push(env[*binder as usize]);
                        }
                        ResearchScopedData::Lambda { .. } => panic!("entry binders stripped"),
                        ResearchScopedData::ReifiedCall {
                            occurrence,
                            callee,
                            argument,
                        } => {
                            assert!(core.eliminate);
                            assert_eq!(core.result.effect, Some((17, *occurrence)));
                            stack.push(Instruction::Enter(*occurrence, argument));
                            stack.push(Instruction::Eval(callee));
                        }
                    },
                    Instruction::Enter(id, argument) => {
                        let function = values.pop().unwrap();
                        run.trace.push(Event::Construct(id));
                        stack.push(Instruction::Finish(id, function));
                        stack.push(Instruction::Eval(argument));
                        if mutant == 1 {
                            stack.push(Instruction::Receipt(id));
                            stack.push(Instruction::Force(id));
                        } else {
                            stack.push(Instruction::Force(id));
                            stack.push(Instruction::Receipt(id));
                        }
                    }
                    Instruction::Receipt(id) => run.trace.push(Event::Receipt(id)),
                    Instruction::Force(id) => run.trace.push(Event::Force(id)),
                    Instruction::Finish(id, function) => {
                        let Value::Int(arg) = values.pop().unwrap() else {
                            panic!("typed Int rebind")
                        };
                        let Value::Function(observe, request) = function else {
                            panic!("Int -> Int")
                        };
                        run.trace.push(Event::Rebind(id, arg));
                        run.trace.push(Event::Body(id));
                        let result = if request {
                            assert!(run.pending.is_empty(), "at most one request");
                            run.trace.push(Event::Request(id, run.state));
                            let suffix = stack
                                .iter()
                                .filter_map(|instruction| {
                                    if let Instruction::Finish(id, _) = instruction {
                                        Some(*id)
                                    } else {
                                        None
                                    }
                                })
                                .collect();
                            run.pending.push((id, run.state, suffix));
                            if mutant != 2 {
                                run.state = response.1;
                            }
                            run.trace.push(Event::Resume(response.0, run.state));
                            response.0
                        } else if observe {
                            run.state
                        } else {
                            arg ^ run.state
                        };
                        run.trace.push(Event::Result(id, result));
                        values.push(Value::Int(result));
                    }
                    Instruction::Suffix => run.trace.push(Event::Suffix(run.state)),
                }
            }
            assert_eq!(values.len(), 1);
            (values[0], run)
        }
        let mut comparisons = 0;
        let mut pending = 0;
        let mut witnesses = [None, None];
        for (source_text, arity) in [("my call f x = f x", 2), ("my compose f g x = f (g x)", 3)] {
            let parsed = parsed(source_text);
            let root = SyntaxNode::new_root(parsed.green().clone());
            let statement = root
                .descendants()
                .find(|n| n.kind() == SyntaxKind::BindingStatement)
                .unwrap();
            let (_, expression) =
                research_lower_binding_candidate(&statement, &parsed, source_text);
            let mut scope = vec![];
            let mut calls = vec![];
            let core = research_synthesize_scoped(&expression, 17, &mut scope, &mut calls);
            assert!(scope.is_empty());
            assert_eq!(calls.len(), arity - 1);
            assert_eq!(
                calls
                    .iter()
                    .map(|c| c.occurrence)
                    .collect::<std::collections::HashSet<_>>()
                    .len(),
                calls.len()
            );
            for call in &calls {
                assert_eq!(call.scope, (0..arity as u32).collect::<Vec<_>>());
            }
            let mut expression_body = &expression;
            let mut core_body = &core;
            for binder in 0..arity as u32 {
                let ResearchScopedExpr::Lambda {
                    binder: actual,
                    body,
                } = expression_body
                else {
                    panic!("lambda")
                };
                assert_eq!(*actual, binder);
                expression_body = body;
                let ResearchScopedData::Lambda {
                    binder: actual,
                    parameter,
                    body,
                } = &core_body.data
                else {
                    panic!("lambda")
                };
                assert_eq!(*actual, binder);
                assert_eq!(
                    *parameter,
                    ResearchScopedValue::Endpoint { fiber: 17, binder }
                );
                core_body = body;
            }
            // Lexicographic exhaustive shrinking inside this declared six-bit domain.
            for input in 0..=1 {
                for initial in 0..=1 {
                    for observe in [false, true] {
                        for request in [false, true] {
                            for returned in 0..=1 {
                                for resumed in 0..=1 {
                                    let env = if arity == 2 {
                                        vec![Value::Function(observe, false), Value::Int(input)]
                                    } else {
                                        vec![
                                            Value::Function(observe, false),
                                            Value::Function(false, request),
                                            Value::Int(input),
                                        ]
                                    };
                                    let mut expected = Run {
                                        state: initial,
                                        trace: vec![],
                                        pending: vec![],
                                    };
                                    let value = source(
                                        expression_body,
                                        &env,
                                        &mut expected,
                                        (returned, resumed),
                                        &mut vec![],
                                    );
                                    expected.trace.push(Event::Suffix(expected.state));
                                    let actual =
                                        machine(core_body, &env, initial, (returned, resumed), 0);
                                    assert_eq!(
                                        actual,
                                        (value, expected.clone()),
                                        "{source_text} {env:?}"
                                    );
                                    comparisons += 1;
                                    pending += expected.pending.len();
                                    if !expected.pending.is_empty() {
                                        assert_eq!(
                                            expected.pending[0].2,
                                            vec![calls[1].occurrence]
                                        );
                                    }
                                    for mutant in 1..=2 {
                                        if witnesses[mutant - 1].is_none()
                                            && machine(
                                                core_body,
                                                &env,
                                                initial,
                                                (returned, resumed),
                                                mutant as u8,
                                            ) != actual
                                        {
                                            witnesses[mutant - 1] = Some((
                                                arity, input, initial, observe, request, returned,
                                                resumed,
                                            ));
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        assert_eq!(comparisons, 128);
        assert_eq!(pending, 32);
        assert_eq!(witnesses[0], Some((2, 0, 0, false, false, 0, 0)));
        assert_eq!(witnesses[1], Some((3, 0, 0, false, true, 0, 1)));
    }

    #[test]
    fn research_scoped_source_synthesizes_lambda_result_skeletons() {
        let mut compose = None;
        for (source, binders, call_count) in [
            ("my call f x = f x", 2, 1),
            ("my compose f g x = f (g x)", 3, 2),
            ("my compose f g x = f(g(x))", 3, 2),
        ] {
            let parsed = parsed(source);
            let root = SyntaxNode::new_root(parsed.green().clone());
            let statement = root
                .descendants()
                .find(|node| node.kind() == SyntaxKind::BindingStatement)
                .unwrap();
            let (_, candidate) = research_lower_binding_candidate(&statement, &parsed, source);
            let mut scope = Vec::new();
            let mut calls = Vec::new();
            let core = research_synthesize_scoped(&candidate, 17, &mut scope, &mut calls);
            assert!(scope.is_empty());
            assert_eq!(calls.len(), call_count);
            let mut body = &core;
            for binder in 0..binders {
                assert!(!body.eliminate);
                assert_eq!(body.result.effect, None);
                let ResearchScopedData::Lambda {
                    binder: actual,
                    parameter,
                    body: inner,
                } = &body.data
                else {
                    panic!("source parameter must generate a lambda")
                };
                assert_eq!(*actual, binder);
                assert_eq!(
                    *parameter,
                    ResearchScopedValue::Endpoint { fiber: 17, binder }
                );
                assert_eq!(
                    body.result.value,
                    ResearchScopedValue::Function {
                        parameter: Box::new(parameter.clone()),
                        result: Box::new(inner.result.clone()),
                    }
                );
                body = inner;
            }
            assert!(body.eliminate);
            for call in &calls {
                assert_eq!(call.scope, (0..binders).collect::<Vec<_>>());
                assert_eq!(call.result.effect, Some((17, call.occurrence)));
                assert_eq!(
                    call.result.value,
                    ResearchScopedValue::CallEndpoint {
                        fiber: 17,
                        occurrence: call.occurrence,
                    }
                );
            }
            assert_eq!(calls[0].argument.effect, None);
            assert_eq!(
                calls[0].argument.value,
                ResearchScopedValue::Endpoint {
                    fiber: 17,
                    binder: binders - 1,
                }
            );
            if call_count == 2 {
                let ResearchScopedData::ReifiedCall { argument, .. } = &body.data else {
                    panic!("compose body must reify its outer call")
                };
                assert!(argument.eliminate);
                assert_eq!(calls[1].argument, calls[0].result);
                assert_eq!(calls[1].argument, argument.result);
                assert_ne!(calls[0].result, calls[1].result);
                // Destructively projecting Result(I_arg) to A erases the inner
                // call's symbolic E. Generated outer-call evidence rejects it.
                let mut mutant = argument.result.clone();
                mutant.effect = None;
                assert_ne!(calls[1].argument, mutant);
                if let Some(expected) = &compose {
                    assert_eq!(expected, &(core.clone(), calls.clone()));
                } else {
                    compose = Some((core.clone(), calls.clone()));
                }
            }
        }
    }

    #[test]
    fn research_multi_parameter_declarations_form_nested_scoped_candidates() {
        for (source, expected_parameters, expected_shape, expected_calls) in [
            ("my call f x = f x", vec!["f", "x"], "λ0.λ1.(v0 v1)", 1),
            (
                "my higher f g x = f g x",
                vec!["f", "g", "x"],
                "λ0.λ1.λ2.((v0 v1) v2)",
                2,
            ),
            (
                "my compose f g x = f(g(x))",
                vec!["f", "g", "x"],
                "λ0.λ1.λ2.(v0 (v1 v2))",
                2,
            ),
            (
                "my compose f g x = f (g x)",
                vec!["f", "g", "x"],
                "λ0.λ1.λ2.(v0 (v1 v2))",
                2,
            ),
        ] {
            let parsed = parsed(source);
            let root = SyntaxNode::new_root(parsed.green().clone());
            let statements = root
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::BindingStatement)
                .collect::<Vec<_>>();
            assert_eq!(statements.len(), 1, "{source}");
            let (parameters, expression) =
                research_lower_binding_candidate(&statements[0], &parsed, source);
            assert_eq!(
                parameters
                    .iter()
                    .map(|(name, _)| name.as_str())
                    .collect::<Vec<_>>(),
                expected_parameters,
                "{source}"
            );
            assert_eq!(
                research_scoped_shape(&expression),
                expected_shape,
                "{source}"
            );
            assert_eq!(
                research_scoped_call_count(&expression),
                expected_calls,
                "{source}"
            );
        }
    }

    #[test]
    fn research_apply_lowering_keeps_parenthesized_call_argument_nested() {
        let associated = parse("f(g(a))");
        assert_eq!(associated.chains().len(), 1);
        let mut next = 0;
        let candidate =
            research_lower_apply(associated.chains()[0].expression(), "f(g(a))", &mut next);
        let ResearchApply::Apply {
            form: SyntaxKind::CallTail,
            argument,
            ..
        } = candidate
        else {
            panic!("outer source step is CallTail");
        };
        assert!(matches!(
            argument.as_ref(),
            ResearchApply::Apply {
                form: SyntaxKind::CallTail,
                ..
            }
        ));
        assert_eq!(next, 2);
    }

    #[test]
    fn research_apply_synthesis_preserves_whole_nested_computations() {
        let gamma = HashMap::from([
            (
                "f".to_owned(),
                ResearchInterface::Value {
                    value: "Tf".to_owned(),
                },
            ),
            (
                "g".to_owned(),
                ResearchInterface::Value {
                    value: "Tg".to_owned(),
                },
            ),
            (
                "a".to_owned(),
                ResearchInterface::Value {
                    value: "Ta".to_owned(),
                },
            ),
            (
                "b".to_owned(),
                ResearchInterface::Value {
                    value: "Tb".to_owned(),
                },
            ),
        ]);

        for (source, application_count, forms, expected_projections) in [
            (
                "f a",
                1,
                vec![SyntaxKind::MlArgument],
                vec![ResearchApplicationProjection {
                    occurrence: 0,
                    callee_value: "Tf".to_owned(),
                    argument_value: "Ta".to_owned(),
                    result_value: "call0.value".to_owned(),
                }],
            ),
            (
                "f(a)",
                1,
                vec![SyntaxKind::CallTail],
                vec![ResearchApplicationProjection {
                    occurrence: 0,
                    callee_value: "Tf".to_owned(),
                    argument_value: "Ta".to_owned(),
                    result_value: "call0.value".to_owned(),
                }],
            ),
            (
                "f a b",
                2,
                vec![SyntaxKind::MlArgument; 2],
                vec![
                    ResearchApplicationProjection {
                        occurrence: 1,
                        callee_value: "Tf".to_owned(),
                        argument_value: "Ta".to_owned(),
                        result_value: "call1.value".to_owned(),
                    },
                    ResearchApplicationProjection {
                        occurrence: 0,
                        callee_value: "call1.value".to_owned(),
                        argument_value: "Tb".to_owned(),
                        result_value: "call0.value".to_owned(),
                    },
                ],
            ),
            (
                "f(a)(b)",
                2,
                vec![SyntaxKind::CallTail; 2],
                vec![
                    ResearchApplicationProjection {
                        occurrence: 1,
                        callee_value: "Tf".to_owned(),
                        argument_value: "Ta".to_owned(),
                        result_value: "call1.value".to_owned(),
                    },
                    ResearchApplicationProjection {
                        occurrence: 0,
                        callee_value: "call1.value".to_owned(),
                        argument_value: "Tb".to_owned(),
                        result_value: "call0.value".to_owned(),
                    },
                ],
            ),
            (
                "f(g(a))",
                2,
                vec![SyntaxKind::CallTail; 2],
                vec![
                    ResearchApplicationProjection {
                        occurrence: 1,
                        callee_value: "Tg".to_owned(),
                        argument_value: "Ta".to_owned(),
                        result_value: "call1.value".to_owned(),
                    },
                    ResearchApplicationProjection {
                        occurrence: 0,
                        callee_value: "Tf".to_owned(),
                        argument_value: "call1.value".to_owned(),
                        result_value: "call0.value".to_owned(),
                    },
                ],
            ),
        ] {
            let associated = parse(source);
            assert_eq!(associated.chains().len(), 1, "{source}");
            assert!(research_expression_is_valid(
                associated.chains()[0].expression()
            ));
            let mut next = 0;
            let candidate =
                research_lower_apply(associated.chains()[0].expression(), source, &mut next);
            let mut actual_atoms = Vec::new();
            research_apply_atoms(&candidate, &mut actual_atoms);
            actual_atoms.sort_by_key(|(_, range)| range.start);
            assert_eq!(actual_atoms, expected_research_atoms(source), "{source}");
            assert!(research_apply_arguments_are_atoms(&candidate) || source == "f(g(a))");
            assert_eq!(
                research_apply_spine(&candidate).len(),
                application_count,
                "{source}"
            );
            assert_eq!(next as usize, application_count, "{source}");

            let mut projections = Vec::new();
            let synthesis = research_synthesize(&candidate, &gamma, &mut projections);
            assert_eq!(projections.len(), application_count, "{source}");
            assert_eq!(projections, expected_projections, "{source}");
            assert_eq!(synthesis.interface.value_endpoint(), "call0.value");
            assert!(matches!(
                synthesis.normalized,
                ResearchComputation::Eliminate { ref effect, .. } if effect == "call0.effect"
            ));
            if matches!(source, "f a b" | "f(a)(b)") {
                assert_eq!(
                    synthesis.data,
                    ResearchData::ReifiedCall {
                        callee: Box::new(ResearchComputation::Eliminate {
                            effect: "call1.effect".to_owned(),
                            data: Box::new(ResearchData::ReifiedCall {
                                callee: Box::new(ResearchComputation::Result(Box::new(
                                    ResearchData::Name("f".to_owned()),
                                ))),
                                argument: Box::new(ResearchComputation::Result(Box::new(
                                    ResearchData::Name("a".to_owned()),
                                ))),
                            }),
                        }),
                        argument: Box::new(ResearchComputation::Result(Box::new(
                            ResearchData::Name("b".to_owned()),
                        ))),
                    },
                    "the prior computation is normalized as the staged callee: {source}"
                );
            }
            let mut projected_forms = Vec::new();
            fn gather_forms(expression: &ResearchApply, into: &mut Vec<SyntaxKind>) {
                match expression {
                    ResearchApply::Atom { .. } => {}
                    ResearchApply::Group { children, .. } => {
                        for child in children {
                            gather_forms(child, into);
                        }
                    }
                    ResearchApply::Apply {
                        form,
                        callee,
                        argument,
                        ..
                    } => {
                        gather_forms(callee, into);
                        into.push(*form);
                        gather_forms(argument, into);
                    }
                }
            }
            gather_forms(&candidate, &mut projected_forms);
            assert_eq!(projected_forms, forms, "{source}");
        }

        let associated = parse("f(g(a))");
        let mut next = 0;
        let candidate =
            research_lower_apply(associated.chains()[0].expression(), "f(g(a))", &mut next);
        let mut projections = Vec::new();
        let synthesis = research_synthesize(&candidate, &gamma, &mut projections);
        assert_eq!(
            projections,
            [
                ResearchApplicationProjection {
                    occurrence: 1,
                    callee_value: "Tg".to_owned(),
                    argument_value: "Ta".to_owned(),
                    result_value: "call1.value".to_owned(),
                },
                ResearchApplicationProjection {
                    occurrence: 0,
                    callee_value: "Tf".to_owned(),
                    argument_value: "call1.value".to_owned(),
                    result_value: "call0.value".to_owned(),
                },
            ]
        );
        assert_eq!(
            synthesis.normalized,
            ResearchComputation::Eliminate {
                effect: "call0.effect".to_owned(),
                data: Box::new(ResearchData::ReifiedCall {
                    callee: Box::new(ResearchComputation::Result(Box::new(ResearchData::Name(
                        "f".to_owned()
                    ),))),
                    argument: Box::new(ResearchComputation::Eliminate {
                        effect: "call1.effect".to_owned(),
                        data: Box::new(ResearchData::ReifiedCall {
                            callee: Box::new(ResearchComputation::Result(Box::new(
                                ResearchData::Name("g".to_owned()),
                            ))),
                            argument: Box::new(ResearchComputation::Result(Box::new(
                                ResearchData::Name("a".to_owned()),
                            ))),
                        }),
                    }),
                }),
            }
        );

        let mut retained_gamma = gamma.clone();
        retained_gamma.insert(
            "pending".to_owned(),
            ResearchInterface::Computation {
                effect: "empty-row".to_owned(),
                value: "A_pending".to_owned(),
            },
        );
        let associated = parse("f pending");
        let mut next = 0;
        let candidate =
            research_lower_apply(associated.chains()[0].expression(), "f pending", &mut next);
        let mut projections = Vec::new();
        let synthesis = research_synthesize(&candidate, &retained_gamma, &mut projections);
        assert_eq!(
            projections[0].argument_value, "A_pending",
            "the whole argument's interface result is projected"
        );
        assert!(matches!(
            synthesis.data,
                ResearchData::ReifiedCall { ref argument, .. }
                if matches!(argument.as_ref(), ResearchComputation::Eliminate { effect, data }
                    if effect == "empty-row"
                        && matches!(data.as_ref(), ResearchData::Name(name) if name == "pending"))
        ));

        let associated = parse("pending");
        let mut next = 0;
        let candidate =
            research_lower_apply(associated.chains()[0].expression(), "pending", &mut next);
        let mut projections = Vec::new();
        let synthesis = research_synthesize(&candidate, &retained_gamma, &mut projections);
        assert_eq!(
            synthesis.interface,
            ResearchInterface::Computation {
                effect: "empty-row".to_owned(),
                value: "A_pending".to_owned(),
            }
        );
        assert_eq!(
            synthesis.normalized,
            ResearchComputation::Eliminate {
                effect: "empty-row".to_owned(),
                data: Box::new(ResearchData::Name("pending".to_owned())),
            }
        );
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
