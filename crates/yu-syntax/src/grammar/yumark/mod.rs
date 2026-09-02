//! Inert AST vocabulary for standalone doc comments and structured Yumark.
//!
//! Gate 1 defines source-preserving carriers only. Recognition, parsing,
//! output adapters, and public dispatch belong to later gates.

use std::ops::Range;

use super::declaration::{Recovered, UseTree};

mod driver;
mod judge;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct DocCommentDeclaration<'source> {
    pub(crate) form: DocCommentForm,
    pub(crate) document: YumarkDocument<'source>,
    pub(crate) range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum DocCommentForm {
    Line {
        prefix: Range<usize>,
    },
    Block {
        open: Range<usize>,
        close: Recovered<Range<usize>>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct YumarkDocument<'source> {
    pub(crate) blocks: Vec<Recovered<YumarkBlock<'source>>>,
    pub(crate) range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum YumarkBlock<'source> {
    BlankLine(YumarkBlankLine),
    Section(YumarkSection<'source>),
    List(YumarkList<'source>),
    Quote(YumarkQuote<'source>),
    CodeFence(YumarkCodeFence),
    Paragraph(YumarkParagraph),
    Command(YumarkCommandBlock<'source>),
    IfChain(YumarkIfChain<'source>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum YumarkCommandBlock<'source> {
    General(YumarkCommand<'source>),
    My(YumarkMy<'source>),
    Use(YumarkUse<'source>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct YumarkBlankLine {
    pub(crate) range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct YumarkSection<'source> {
    pub(crate) heading: YumarkHeading,
    pub(crate) form: YumarkSectionForm<'source>,
    pub(crate) close: Option<Range<usize>>,
    pub(crate) range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum YumarkSectionForm<'source> {
    Implicit {
        document: YumarkDocument<'source>,
    },
    Explicit {
        body_introducer: Range<usize>,
        document: Recovered<YumarkDocument<'source>>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct YumarkHeading {
    pub(crate) marker: Range<usize>,
    pub(crate) level: usize,
    pub(crate) title: YumarkInlineDocument,
    pub(crate) range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct YumarkList<'source> {
    pub(crate) items: Vec<Recovered<YumarkListItem<'source>>>,
    pub(crate) indent: usize,
    pub(crate) range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct YumarkListItem<'source> {
    pub(crate) marker: Range<usize>,
    pub(crate) indent: usize,
    pub(crate) content_column: usize,
    pub(crate) body: YumarkDocument<'source>,
    pub(crate) range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct YumarkQuote<'source> {
    pub(crate) form: YumarkQuoteForm,
    pub(crate) document: YumarkDocument<'source>,
    pub(crate) range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum YumarkQuoteForm {
    Explicit {
        open: Range<usize>,
        close: Recovered<Range<usize>>,
    },
    Prefix {
        markers: Vec<Range<usize>>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct YumarkCodeFence {
    pub(crate) open: Range<usize>,
    pub(crate) info: Range<usize>,
    pub(crate) opening_newline: Range<usize>,
    pub(crate) text: Range<usize>,
    pub(crate) close: Recovered<Range<usize>>,
    pub(crate) range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct YumarkParagraph {
    pub(crate) document: YumarkInlineDocument,
    pub(crate) range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct YumarkInlineDocument {
    pub(crate) items: Vec<Recovered<YumarkInline>>,
    pub(crate) range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum YumarkInline {
    Text(YumarkText),
    Group(YumarkInlineGroup),
    Link(YumarkInlineLink),
    Image(YumarkInlineImage),
    Apply(YumarkInlineApply),
    Reference(YumarkInlineReference),
    Emphasis(YumarkEmphasis),
    Strong(YumarkStrong),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct YumarkText {
    pub(crate) range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct YumarkInlineGroup {
    pub(crate) open: Range<usize>,
    pub(crate) document: YumarkInlineDocument,
    pub(crate) close: Recovered<Range<usize>>,
    pub(crate) range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct YumarkInlineLink {
    pub(crate) group: YumarkInlineGroup,
    pub(crate) destination: Range<usize>,
    pub(crate) close: Recovered<Range<usize>>,
    pub(crate) range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct YumarkInlineImage {
    pub(crate) marker: Range<usize>,
    pub(crate) document: YumarkInlineDocument,
    pub(crate) group_close: Recovered<Range<usize>>,
    pub(crate) destination: Recovered<Range<usize>>,
    pub(crate) destination_close: Option<Recovered<Range<usize>>>,
    pub(crate) range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct YumarkInlineApply {
    pub(crate) group: YumarkInlineGroup,
    pub(crate) head: Range<usize>,
    pub(crate) arguments: Option<YumarkYulangArguments>,
    pub(crate) range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct YumarkInlineReference {
    pub(crate) backslash: Range<usize>,
    pub(crate) name: Recovered<Range<usize>>,
    pub(crate) arguments: Option<YumarkYulangArguments>,
    pub(crate) terminator: Option<Range<usize>>,
    pub(crate) range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct YumarkEmphasis {
    pub(crate) open: Range<usize>,
    pub(crate) document: YumarkInlineDocument,
    pub(crate) close: Recovered<Range<usize>>,
    pub(crate) range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct YumarkStrong {
    pub(crate) open: Range<usize>,
    pub(crate) document: YumarkInlineDocument,
    pub(crate) close: Recovered<Range<usize>>,
    pub(crate) range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct YumarkYulangArguments {
    pub(crate) range: Range<usize>,
    pub(crate) close: Recovered<Range<usize>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct YumarkCommand<'source> {
    pub(crate) range: Range<usize>,
    pub(crate) promotion: GeneralCommandPromotion,
    pub(crate) arguments: Vec<CommandArgument>,
    pub(crate) local_body: Option<YumarkCommandBody<'source>>,
    pub(crate) do_capture: Option<Recovered<YumarkDoCapture<'source>>>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum GeneralCommandPromotion {
    ImmediateDocArgument,
    ImmediateDo,
    ImmediateBody,
    YulangThenDocArgument,
    YulangThenBody,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum CommandArgument {
    Yulang {
        range: Range<usize>,
    },
    Document {
        document: YumarkInlineDocument,
        close: Recovered<Range<usize>>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum YumarkCommandBody<'source> {
    BracedDoc {
        open: Range<usize>,
        document: YumarkDocument<'source>,
        close: Recovered<Range<usize>>,
    },
    IndentedDoc {
        introducer: Range<usize>,
        document: Recovered<YumarkDocument<'source>>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct YumarkDoCapture<'source> {
    pub(crate) range: Range<usize>,
    pub(crate) blocks: Vec<Recovered<YumarkBlock<'source>>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct YumarkMy<'source> {
    pub(crate) head_form: YumarkMyHeadForm,
    pub(crate) head: Recovered<YumarkBindingHead>,
    pub(crate) body: Recovered<YumarkMyBody<'source>>,
    pub(crate) range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum YumarkMyHeadForm {
    Bare,
    Parenthesized { close: Recovered<Range<usize>> },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct YumarkBindingHead {
    pub(crate) patterns: Vec<Recovered<Range<usize>>>,
    pub(crate) range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum YumarkMyBody<'source> {
    InlineExpression {
        expression: Recovered<Range<usize>>,
        terminator: Recovered<Range<usize>>,
    },
    IndentedExpression {
        expression: Recovered<Range<usize>>,
    },
    BracedDoc {
        open: Range<usize>,
        document: YumarkDocument<'source>,
        close: Recovered<Range<usize>>,
    },
    IndentedDoc {
        introducer: Range<usize>,
        document: Recovered<YumarkDocument<'source>>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct YumarkUse<'source> {
    pub(crate) form: YumarkUseForm,
    pub(crate) route: Recovered<UseTree<'source>>,
    pub(crate) range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum YumarkUseForm {
    Parenthesized { close: Recovered<Range<usize>> },
    Bare { terminator: Recovered<Range<usize>> },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct YumarkIfChain<'source> {
    pub(crate) branches: Vec<YumarkIfBranch<'source>>,
    pub(crate) else_branch: Option<YumarkElseBranch<'source>>,
    pub(crate) range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct YumarkIfBranch<'source> {
    pub(crate) kind: YumarkConditionalBranchKind,
    pub(crate) condition: Recovered<Range<usize>>,
    pub(crate) condition_close: Recovered<Range<usize>>,
    pub(crate) body: Recovered<YumarkCommandBody<'source>>,
    pub(crate) range: Range<usize>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum YumarkConditionalBranchKind {
    If,
    Elsif,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct YumarkElseBranch<'source> {
    pub(crate) body: Recovered<YumarkCommandBody<'source>>,
    pub(crate) range: Range<usize>,
}

#[cfg(test)]
mod ast_tests {
    use super::*;

    #[test]
    fn ast_vocabulary_preserves_document_and_command_surface_forms() {
        let document = YumarkDocument {
            blocks: Vec::new(),
            range: 2..2,
        };
        let declaration = DocCommentDeclaration {
            form: DocCommentForm::Line { prefix: 0..2 },
            document,
            range: 0..2,
        };
        assert!(matches!(declaration.form, DocCommentForm::Line { .. }));
        assert_eq!(declaration.document.blocks, Vec::new());

        let use_command: YumarkUse<'static> = YumarkUse {
            form: YumarkUseForm::Bare {
                terminator: Recovered::Complete(8..9),
            },
            route: Recovered::Incomplete,
            range: 0..9,
        };
        let route: &Recovered<UseTree<'static>> = &use_command.route;
        assert_eq!(route, &Recovered::Incomplete);

        assert_eq!(
            [
                GeneralCommandPromotion::ImmediateDocArgument,
                GeneralCommandPromotion::ImmediateDo,
                GeneralCommandPromotion::ImmediateBody,
                GeneralCommandPromotion::YulangThenDocArgument,
                GeneralCommandPromotion::YulangThenBody,
            ]
            .len(),
            5
        );
    }
}

#[cfg(test)]
mod tests;
