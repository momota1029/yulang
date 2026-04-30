use rowan::{GreenNode, GreenNodeBuilder, Language as RowanLanguage};

use crate::lex::{Lex, SyntaxKind, Trivia, TriviaInfo, TriviaKind};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Event {
    Start(SyntaxKind),
    Lex(SyntaxKind),
    Finish,
}

pub trait EventSink {
    fn start(&mut self, kind: SyntaxKind);
    fn lex(&mut self, lex: &Lex);
    fn push(&mut self, kind: SyntaxKind, text: &str) {
        self.lex(&Lex::new(TriviaInfo::None, kind, text, Trivia::empty()))
    }
    fn finish(&mut self);
}

#[derive(Debug, Default)]
pub struct VecSink {
    pub events: Vec<Event>,
    pub lexs: Vec<Lex>,
}

impl VecSink {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn into_parts(self) -> (Vec<Event>, Vec<Lex>) {
        (self.events, self.lexs)
    }
}

impl EventSink for VecSink {
    fn start(&mut self, kind: SyntaxKind) {
        self.events.push(Event::Start(kind));
    }

    fn lex(&mut self, lex: &Lex) {
        self.events.push(Event::Lex(lex.kind));
        self.lexs.push(lex.clone());
    }

    fn finish(&mut self) {
        self.events.push(Event::Finish);
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum YulangLanguage {}

impl RowanLanguage for YulangLanguage {
    type Kind = SyntaxKind;

    fn kind_from_raw(raw: rowan::SyntaxKind) -> Self::Kind {
        unsafe { std::mem::transmute::<u16, SyntaxKind>(raw.0) }
    }

    fn kind_to_raw(kind: Self::Kind) -> rowan::SyntaxKind {
        rowan::SyntaxKind(kind as u16)
    }
}

pub struct GreenSink {
    builder: GreenNodeBuilder<'static>,
}

impl GreenSink {
    pub fn new() -> Self {
        Self {
            builder: GreenNodeBuilder::new(),
        }
    }

    pub fn finish_green(self) -> GreenNode {
        self.builder.finish()
    }
}

impl Default for GreenSink {
    fn default() -> Self {
        Self::new()
    }
}

impl EventSink for GreenSink {
    fn start(&mut self, kind: SyntaxKind) {
        self.builder.start_node(YulangLanguage::kind_to_raw(kind));
    }

    fn lex(&mut self, lex: &Lex) {
        self.builder
            .token(YulangLanguage::kind_to_raw(lex.kind), lex.text.as_ref());
        for trivia in lex.trailing_trivia.parts() {
            match trivia.kind {
                TriviaKind::BlockCommentStart => {
                    self.builder
                        .start_node(YulangLanguage::kind_to_raw(SyntaxKind::BlockComment));
                    self.builder.token(
                        YulangLanguage::kind_to_raw(SyntaxKind::BlockCommentStart),
                        trivia.text.as_ref(),
                    );
                }
                TriviaKind::BlockCommentEnd => {
                    self.builder.token(
                        YulangLanguage::kind_to_raw(SyntaxKind::BlockCommentEnd),
                        trivia.text.as_ref(),
                    );
                    self.builder.finish_node();
                }
                _ => {
                    self.builder.token(
                        YulangLanguage::kind_to_raw(trivia.kind.into()),
                        trivia.text.as_ref(),
                    );
                }
            }
        }
    }

    fn finish(&mut self) {
        self.builder.finish_node();
    }
}
