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
    fn trivia(&mut self, _trivia: &Trivia) {}
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

    fn trivia(&mut self, _trivia: &Trivia) {}

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
    stats: GreenSinkStats,
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct GreenSinkStats {
    pub nodes_started: usize,
    pub nodes_finished: usize,
    pub tokens: usize,
    pub token_bytes: usize,
}

impl GreenSink {
    pub fn new() -> Self {
        Self {
            builder: GreenNodeBuilder::new(),
            stats: GreenSinkStats::default(),
        }
    }

    pub fn finish_green(self) -> GreenNode {
        self.finish_green_with_stats().0
    }

    pub fn finish_green_with_stats(self) -> (GreenNode, GreenSinkStats) {
        (self.builder.finish(), self.stats)
    }

    fn start_node(&mut self, kind: SyntaxKind) {
        self.builder.start_node(YulangLanguage::kind_to_raw(kind));
        self.stats.nodes_started += 1;
    }

    fn token(&mut self, kind: SyntaxKind, text: &str) {
        self.builder
            .token(YulangLanguage::kind_to_raw(kind), text.as_ref());
        self.stats.tokens += 1;
        self.stats.token_bytes += text.len();
    }

    fn finish_node(&mut self) {
        self.builder.finish_node();
        self.stats.nodes_finished += 1;
    }
}

impl Default for GreenSink {
    fn default() -> Self {
        Self::new()
    }
}

impl EventSink for GreenSink {
    fn start(&mut self, kind: SyntaxKind) {
        self.start_node(kind);
    }

    fn lex(&mut self, lex: &Lex) {
        self.token(lex.kind, lex.text.as_ref());
        self.trivia(&lex.trailing_trivia);
    }

    fn trivia(&mut self, trivia: &Trivia) {
        for part in trivia.parts() {
            match part.kind {
                TriviaKind::BlockCommentStart => {
                    self.start_node(SyntaxKind::BlockComment);
                    self.token(SyntaxKind::BlockCommentStart, part.text.as_ref());
                }
                TriviaKind::BlockCommentEnd => {
                    self.token(SyntaxKind::BlockCommentEnd, part.text.as_ref());
                    self.finish_node();
                }
                _ => {
                    self.token(part.kind.into(), part.text.as_ref());
                }
            }
        }
    }

    fn finish(&mut self) {
        self.finish_node();
    }
}
