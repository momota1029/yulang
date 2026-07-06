use crate::text::ByteRange;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Diagnostic {
    pub severity: DiagnosticSeverity,
    pub code: Option<String>,
    pub label: Option<String>,
    pub range: Option<ByteRange>,
    pub message: String,
    pub hint: Option<String>,
    pub related: Vec<RelatedDiagnostic>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RelatedDiagnostic {
    pub message: String,
    pub range: ByteRange,
    pub origin: Option<RelatedOrigin>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RelatedOrigin {
    TypeAnnotation,
    Expression,
    ImplCandidate,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiagnosticSeverity {
    Error,
}

impl Diagnostic {
    pub fn message_with_label_and_hint(&self) -> String {
        let mut message = match self.label.as_ref() {
            Some(label) => format!("{label}: {}", self.message),
            None => self.message.clone(),
        };
        if let Some(hint) = self.hint.as_ref() {
            message.push_str("\nhint: ");
            message.push_str(hint);
        }
        message
    }
}

impl RelatedOrigin {
    pub fn playground_code(self) -> &'static str {
        match self {
            RelatedOrigin::TypeAnnotation => "type_annotation",
            RelatedOrigin::Expression => "expression",
            RelatedOrigin::ImplCandidate => "impl_candidate",
        }
    }
}
