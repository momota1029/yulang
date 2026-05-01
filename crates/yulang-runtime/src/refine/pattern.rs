use super::*;

impl RefineRewriter {
    pub(super) fn pattern(&mut self, pattern: Pattern) -> Pattern {
        match pattern {
            Pattern::Wildcard { ty } => Pattern::Wildcard {
                ty: substitute_hir_type(&ty, &self.substitutions),
            },
            Pattern::Bind { name, ty } => Pattern::Bind {
                name,
                ty: substitute_hir_type(&ty, &self.substitutions),
            },
            Pattern::Lit { lit, ty } => Pattern::Lit {
                lit,
                ty: substitute_hir_type(&ty, &self.substitutions),
            },
            Pattern::Tuple { items, ty } => Pattern::Tuple {
                items: items.into_iter().map(|item| self.pattern(item)).collect(),
                ty: substitute_hir_type(&ty, &self.substitutions),
            },
            Pattern::List {
                prefix,
                spread,
                suffix,
                ty,
            } => Pattern::List {
                prefix: prefix.into_iter().map(|item| self.pattern(item)).collect(),
                spread: spread.map(|spread| Box::new(self.pattern(*spread))),
                suffix: suffix.into_iter().map(|item| self.pattern(item)).collect(),
                ty: substitute_hir_type(&ty, &self.substitutions),
            },
            Pattern::Record { fields, spread, ty } => Pattern::Record {
                fields: fields
                    .into_iter()
                    .map(|field| RecordPatternField {
                        name: field.name,
                        pattern: self.pattern(field.pattern),
                        default: field.default.map(|default| self.expr(default, None)),
                    })
                    .collect(),
                spread: spread.map(|spread| match spread {
                    RecordSpreadPattern::Head(pattern) => {
                        RecordSpreadPattern::Head(Box::new(self.pattern(*pattern)))
                    }
                    RecordSpreadPattern::Tail(pattern) => {
                        RecordSpreadPattern::Tail(Box::new(self.pattern(*pattern)))
                    }
                }),
                ty: substitute_hir_type(&ty, &self.substitutions),
            },
            Pattern::Variant { tag, value, ty } => Pattern::Variant {
                tag,
                value: value.map(|value| Box::new(self.pattern(*value))),
                ty: substitute_hir_type(&ty, &self.substitutions),
            },
            Pattern::Or { left, right, ty } => Pattern::Or {
                left: Box::new(self.pattern(*left)),
                right: Box::new(self.pattern(*right)),
                ty: substitute_hir_type(&ty, &self.substitutions),
            },
            Pattern::As { pattern, name, ty } => Pattern::As {
                pattern: Box::new(self.pattern(*pattern)),
                name,
                ty: substitute_hir_type(&ty, &self.substitutions),
            },
        }
    }
}
