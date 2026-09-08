//! Immutable ordinary-owner visibility, separate from source observation.

/// The logical optional view, with an immutable source-free proof hook in tests.
#[derive(Clone, Copy)]
#[cfg_attr(not(test), repr(transparent))]
pub(in crate::parser) struct AmbientClaimContext<'frame> {
    pub(in crate::parser) view: Option<AmbientClaimView<'frame>>,
    #[cfg(test)]
    proof: Option<fn(ProofSite, Option<AmbientClaimView<'_>>)>,
}

impl<'frame> From<Option<AmbientClaimView<'frame>>> for AmbientClaimContext<'frame> {
    fn from(view: Option<AmbientClaimView<'frame>>) -> Self {
        Self {
            view,
            #[cfg(test)]
            proof: None,
        }
    }
}

impl<'frame> AmbientClaimContext<'frame> {
    pub(in crate::parser) fn map<'inner>(
        self,
        transform: impl FnOnce(AmbientClaimView<'frame>) -> AmbientClaimView<'inner>,
    ) -> AmbientClaimContext<'inner> {
        AmbientClaimContext {
            view: self.view.map(transform),
            #[cfg(test)]
            proof: self.proof,
        }
    }

    pub(in crate::parser) fn unavailable(self) -> Self {
        Self { view: None, ..self }
    }

    #[inline]
    pub(in crate::parser) fn if_outer_tail(self) -> Self {
        #[cfg(test)]
        self.observe(ProofSite::IfOuterTail);
        self
    }

    #[cfg(test)]
    pub(in crate::parser) fn assert_shape(self, baseline: Option<usize>, frames: &[usize]) {
        let view = self.view.expect("available ordinary carrier");
        assert_eq!(view.statement_baseline, baseline);
        let mut frame = view.companions;
        for expected in frames {
            let actual = frame.expect("missing companion frame");
            assert_eq!(actual.baseline, *expected);
            frame = actual.parent;
        }
        assert!(frame.is_none(), "unexpected companion frame");
    }

    #[cfg(test)]
    pub(in crate::parser) fn with_proof(
        mut self,
        proof: fn(ProofSite, Option<AmbientClaimView<'_>>),
    ) -> Self {
        self.proof = Some(proof);
        self
    }

    #[cfg(test)]
    pub(in crate::parser) fn observe(self, site: ProofSite) {
        if let Some(proof) = self.proof {
            proof(site, self.view);
        }
    }
}

#[cfg(test)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::parser) enum ProofSite {
    PolymorphicVariant,
    ElseBody,
    IfOuterTail,
}

#[derive(Clone, Copy)]
pub(in crate::parser) struct AmbientClaimView<'frame> {
    statement_baseline: Option<usize>,
    companions: Option<&'frame AmbientIfCompanion<'frame>>,
}

pub(in crate::parser) struct AmbientIfCompanion<'frame> {
    #[allow(
        dead_code,
        reason = "ambient-claim prerequisite retains companion evidence until its observer gate"
    )]
    parent: Option<&'frame AmbientIfCompanion<'frame>>,
    #[allow(
        dead_code,
        reason = "ambient-claim prerequisite retains companion evidence until its observer gate"
    )]
    baseline: usize,
    #[allow(
        dead_code,
        reason = "ambient-claim prerequisite retains companion evidence until its observer gate"
    )]
    exact_words: &'static [&'static str],
}

#[derive(Clone, Copy)]
#[allow(
    dead_code,
    reason = "ambient-claim prerequisite reserves this evidence for the separately approved observer"
)]
pub(in crate::parser) struct AmbientPositionEvidence<'word> {
    pub(in crate::parser) has_physical_newline: bool,
    pub(in crate::parser) following_line_indent: usize,
    pub(in crate::parser) following_word: Option<&'word str>,
}

impl<'frame> AmbientClaimView<'frame> {
    pub(in crate::parser) fn root_statement(baseline: usize) -> Self {
        Self {
            statement_baseline: Some(baseline),
            companions: None,
        }
    }

    pub(in crate::parser) fn statement(self, baseline: usize) -> Self {
        Self {
            statement_baseline: Some(baseline),
            ..self
        }
    }

    pub(in crate::parser) fn braced(self) -> Self {
        Self {
            statement_baseline: None,
            companions: None,
        }
    }

    pub(in crate::parser) fn if_companion(self, baseline: usize) -> AmbientIfCompanion<'frame> {
        AmbientIfCompanion {
            parent: self.companions,
            baseline,
            exact_words: &["elsif", "else"],
        }
    }

    pub(in crate::parser) fn with_if<'inner>(
        self,
        companion: &'inner AmbientIfCompanion<'frame>,
    ) -> AmbientClaimView<'inner>
    where
        'frame: 'inner,
    {
        AmbientClaimView {
            statement_baseline: self.statement_baseline,
            companions: Some(companion),
        }
    }

    #[allow(
        dead_code,
        reason = "ambient-claim prerequisite explicitly keeps the query unused outside its proof tests"
    )]
    pub(in crate::parser) fn claims(self, evidence: AmbientPositionEvidence<'_>) -> bool {
        if evidence.has_physical_newline
            && self
                .statement_baseline
                .is_some_and(|b| evidence.following_line_indent < b)
        {
            return true;
        }
        let Some(word) = evidence.following_word else {
            return false;
        };
        let mut companion = self.companions;
        while let Some(frame) = companion {
            if (!evidence.has_physical_newline || evidence.following_line_indent >= frame.baseline)
                && frame.exact_words.contains(&word)
            {
                return true;
            }
            companion = frame.parent;
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn position(newline: bool, indent: usize, word: Option<&str>) -> AmbientPositionEvidence<'_> {
        AmbientPositionEvidence {
            has_physical_newline: newline,
            following_line_indent: indent,
            following_word: word,
        }
    }

    #[test]
    fn ordinary_baseline_claims_only_physical_strict_dedent() {
        let view = AmbientClaimView::root_statement(4);
        assert!(!view.claims(position(false, 0, None)));
        assert!(!view.claims(position(true, 4, None)));
        assert!(!view.claims(position(true, 5, None)));
        assert!(view.claims(position(true, 3, None)));
        assert!(!view.statement(2).claims(position(true, 3, None)));
    }

    #[test]
    fn companion_words_are_exact_and_indentation_sensitive() {
        let caller = AmbientClaimView::root_statement(0);
        let frame = caller.if_companion(4);
        let arm = caller.with_if(&frame);
        for word in ["else", "elsif"] {
            assert!(arm.claims(position(false, 0, Some(word))));
            assert!(arm.claims(position(true, 4, Some(word))));
            assert!(!arm.claims(position(true, 3, Some(word))));
        }
        for word in [None, Some("elsewhere"), Some("elsif_suffix")] {
            assert!(!arm.claims(position(false, 0, word)));
        }
    }

    #[test]
    fn ineligible_inner_companion_does_not_hide_an_eligible_outer_frame() {
        let root = AmbientClaimView::root_statement(0);
        let outer_frame = root.if_companion(2);
        let outer = root.with_if(&outer_frame);
        let inner_frame = outer.if_companion(6);
        let inner = outer.with_if(&inner_frame);
        assert!(inner.claims(position(true, 3, Some("else"))));
        assert!(!inner.claims(position(true, 1, Some("else"))));
        assert!(inner.statement(8).claims(position(true, 7, None)));
        assert!(inner.statement(0).claims(position(true, 3, Some("elsif"))));
    }

    #[test]
    fn braced_barrier_hides_both_owners_and_return_restores_the_caller() {
        let root = AmbientClaimView::root_statement(4);
        let frame = root.if_companion(4);
        let caller = root.with_if(&frame);
        let braced = caller.braced();
        assert!(!braced.claims(position(true, 0, Some("else"))));
        assert!(!braced.claims(position(false, 0, Some("elsif"))));
        assert!(caller.claims(position(true, 0, None)));
        assert!(caller.claims(position(false, 0, Some("else"))));
    }

    #[test]
    fn own_else_and_outer_tail_use_caller_without_the_retired_frame() {
        let root = AmbientClaimView::root_statement(0);
        {
            let frame = root.if_companion(2);
            let arm = root.with_if(&frame);
            assert!(arm.claims(position(false, 0, Some("else"))));
            // This caller value is also the owning Else body and outer tail view.
            assert!(!root.claims(position(false, 0, Some("else"))));
        }
        assert!(!root.claims(position(true, 2, Some("elsif"))));

        let outer_frame = root.if_companion(1);
        let outer = root.with_if(&outer_frame);
        {
            let inner_frame = outer.if_companion(4);
            let inner = outer.with_if(&inner_frame);
            assert!(inner.claims(position(true, 4, Some("else"))));
        }
        assert!(outer.claims(position(true, 1, Some("else"))));
    }

    #[test]
    fn unavailable_virtual_and_yumark_views_survive_every_ordinary_transition() {
        let unavailable: Option<AmbientClaimView<'_>> = None;
        let statement = unavailable.map(|view| view.statement(0));
        let indented = statement.map(|view| view.statement(4));
        let braced = indented.map(AmbientClaimView::braced);
        let frame = braced.map(|view| view.if_companion(4));
        let arm = braced.map(|view| view.with_if(frame.as_ref().unwrap()));
        assert!(statement.is_none());
        assert!(indented.is_none());
        assert!(braced.is_none());
        assert!(frame.is_none());
        assert!(arm.is_none());
        assert!(unavailable.is_none());
    }
}
