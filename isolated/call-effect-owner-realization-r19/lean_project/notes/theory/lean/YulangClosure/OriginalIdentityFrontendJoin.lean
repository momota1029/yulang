import YulangClosure.OriginalIdentityEntryOrigin

/-!
# Original Identity frontend join: first owner boundary

This module deliberately introduces no frontend representation or correspondence
premise. The pinned inline Lambda builder retains an authentic Lambda
SourceNodeKey and binder token range, a branded HirParameterId, and a branded
LocalSourceIndex for the body (yu-hir/module/local_source.rs:2092-2122).
Its exact source accessor returns InlineLambda { lambda, binder }, whereas the
IdentifierPattern accessor returns MissingSource for this constructor
(yu-hir/shadow.rs:1787-1829). This is supported inline syntax, not a refusal.

OriginalIdentityRealization.Identity.parameter constructs an original Formal
and a separate Source.wild patternSite, plus a resolved Source.name body.
The imported Lean source model has no checked interpretation of the authentic
parse/HIR owners into its Declaration, ambient ScopeEntry list, Context,
Site or Name. In particular, no source constructor currently assigns that
inline binder's formalSite and wild patternSite from its Lambda/token origin.

Required next owner: original-source/frontend interpretation of this exact
inline constructor, retaining source-root/artifact branding, lexical binding,
occurrence/site incidence, and the original source-rule expansion. The missing
construction must derive an Identity and enclosing original App from one
frontend origin, rather than assume their desired equations. The parent
source constructors are audited in AuditOriginalIdentityFrontendJoin.lean.

No Raw program table, Closure/provider equality, generated label, saved/caller
environment equality, admission, or Callee prefix application follows here.
This absent interface is not a theorem that a future join is impossible, and
is not a source-qualified counterexample. All original parents remain open.
-/
namespace YulangClosure.OriginalIdentityFrontendJoin
end YulangClosure.OriginalIdentityFrontendJoin
