# Cycle64: captured parent to original where models

Status: Draft implementation plan. Scope: the existing finite interval candidate kernel.

Goal: for arbitrary source valuation, an actually accepted parent and its original
head model preserve the same valuation in every actual where-child interval.
No interval centre is chosen by execution. The existing total binding lookup is
used only at names proven bound by the real candidate checker. Child templates
may contain pair, tick, and join, although candidate heads retain their explicitly
limited structural grammar.

Independent judgment: HeadFits interprets each original declaration template
under the shared source valuation and compares it with the actual child endpoints.
Prove template monotonicity, bound-lookup preservation, and normalization
invariance, then derive all child models from the original parent model.

Public goal: actual inspect/constraint generation of one arbitrary parent yields generated
atoms iff one shared valuation satisfies old source demands, the original parent
head, and every generated original where-template. The child conditions are
conservative consequences, not evidence that a child dictionary exists.

This supports source_boundary_adequate and generated_work_closed. All five main
B4 bridges remain open. State-dependent graph materialization, canonical source
map construction, recursive child selection, saturation, and dictionary semantics
are not asserted. Source names are still supplied explicitly.

Yulang2 evidence read before implementation: audit x-oracle X13–X16 and
C3-PARENT/C3-PARENT-NEG. Those observations motivate shared source constraints;
they do not establish this arbitrary finite theorem. No new language rule is chosen.

Implementation also proves original endpoint-name provenance: normalize introduces
no names, capture retains original endpoint subtrees, finite bound lookup selects
one of those subtrees, and each actual child substitution therefore uses only
parent endpoint names. `returned_sources` is unconditional apart from the real
return, even for inconsistent inputs. This is a general multibinder extension of
the earlier unary source-template provenance, not yet canonical graph allocation.
