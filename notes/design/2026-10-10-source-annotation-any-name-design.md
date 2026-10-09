# Built-in Type name `any`

Date: 2026-10-10
Status: user-approved name-resolution decision; semantic root/law and implementation open
Authority: approved `source-annotation-any-name-resolution/q1/d1`; integration receipt at the matching q1 directory

For the selected source annotation case, lowercase `any` is a built-in Type
name. It resolves without a declaration or import, and builtin resolution takes
precedence over same-named type declarations, imports, or aliases; they cannot
shadow this meaning. No uppercase `Any` builtin alias is introduced. Whether a
conflicting declaration itself is accepted or diagnosed is not decided here.

This decision covers Type-name introduction and lookup only. It does not define
the meaning of `Value(Any)`, construct its ordinary root, membership guards or
evidence, establish the hereditary Top law or Direct proof, determine value
namespace behavior, or authorize compiler implementation, production routing,
runtime changes, or F5 cutover. The reviewed one-case annotation design remains
the governing owner plan with `any` substituted for the selected source
spelling; its semantic producer dependencies remain open.
