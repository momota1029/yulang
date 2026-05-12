; ── comments ───────────────────────────────────────
(line_comment) @comment
(block_comment) @comment

; ── keywords: control flow ─────────────────────────
((keyword) @keyword.control
 (#match? @keyword.control "^(if|else|elsif|case|catch|do)$"))

; ── keywords: declarations ─────────────────────────
((keyword) @keyword.storage
 (#match? @keyword.storage "^(my|our|pub|type|struct|enum|error|role|impl|mod)$"))

; ── keywords: import / module ──────────────────────
((keyword) @keyword.import
 (#match? @keyword.import "^(use|as)$"))

; ── keywords: effect / cast ────────────────────────
((keyword) @keyword.special
 (#match? @keyword.special "^(act|cast)$"))

; ── keywords: remaining ────────────────────────────
((keyword) @keyword
 (#match? @keyword "^(for|in|with|where|via|rule|prefix|infix|suffix|nullfix|lazy)$"))

; ── strings ────────────────────────────────────────
(string) @string
(string_escape) @string.escape
(string_interp) @embedded

; ── rule literals ──────────────────────────────────
(rule_literal) @string.regex
(rule_lit_interp) @embedded
(rule_lit_lazy
  (rule_lazy_name) @variable.parameter)

; ── atoms ──────────────────────────────────────────
(number) @number
(type_var) @type
(apostrophe) @punctuation.special
(sigil_ident) @variable.builtin

; ── identifiers ────────────────────────────────────
(identifier) @variable

; ── punctuation / operators ────────────────────────
(dot_field) @property
(arrow) @operator
(fat_arrow) @operator
(dot_dot) @operator
(dot_dot_eq_excl) @operator
(colon) @operator
(equals) @punctuation.delimiter
(pipe) @operator
(comma) @punctuation.delimiter
(semicolon) @punctuation.delimiter
(backslash) @operator
(amp) @operator
(paren_group ["(" ")"] @punctuation.bracket)
(bracket_group ["[" "]"] @punctuation.bracket)
(brace_group ["{" "}"] @punctuation.bracket)
(operator) @operator
