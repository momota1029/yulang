; ── comments ───────────────────────────────────────
(line_comment) @comment
(block_comment) @comment

; ── keywords ───────────────────────────────────────
(keyword) @keyword

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
(path_sep) @punctuation.delimiter
(dot_field) @property
(arrow) @operator
(fat_arrow) @operator
(dot_dot) @operator
(dot_dot_eq_excl) @operator
(colon) @punctuation.delimiter
(equals) @operator
(pipe) @operator
(comma) @punctuation.delimiter
(semicolon) @punctuation.delimiter
(backslash) @operator
(amp) @operator
(paren_group ["(" ")"] @punctuation.bracket)
(bracket_group ["[" "]"] @punctuation.bracket)
(brace_group ["{" "}"] @punctuation.bracket)
(operator) @operator
