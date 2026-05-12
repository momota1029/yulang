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

; ── shallow semantic-ish syntax ────────────────────
(binding_decl
  name: (identifier) @function)

(function_header
  name: (identifier) @function)

(field_binding_decl
  field: (dot_field) @property)

(value_binding_decl
  name: (identifier) @variable)

(function_call
  function: (identifier) @function)

(path_expr
  head: (identifier) @namespace)

(case_arm
  pattern: (pattern_expr
    (identifier) @variable))

(case_arm
  pattern: (pattern_expr
    (sigil_ident) @variable.builtin))

(record_field
  name: (identifier) @property)

; ── atoms ──────────────────────────────────────────
(number) @number
(type_var) @type
(apostrophe) @punctuation.special
(sigil_ident) @variable.builtin

; ── punctuation / operators ────────────────────────
(dot_field) @property
(path_sep) @punctuation.delimiter
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
