# R281 — Yulang2 escaped quote in string literals

Status: checkpointed parser-only addendum under unchanged-source R149.

The exact pinned fmt source writes a quotation mark inside a normal string as backslash-quote, followed by a second quote that closes the string. The current escape owner gives every quote after a backslash to the close-sentinel recovery path, which is useful for an incomplete escape but rejects the complete source form.

When a normal-string backslash is followed by two consecutive quotes, consume the first as the simple escaped-quote target and let the ordinary string owner consume the second as StringEnd. Keep the existing sentinel fallback for a single quote with no following closer. This is a syntax ownership rule only; it establishes no runtime string value, role result or theorem.

## Result

The exact source form parses as one `StringEscape` with a `StringEscapeSimple` quote target, followed by the normal `StringEnd`. The legacy lone-quote sentinel remains intact. The exact fmt source now has zero syntax diagnostics without source rewriting. Runtime string value and later compiler stages remain separate obligations.
