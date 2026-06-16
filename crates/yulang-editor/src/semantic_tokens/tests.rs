use super::*;

mod tests {
    use super::*;
    use parser::op::{BpVec, OpDef};

    #[test]
    fn return_is_colored() {
        let tokens = compute("if x == 5: return x");
        // tokens are [delta_line, delta_col, len, type, modifiers] groups
        // `return` is currently visible in the CST as a call-position identifier.
        let has_return = tokens.chunks(5).any(|c| c[2] == 6 && c[3] == FUNCTION);
        assert!(
            has_return,
            "expected 'return' (len=6) to be colored FUNCTION; got: {:?}",
            tokens
        );
    }

    #[test]
    fn imported_prefix_operator_is_colored_as_operator() {
        let mut table = standard_op_table();
        table.0.insert(
            "return".into(),
            OpDef {
                prefix: Some(BpVec::new(vec![1])),
                nullfix: true,
                ..OpDef::default()
            },
        );

        let tokens = compute_with_op_table("if x == 5: return x", Some(table));
        let chunks: Vec<&[u32]> = tokens.chunks(5).collect();

        assert!(chunks.iter().any(|c| c[2] == 6 && c[3] == OPERATOR));
        assert!(!chunks.iter().any(|c| c[2] == 6 && c[3] == FUNCTION));
    }

    #[test]
    fn registered_operator_is_not_colored_as_function() {
        let tokens = compute("if x == 5: x");
        let chunks: Vec<&[u32]> = tokens.chunks(5).collect();

        assert!(chunks.iter().any(|c| c[2] == 2 && c[3] == OPERATOR));
        assert!(!chunks.iter().any(|c| c[2] == 2 && c[3] == FUNCTION));
    }

    #[test]
    fn inflate_call_is_colored() {
        let tokens = compute("inflate { base: 3 }");
        // "inflate" has len=7
        let has_inflate = tokens.chunks(5).any(|c| c[2] == 7 && c[3] == FUNCTION);
        assert!(
            has_inflate,
            "expected 'inflate' (len=7) to be colored FUNCTION; got: {:?}",
            tokens
        );
    }

    #[test]
    fn colon_call_name_is_colored() {
        let tokens = compute("sub:\n  0");
        let chunks: Vec<&[u32]> = tokens.chunks(5).collect();

        assert!(
            chunks.iter().any(|c| c[2] == 3 && c[3] == FUNCTION),
            "expected 'sub' (len=3) to be colored FUNCTION; got: {:?}",
            tokens
        );
    }

    #[test]
    fn sigil_prefixes_are_colored_consistently() {
        let tokens = compute("my $xs = [1]\n&xs[0] = 2");
        let chunks: Vec<&[u32]> = tokens.chunks(5).collect();

        assert_eq!(
            chunks
                .iter()
                .filter(|c| c[2] == 1 && c[3] == OPERATOR)
                .count(),
            2,
            "expected '$' and '&' sigils to be colored OPERATOR; got: {:?}",
            tokens
        );
    }

    #[test]
    fn record_field_name_is_colored_as_property() {
        let tokens = compute("point { x: 3, y: y } .norm2");
        let chunks: Vec<&[u32]> = tokens.chunks(5).collect();

        assert!(
            chunks.iter().any(|c| c[2] == 1 && c[3] == PROPERTY),
            "expected record field names (len=1) to be colored PROPERTY; got: {:?}",
            tokens
        );
    }

    #[test]
    fn struct_name_and_dot_field_keep_editor_token_kinds() {
        let tokens = compute("struct point { x: int } with:\n  our p.norm2 = p.x\n");
        let chunks: Vec<&[u32]> = tokens.chunks(5).collect();

        assert!(
            chunks.iter().any(|c| c[2] == 5 && c[3] == TYPE),
            "expected struct name 'point' to be colored TYPE; got: {:?}",
            tokens
        );
        assert!(
            chunks.iter().any(|c| c[2] == 5 && c[3] == FUNCTION),
            "expected dot-field 'norm2' to be colored FUNCTION; got: {:?}",
            tokens
        );
        assert!(
            !chunks.iter().any(|c| c[2] == 5 && c[3] == PROPERTY),
            "expected dot-field 'norm2' not to be colored PROPERTY; got: {:?}",
            tokens
        );
    }

    #[test]
    fn block_colon_call_is_not_colored_as_record_field() {
        let tokens = compute("sub { return 1 }");
        let chunks: Vec<&[u32]> = tokens.chunks(5).collect();

        assert!(!chunks.iter().any(|c| c[2] == 3 && c[3] == PROPERTY));
    }

    #[test]
    fn path_call_tail_is_colored_as_function() {
        let tokens = compute("result::err err");
        let chunks: Vec<&[u32]> = tokens.chunks(5).collect();

        assert!(chunks.iter().any(|c| c[2] == 3 && c[3] == FUNCTION));
    }

    #[test]
    fn intermediate_path_segments_are_not_colored_as_function() {
        let tokens = compute("std::list::merge xs ys\nstd::opt::opt::nil");
        let chunks: Vec<&[u32]> = tokens.chunks(5).collect();

        assert!(!chunks.iter().any(|c| c[2] == 4 && c[3] == FUNCTION));
        assert!(!chunks.iter().any(|c| c[2] == 4 && c[3] == NAMESPACE));
        assert!(!chunks.iter().any(|c| c[2] == 3 && c[3] == NAMESPACE));
        assert!(
            chunks.iter().any(|c| c[2] == 5 && c[3] == FUNCTION),
            "expected empty/singleton definition names to be colored FUNCTION; got: {:?}",
            tokens
        );
        assert!(!chunks.iter().any(|c| c[2] == 3 && c[3] == FUNCTION));
    }

    #[test]
    fn path_tail_reference_is_not_colored_as_function() {
        let tokens = compute("std::opt::opt::nil\nstd::opt::opt::just");
        let chunks: Vec<&[u32]> = tokens.chunks(5).collect();

        assert!(!chunks.iter().any(|c| c[2] == 3 && c[3] == FUNCTION));
        assert!(!chunks.iter().any(|c| c[2] == 4 && c[3] == FUNCTION));
    }

    #[test]
    fn paren_function_definition_name_is_colored_as_function() {
        let tokens = compute("pub empty(): list 'a = []\npub singleton(x: 'a): list 'a = [x]");
        let chunks: Vec<&[u32]> = tokens.chunks(5).collect();

        assert!(
            chunks.iter().any(|c| c[2] == 5 && c[3] == FUNCTION),
            "expected empty/singleton definition names to be colored FUNCTION; got: {:?}",
            tokens
        );
        assert!(
            chunks.iter().any(|c| c[2] == 9 && c[3] == FUNCTION),
            "expected empty/singleton definition names to be colored FUNCTION; got: {:?}",
            tokens
        );
    }

    #[test]
    fn case_pattern_names_are_colored_as_variables() {
        let tokens = compute("case r:\n  result::err err -> result::err err");
        let chunks: Vec<&[u32]> = tokens.chunks(5).collect();

        assert!(chunks.iter().any(|c| c[2] == 3 && c[3] == PATTERN));
    }

    #[test]
    fn pattern_path_is_colored_as_constructor() {
        let tokens = compute("case v:\n  std::opt::opt::just x -> x\n  std::opt::opt::nil -> y");
        let chunks: Vec<&[u32]> = tokens.chunks(5).collect();

        assert!(
            chunks.iter().any(|c| c[2] == 3 && c[3] == TYPE),
            "expected path constructor segments like 'std'/'nil' to be colored TYPE; got: {:?}",
            tokens
        );
        assert!(
            chunks.iter().any(|c| c[2] == 4 && c[3] == TYPE),
            "expected path constructor segments like 'just' to be colored TYPE; got: {:?}",
            tokens
        );
        assert!(!chunks.iter().any(|c| c[2] == 4 && c[3] == FUNCTION));
        assert!(!chunks.iter().any(|c| c[2] == 3 && c[3] == FUNCTION));
    }

    #[test]
    fn bare_pattern_name_stays_pattern() {
        let tokens = compute("case v:\n  nil -> x");
        let chunks: Vec<&[u32]> = tokens.chunks(5).collect();

        assert!(chunks.iter().any(|c| c[2] == 3 && c[3] == PATTERN));
        assert!(!chunks.iter().any(|c| c[2] == 3 && c[3] == FUNCTION));
    }

    #[test]
    fn bare_pattern_call_is_colored_as_constructor() {
        let tokens = compute("case v:\n  last() -> x");
        let chunks: Vec<&[u32]> = tokens.chunks(5).collect();

        assert!(
            chunks.iter().any(|c| c[2] == 4 && c[3] == TYPE),
            "expected bare pattern call 'last()' to color 'last' as TYPE; got: {:?}",
            tokens
        );
    }

    #[test]
    fn resolved_highlights_limit_bare_pattern_constructor_calls() {
        let mut highlights = ResolvedHighlightInfo::new();
        highlights.insert_constructor_name("last");
        let tokens = compute_with_op_table_and_highlights(
            "case v:\n  last() -> x\n  not_ctor() -> y",
            None,
            Some(&highlights),
        );
        let chunks: Vec<&[u32]> = tokens.chunks(5).collect();

        assert!(
            chunks.iter().any(|c| c[2] == 4 && c[3] == TYPE),
            "expected resolved constructor call 'last()' to color 'last' as TYPE; got: {:?}",
            tokens
        );
        assert!(
            !chunks.iter().any(|c| c[2] == 8 && c[3] == TYPE),
            "expected unresolved bare pattern call 'not_ctor()' to stay non-constructor; got: {:?}",
            tokens
        );
    }

    #[test]
    fn resolved_highlights_require_exact_constructor_path() {
        let mut highlights = ResolvedHighlightInfo::new();
        highlights.insert_constructor_path(["std", "opt", "opt", "nil"]);
        let tokens = compute_with_op_table_and_highlights(
            "std::opt::opt::nil\nother::opt::opt::nil",
            None,
            Some(&highlights),
        );
        let chunks: Vec<&[u32]> = tokens.chunks(5).collect();

        assert!(
            chunks.iter().any(|c| c[2] == 3 && c[3] == TYPE),
            "expected exact constructor path tail 'nil' to be colored TYPE; got: {:?}",
            tokens
        );
        assert_eq!(
            chunks.iter().filter(|c| c[2] == 3 && c[3] == TYPE).count(),
            1,
            "expected only exact constructor path tail to be colored TYPE; got: {:?}",
            tokens
        );
    }

    #[test]
    fn lexical_tokens_are_colored_by_lsp() {
        let tokens = compute("// note\nmy answer = \"ok\"");
        let chunks: Vec<&[u32]> = tokens.chunks(5).collect();

        assert!(chunks.iter().any(|c| c[2] == 7 && c[3] == COMMENT));
        assert!(chunks.iter().any(|c| c[2] == 2 && c[3] == KEYWORD));
        assert!(chunks.iter().any(|c| c[2] == 1 && c[3] == DELIMITER));
        assert!(chunks.iter().any(|c| c[2] == 4 && c[3] == STRING));
    }

    #[test]
    fn leading_comment_does_not_shift_parser_token_positions() {
        let source = "// note\nmy answer = \"ok\"";
        let tokens = decode_tokens(&compute(source));

        assert!(tokens.contains(&(0, 0, 7, COMMENT)));
        assert!(tokens.contains(&(1, 0, 2, KEYWORD)));
        assert!(tokens.contains(&(1, 10, 1, DELIMITER)));
        assert!(tokens.contains(&(1, 12, 4, STRING)));
    }

    #[test]
    fn colon_and_path_separator_are_delimiters() {
        let tokens = compute("my result = std::int::add: 1");
        let chunks: Vec<&[u32]> = tokens.chunks(5).collect();

        assert!(chunks.iter().any(|c| c[2] == 1 && c[3] == COLON));
        assert!(chunks.iter().any(|c| c[2] == 2 && c[3] == DELIMITER));
        assert!(!chunks.iter().any(|c| c[2] == 2 && c[3] == OPERATOR));
    }

    fn decode_tokens(encoded: &[u32]) -> Vec<(u32, u32, u32, u32)> {
        let mut line = 0;
        let mut col = 0;
        encoded
            .chunks_exact(5)
            .map(|chunk| {
                line += chunk[0];
                if chunk[0] == 0 {
                    col += chunk[1];
                } else {
                    col = chunk[1];
                }
                (line, col, chunk[2], chunk[3])
            })
            .collect()
    }
}
