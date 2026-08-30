    fn gate2_performance_parse_ast<'source>(
        source: &'source str,
        table: &OperatorTable,
        policy: StatementSequencePolicy,
    ) -> (Vec<Recovered<Statement<'source>>>, usize) {
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);
        let items = match policy {
            StatementSequencePolicy::Indented { block_indent, .. } => {
                i.run(scan_trivia).expect("opening trivia");
                let scope = push_indented_statement_block_scope(&mut i, block_indent);
                let items = parse_statement_sequence(table, policy, &mut i);
                pop_indented_statement_block_scope(&mut i, scope, block_indent);
                items
            }
            StatementSequencePolicy::BracedPrimary => {
                i.run(scan_punctuation).expect("opening brace");
                let scope = push_braced_statement_block_scope(
                    &mut i,
                    BracedBarrierOrigin::BracedStatementBlockExpression,
                );
                consume_trivia(&mut i).expect("trivia scanning is total");
                let items = parse_statement_sequence(table, policy, &mut i);
                consume_trivia(&mut i).expect("trivia scanning is total");
                i.run(recognize_braced_statement_block_close)
                    .expect("closing brace");
                pop_braced_statement_block_scope(&mut i, scope);
                items
            }
        };
        (items, i.pos())
    }

    fn gate2_performance_commit_direct(
        source: &str,
        table: &OperatorTable,
        policy: StatementSequencePolicy,
    ) -> (SyntaxNode, usize, usize) {
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);
        let mut committed = Probe::new(i).commit(FullCstOutput::new(source));
        committed.start_node(SyntaxKind::Root);
        match policy {
            StatementSequencePolicy::Indented { block_indent, .. } => {
                let opening = committed
                    .probe(|probe| probe.input().run(scan_trivia))
                    .expect("opening trivia");
                committed.emit_trivia(&opening);
                let scope = committed.probe(|probe| {
                    push_indented_statement_block_scope(probe.input(), block_indent)
                });
                commit_statement_sequence(table, policy, &mut committed);
                committed.probe(|probe| {
                    pop_indented_statement_block_scope(probe.input(), scope, block_indent)
                });
            }
            StatementSequencePolicy::BracedPrimary => {
                let open = committed
                    .probe(|probe| probe.input().run(scan_punctuation))
                    .expect("opening brace");
                committed.token(SyntaxKind::LBrace, open.range());
                let scope = committed.probe(|probe| {
                    push_braced_statement_block_scope(
                        probe.input(),
                        BracedBarrierOrigin::BracedStatementBlockExpression,
                    )
                });
                let trivia = committed
                    .probe(|probe| probe.input().run(scan_trivia))
                    .expect("trivia scanning is total");
                committed.emit_trivia(&trivia);
                commit_statement_sequence(table, policy, &mut committed);
                let trivia = committed
                    .probe(|probe| probe.input().run(scan_trivia))
                    .expect("trivia scanning is total");
                committed.emit_trivia(&trivia);
                let close = committed
                    .probe(|probe| probe.input().run(recognize_braced_statement_block_close))
                    .expect("closing brace");
                committed.token(SyntaxKind::RBrace, close);
                committed.probe(|probe| pop_braced_statement_block_scope(probe.input(), scope));
            }
        }
        let consumed = committed.probe(|probe| probe.input().pos());
        committed.finish_node();
        let output = committed.into_output();
        let recovery_count = output.committed_recoveries().len();
        let root = SyntaxNode::new_root(output.finish_complete());
        (root, consumed, recovery_count)
    }

    #[test]
    #[ignore = "manual Gate 2 sequence performance measurement"]
    fn gate2_statement_sequence_performance_harness() {
        use std::hint::black_box;

        let case =
            std::env::var("YULANG_GATE2_SEQUENCE_CASE").expect("set YULANG_GATE2_SEQUENCE_CASE");
        let count: usize = std::env::var("YULANG_GATE2_SEQUENCE_ITEMS")
            .expect("set YULANG_GATE2_SEQUENCE_ITEMS")
            .parse()
            .expect("item count is a positive integer");
        let repeats: usize = std::env::var("YULANG_GATE2_SEQUENCE_REPEATS")
            .unwrap_or_else(|_| "1".to_owned())
            .parse()
            .expect("repeat count is a positive integer");
        assert!(count > 0);
        assert!(repeats > 0);

        let source = match case.as_str() {
            "indented_ast" | "indented_direct" => {
                let mut source = String::with_capacity(count * 8);
                for _ in 0..count {
                    source.push_str("\n  value");
                }
                source
            }
            "indented_direct_comment_stress" => {
                let item = "\n  @ /* first; ) ] } , / internal */ value";
                let mut source = String::with_capacity(count * item.len());
                for _ in 0..count {
                    source.push_str(item);
                }
                source
            }
            "braced_ast" | "braced_direct" => {
                let mut source = String::with_capacity(count * 6 + 2);
                source.push('{');
                for index in 0..count {
                    if index > 0 {
                        source.push(';');
                    }
                    source.push_str("value");
                }
                source.push('}');
                source
            }
            _ => panic!("unknown performance case: {case}"),
        };
        let table = canonical_operator_table();

        match case.as_str() {
            "indented_ast" | "braced_ast" => {
                let policy = if case == "indented_ast" {
                    StatementSequencePolicy::Indented {
                        block_indent: 2,
                        options: IndentedStatementBlockOptions::default(),
                    }
                } else {
                    StatementSequencePolicy::BracedPrimary
                };
                let mut retained = None;
                for _ in 0..repeats {
                    retained = Some(gate2_performance_parse_ast(&source, &table, policy));
                    black_box(retained.as_ref());
                }
                let (items, consumed) = retained.expect("at least one timed parse");
                assert_eq!(items.len(), count);
                assert_eq!(consumed, source.len());
            }
            "indented_direct" | "braced_direct" | "indented_direct_comment_stress" => {
                let policy = if case.starts_with("indented") {
                    StatementSequencePolicy::Indented {
                        block_indent: 2,
                        options: IndentedStatementBlockOptions::default(),
                    }
                } else {
                    StatementSequencePolicy::BracedPrimary
                };
                let mut retained = None;
                for _ in 0..repeats {
                    retained = Some(gate2_performance_commit_direct(&source, &table, policy));
                    black_box(retained.as_ref());
                }
                let (root, consumed, recovery_count) =
                    retained.expect("at least one timed direct commit");
                assert_eq!(consumed, source.len());
                assert_eq!(
                    recovery_count,
                    if case == "indented_direct_comment_stress" {
                        count
                    } else {
                        0
                    }
                );
                assert_eq!(
                    root.descendants()
                        .filter(|node| node.kind() == SyntaxKind::Statement)
                        .count(),
                    count
                );
                assert_eq!(root.to_string(), source);
            }
            _ => unreachable!("case checked while constructing the source"),
        }
    }
