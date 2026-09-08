use crate::lexical::yumark::{FenceOpener, FencePrefixPolicy};
use crate::tests::support::*;

fn active_fence() -> FenceBoundary {
    FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    }
}

fn plain_fence() -> FenceBoundary {
    FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::None,
        close_column: 0,
    }
}

fn syntax_tokens(green: GreenNode) -> Vec<(SyntaxKind, String)> {
    SyntaxNode::new_root(green)
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .map(|token| (token.kind(), token.text().to_owned()))
        .collect()
}

#[test]
fn normalized_type_declaration_streams_bare_and_visibility_headers() {
    let fence = active_fence();
    for (source, accepted, remainder, prefixes, parameters, line_entry) in [
        (
            "> > type T _x 'a = U\n> > ```\nouter",
            "> > type T _x 'a = U",
            "> > ```\nouter",
            1,
            2,
            LineEntry::PhysicalStart,
        ),
        (
            "> > our\r\n> >   type T = U\r\n> > ```\r\nouter",
            "> > our\r\n> >   type T = U",
            "> > ```\r\nouter",
            2,
            0,
            LineEntry::PhysicalStart,
        ),
    ] {
        let (green, exit, actual_remainder) =
            run_statement_normalized(source, 4100, LineEntry::PhysicalStart, Some(&fence));
        let NormalizedExit::Complete(Err(Either::Left(boundary)), actual_line_entry) = exit else {
            panic!("the Type owner must stream to the exact fence: {source:?}")
        };
        assert!(boundary.payload_view().is_boundary(), "{source:?}");
        assert_eq!(actual_line_entry, line_entry, "{source:?}");
        let root = SyntaxNode::new_root(green);
        assert_eq!(root.to_string(), accepted, "{source:?}");
        assert_eq!(actual_remainder, remainder, "{source:?}");
        assert_eq!(
            root.descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .filter(|token| token.kind() == SyntaxKind::YmQuotePrefix)
                .count(),
            prefixes,
            "{source:?}",
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::TypeDeclaration)
                .count(),
            1,
            "{source:?}",
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::DeclarationTypeParameterList)
                .flat_map(|node| node.children_with_tokens())
                .filter(|element| {
                    element.as_token().is_some_and(|token| {
                        matches!(
                            token.kind(),
                            SyntaxKind::Identifier | SyntaxKind::SigilIdentifier
                        )
                    })
                })
                .count(),
            parameters,
            "{source:?}",
        );
    }
}

#[test]
fn normalized_type_declaration_keeps_each_phase_boundary_pending() {
    let fence = active_fence();
    for (source, accepted, remainder, missing, line_entry) in [
        (
            "> > type\n> > ```\nouter",
            "> > type",
            "> > ```\nouter",
            1,
            LineEntry::PhysicalStart,
        ),
        (
            "> > type T\n> ]\nouter",
            "> > type T",
            "> ]\nouter",
            0,
            LineEntry::PhysicalStart,
        ),
        (
            "> > type T =\n> > ```\nouter",
            "> > type T =",
            "> > ```\nouter",
            1,
            LineEntry::PhysicalStart,
        ),
        (
            "> > type T derives\n> > ```\nouter",
            "> > type T derives",
            "> > ```\nouter",
            1,
            LineEntry::PhysicalStart,
        ),
        (
            "> > type T derives Role via\n> > ```\nouter",
            "> > type T derives Role via",
            "> > ```\nouter",
            1,
            LineEntry::PhysicalStart,
        ),
        ("> > type T", "> > type T", "", 0, LineEntry::InLine),
    ] {
        let (green, exit, actual_remainder) =
            run_statement_normalized(source, 4175, LineEntry::PhysicalStart, Some(&fence));
        let NormalizedExit::Complete(Err(Either::Left(boundary)), actual_line_entry) = exit else {
            panic!("Type phase must return the exact fence boundary: {source:?}")
        };
        assert!(boundary.payload_view().is_boundary(), "{source:?}");
        assert_eq!(actual_line_entry, line_entry, "{source:?}");
        let root = SyntaxNode::new_root(green);
        assert_eq!(root.to_string(), accepted, "{source:?}");
        assert_eq!(actual_remainder, remainder, "{source:?}");
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            missing,
            "{source:?}",
        );
    }
}

#[test]
fn normalized_type_declaration_streams_header_and_trailing_derives() {
    let fence = active_fence();
    let accepted = "> > type T derives Role via Header = F derives Trait, Other via Tail";
    let source = format!("{accepted}\r\n> > ```\r\nouter");
    let (green, exit, remainder) =
        run_statement_normalized(&source, 4225, LineEntry::PhysicalStart, Some(&fence));
    let NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart) = exit
    else {
        panic!("both Derives episodes must stream through the Type owner")
    };
    assert!(boundary.payload_view().is_boundary());
    let root = SyntaxNode::new_root(green);
    assert_eq!(root.to_string(), accepted);
    assert_eq!(remainder, "> > ```\r\nouter");
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::DerivesClause)
            .count(),
        2
    );
    assert!(
        root.descendants()
            .all(|node| !matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Missing))
    );
}

#[test]
fn normalized_statement_visibility_admission_respects_the_fence() {
    let fence = active_fence();
    for (source, family) in [
        ("> > my role A", SyntaxKind::RoleDeclaration),
        ("> > my impl A", SyntaxKind::ImplDeclaration),
    ] {
        let (green, _, remainder) =
            run_statement_normalized(source, 4300, LineEntry::PhysicalStart, Some(&fence));
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        assert!(
            SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == family),
            "{source:?}",
        );
    }

    let source = "> > my\n> > ```\nouter";
    let (green, exit, remainder) =
        run_statement_normalized(source, 4400, LineEntry::PhysicalStart, Some(&fence));
    let NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart) = exit
    else {
        panic!("the selected Binding owner must reach the boundary after visibility")
    };
    let root = SyntaxNode::new_root(green);
    assert!(boundary.payload_view().is_boundary());
    assert_eq!(root.to_string(), "> > my");
    assert_eq!(remainder, "> > ```\nouter");
    let (boundary_leading, _) = emit_terminal_leading_text(boundary);
    assert_eq!(boundary_leading, "\n");
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
}

#[test]
fn normalized_struct_streams_visibility_and_all_body_forms() {
    let fence = active_fence();
    let origin = 4455;
    for (accepted, line_break, fields, quote_prefixes, errors, missing) in [
        ("> > struct Empty;", "\r\n", 0, 1, 0, 0),
        (
            "> > my\r\n> >   struct\r\n> >   Point{x: F,\r\n> >     y: Y}",
            "\r\n",
            2,
            4,
            0,
            0,
        ),
        ("> > struct Pair(F, G)", "\n", 2, 1, 0, 0),
        ("> > struct Row:\n> >   x: F\n> >   y: Y", "\n", 2, 3, 0, 0),
    ] {
        let source = format!("{accepted}{line_break}> > ```{line_break}outer");
        let (green, exit, remainder) =
            run_statement_normalized(&source, origin, LineEntry::PhysicalStart, Some(&fence));
        let NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart) = exit
        else {
            panic!("Struct must stream to its exact fence: {accepted:?}")
        };
        let root = SyntaxNode::new_root(green);
        assert_eq!(root.to_string(), accepted, "{accepted:?}");
        assert_eq!(
            remainder,
            format!("> > ```{line_break}outer"),
            "{accepted:?}",
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::StructField)
                .count(),
            fields,
            "{accepted:?}",
        );
        assert_eq!(
            root.descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .filter(|token| token.kind() == SyntaxKind::YmQuotePrefix)
                .count(),
            quote_prefixes,
            "{accepted:?}",
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            errors,
            "{accepted:?}",
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            missing,
            "{accepted:?}",
        );
        let (leading, pending) = emit_terminal_leading_text(boundary);
        assert_eq!(leading, line_break, "{accepted:?}");
        assert_eq!(
            pending.coordinate(),
            origin + accepted.len() + line_break.len(),
            "{accepted:?}",
        );
    }
}

#[test]
fn normalized_struct_phase_recovery_stops_before_boundaries() {
    let fence = active_fence();
    let origin = 4470;
    for (accepted, missing, errors) in [
        ("> > struct", 1, 0),
        ("> > struct Name", 1, 0),
        ("> > struct @", 0, 1),
        ("> > struct Name @", 0, 1),
        ("> > struct Name{x:", 3, 0),
        ("> > struct Name(F", 2, 0),
    ] {
        let source = format!("{accepted}\n> > ```\nouter");
        let (green, exit, remainder) =
            run_statement_normalized(&source, origin, LineEntry::PhysicalStart, Some(&fence));
        let NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart) = exit
        else {
            panic!("Struct recovery must preserve the exact fence: {accepted:?}")
        };
        let root = SyntaxNode::new_root(green);
        assert_eq!(root.to_string(), accepted, "{accepted:?}");
        assert_eq!(remainder, "> > ```\nouter", "{accepted:?}");
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            missing,
            "{accepted:?}",
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            errors,
            "{accepted:?}",
        );
        let (leading, pending) = emit_terminal_leading_text(boundary);
        assert_eq!(leading, "\n", "{accepted:?}");
        assert_eq!(
            pending.coordinate(),
            origin + accepted.len() + 1,
            "{accepted:?}"
        );
    }

    let source = "> > struct Name\r\n> ]\r\nouter";
    let (green, exit, remainder) =
        run_statement_normalized(source, origin, LineEntry::PhysicalStart, Some(&fence));
    let NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart) = exit
    else {
        panic!("Struct must preserve an outer transition")
    };
    assert_eq!(green.to_string(), "> > struct Name");
    assert_eq!(remainder, "> ]\r\nouter");
    assert_eq!(emit_terminal_leading_text(boundary).0, "\r\n");

    let source = "> > struct Name";
    let (green, exit, remainder) =
        run_statement_normalized(source, origin, LineEntry::PhysicalStart, Some(&fence));
    let NormalizedExit::Complete(Err(Either::Left(boundary)), actual_entry) = exit else {
        panic!("physical EOF must remain the Struct caller's boundary")
    };
    assert_eq!(actual_entry, LineEntry::InLine);
    assert!(boundary.payload_view().is_boundary());
    assert_eq!(emit_terminal_leading_text(boundary).0, "");
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
}

#[test]
fn normalized_struct_named_field_boundary_is_fence_aware() {
    let fence = active_fence();
    let origin = 4490;
    for (accepted, fields, types, missing) in [
        ("> > struct S{x: F y: Y}", 2, 2, 1),
        ("> > struct S{x: F Y}", 1, 2, 0),
    ] {
        let source = format!("{accepted}\n> > ```\nouter");
        let (green, exit, remainder) =
            run_statement_normalized(&source, origin, LineEntry::PhysicalStart, Some(&fence));
        assert!(matches!(
            exit,
            NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::PhysicalStart)
                if item.payload_view().is_boundary()
        ));
        let root = SyntaxNode::new_root(green);
        assert_eq!(root.to_string(), accepted, "{accepted:?}");
        assert_eq!(remainder, "> > ```\nouter", "{accepted:?}");
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::StructField)
                .count(),
            fields,
            "{accepted:?}",
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::TypeExpression)
                .count(),
            types,
            "{accepted:?}",
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            missing,
            "{accepted:?}",
        );
    }

    let accepted = "> > struct S{x: F y";
    let source = format!("{accepted}\n> ]\n: Y");
    let (green, exit, remainder) =
        run_statement_normalized(&source, origin, LineEntry::PhysicalStart, Some(&fence));
    let NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart) = exit
    else {
        panic!("the named-field observer must stop at the transition")
    };
    let root = SyntaxNode::new_root(green);
    assert_eq!(root.to_string(), accepted);
    assert_eq!(remainder, "> ]\n: Y");
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::StructField)
            .count(),
        2,
    );
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::TypeExpression)
            .count(),
        2,
    );
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        2,
    );
    assert_eq!(emit_terminal_leading_text(boundary).0, "\n");
}

#[test]
fn normalized_struct_preserves_type_openers_and_successor_frontiers() {
    let fence = active_fence();
    let source = "> > struct S :{A}";
    let (green, exit, remainder) =
        run_statement_normalized(source, 4510, LineEntry::PhysicalStart, Some(&fence));
    let NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::InLine) = exit else {
        panic!("the polymorphic variant Type opener must remain pending")
    };
    assert_eq!(green.to_string(), "> > struct S ");
    assert_eq!(
        item.payload_view().token_kind(),
        Some(TokenKind::PolymorphicVariantColon)
    );
    assert_eq!(remainder, "{A}");

    let source = "> > {struct S; type T = U";
    let operators = OperatorTable::empty();
    let (green, exit, remainder) = run_normalized(
        source,
        &operators,
        4520,
        LineEntry::PhysicalStart,
        Some(&fence),
    );
    let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::InLine)) = exit
    else {
        panic!("Struct completion must enter the following Type owner")
    };
    assert!(boundary.payload_view().is_boundary());
    let root = SyntaxNode::new_root(green);
    assert_eq!(root.to_string(), source);
    assert_eq!(remainder, "");
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::TypeDeclaration)
            .count(),
        1
    );
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        2
    );
}

#[test]
fn normalized_mod_streams_visibility_gaps_and_all_body_forms() {
    let fence = active_fence();
    let origin = 4460;
    for (accepted, line_break, quote_prefixes, blocks) in [
        ("> > mod Plain;", "\r\n", 1, (0, 0)),
        ("> > mod test;", "\n", 1, (0, 0)),
        (
            "> > our\r\n> >   mod\r\n> >   test\r\n> >   Suite\r\n> >   ;",
            "\r\n",
            5,
            (0, 0),
        ),
        ("> > mod Braced {x;}", "\n", 1, (1, 0)),
        ("> > mod Inline: x;", "\n", 1, (0, 0)),
        ("> > mod Indented:\n> >   x", "\n", 2, (0, 1)),
    ] {
        let source = format!("{accepted}{line_break}> > ```{line_break}outer");
        let (green, exit, remainder) =
            run_statement_normalized(&source, origin, LineEntry::PhysicalStart, Some(&fence));
        let NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart) = exit
        else {
            panic!("Mod must stream to the exact fence: {accepted:?}")
        };
        let root = SyntaxNode::new_root(green);
        assert_eq!(root.to_string(), accepted, "{accepted:?}");
        assert_eq!(
            remainder,
            format!("> > ```{line_break}outer"),
            "{accepted:?}",
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::ModDeclaration)
                .count(),
            1,
            "{accepted:?}",
        );
        assert_eq!(
            root.descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .filter(|token| token.kind() == SyntaxKind::YmQuotePrefix)
                .count(),
            quote_prefixes,
            "{accepted:?}",
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
                .count(),
            blocks.0,
            "{accepted:?}",
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::IndentedStatementBlock)
                .count(),
            blocks.1,
            "{accepted:?}",
        );
        assert!(
            root.descendants()
                .all(|node| !matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Missing)),
            "{accepted:?}",
        );
        let (leading, pending) = emit_terminal_leading_text(boundary);
        assert_eq!(leading, line_break, "{accepted:?}");
        assert_eq!(
            pending.coordinate(),
            origin + accepted.len() + line_break.len(),
            "{accepted:?}",
        );
    }
}

#[test]
fn normalized_mod_test_name_slot_hands_close_transition_and_eof_up() {
    let fence = active_fence();
    let origin = 4480;
    for (source, accepted, remainder, line_entry, terminal_leading) in [
        (
            "> > mod test\n> > ```\nouter",
            "> > mod test",
            "> > ```\nouter",
            LineEntry::PhysicalStart,
            "\n",
        ),
        (
            "> > mod test\r\n> ]\r\nouter",
            "> > mod test",
            "> ]\r\nouter",
            LineEntry::PhysicalStart,
            "\r\n",
        ),
        ("> > mod test", "> > mod test", "", LineEntry::InLine, ""),
    ] {
        let (green, exit, actual_remainder) =
            run_statement_normalized(source, origin, LineEntry::PhysicalStart, Some(&fence));
        let NormalizedExit::Complete(Err(Either::Left(boundary)), actual_entry) = exit else {
            panic!("the second Mod name slot must preserve its exact boundary: {source:?}")
        };
        let root = SyntaxNode::new_root(green);
        assert_eq!(actual_entry, line_entry, "{source:?}");
        assert_eq!(root.to_string(), accepted, "{source:?}");
        assert_eq!(actual_remainder, remainder, "{source:?}");
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
            "{source:?}",
        );
        let (leading, pending) = emit_terminal_leading_text(boundary);
        assert_eq!(leading, terminal_leading, "{source:?}");
        assert_eq!(
            pending.coordinate(),
            origin + accepted.len() + terminal_leading.len(),
            "{source:?}",
        );
    }
}

#[test]
fn normalized_mod_phase_recovery_stops_before_fence_boundaries() {
    let fence = active_fence();
    let origin = 4500;
    for (accepted, missing, errors) in [
        ("> > mod", 1, 0),
        ("> > mod Name", 1, 0),
        ("> > mod @", 0, 1),
        ("> > mod Name @", 0, 1),
        ("> > mod Name: @", 0, 1),
    ] {
        let source = format!("{accepted}\n> > ```\nouter");
        let (green, exit, remainder) =
            run_statement_normalized(&source, origin, LineEntry::PhysicalStart, Some(&fence));
        let NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart) = exit
        else {
            panic!("Mod recovery must stop before the fence: {accepted:?}")
        };
        let root = SyntaxNode::new_root(green);
        assert_eq!(root.to_string(), accepted, "{accepted:?}");
        assert_eq!(remainder, "> > ```\nouter", "{accepted:?}");
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            missing,
            "{accepted:?}",
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            errors,
            "{accepted:?}",
        );
        let (leading, pending) = emit_terminal_leading_text(boundary);
        assert_eq!(leading, "\n", "{accepted:?}");
        assert_eq!(
            pending.coordinate(),
            origin + accepted.len() + 1,
            "{accepted:?}"
        );
    }
}

#[test]
fn normalized_mod_owns_the_nested_type_statement() {
    let fence = active_fence();
    for source in ["> > mod Outer:\n> >   type T = U"] {
        let (green, exit, actual_remainder) =
            run_statement_normalized(source, 4520, LineEntry::PhysicalStart, Some(&fence));
        let NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::InLine) = exit else {
            panic!("Mod must enter its nested Type declaration: {source:?}")
        };
        assert!(boundary.payload_view().is_boundary(), "{source:?}");
        let root = SyntaxNode::new_root(green);
        assert_eq!(root.to_string(), source, "{source:?}");
        assert_eq!(actual_remainder, "", "{source:?}");
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::ModDeclaration)
                .count(),
            1,
            "{source:?}",
        );
        assert!(
            root.descendants()
                .all(|node| !matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Missing)),
            "{source:?}",
        );
    }
}

#[test]
fn normalized_binding_streams_inline_and_nested_deeper_bodies() {
    let fence = active_fence();
    for (accepted, bindings, indented_blocks, quote_prefixes) in [
        ("> > my x = value", 1, 0, 1),
        ("> > my\r\n> >   x = value", 1, 0, 2),
        ("> > my x =\n> >   my y = 1\n> >   y", 2, 1, 3),
    ] {
        let source = format!("{accepted}\n> > ```\nouter");
        let (green, exit, remainder) =
            run_statement_normalized(&source, 4475, LineEntry::PhysicalStart, Some(&fence));
        let NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart) = exit
        else {
            panic!("the Binding owner must stream to the exact fence: {accepted:?}")
        };
        let root = SyntaxNode::new_root(green);
        assert!(boundary.payload_view().is_boundary(), "{accepted:?}");
        assert_eq!(root.to_string(), accepted, "{accepted:?}");
        assert_eq!(remainder, "> > ```\nouter", "{accepted:?}");
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::BindingStatement)
                .count(),
            bindings,
            "{accepted:?}",
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::IndentedStatementBlock)
                .count(),
            indented_blocks,
            "{accepted:?}",
        );
        assert_eq!(
            root.descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .filter(|token| token.kind() == SyntaxKind::YmQuotePrefix)
                .count(),
            quote_prefixes,
            "{accepted:?}",
        );
        assert!(
            root.descendants()
                .all(|node| !matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Missing)),
            "{accepted:?}",
        );
    }
}

#[test]
fn normalized_binding_emits_quote_prefixes_across_pattern_equals_and_rhs() {
    let fence = active_fence();
    let accepted = "> > my\n> >   x\n> >   =\n> >   value";
    let source = format!("{accepted}\n> > ```\nouter");
    let (green, exit, remainder) =
        run_statement_normalized(&source, 4500, LineEntry::PhysicalStart, Some(&fence));
    assert!(matches!(
        exit,
        NormalizedExit::Complete(Err(Either::Left(_)), LineEntry::PhysicalStart)
    ));
    let root = SyntaxNode::new_root(green);
    assert_eq!(root.to_string(), accepted);
    assert_eq!(remainder, "> > ```\nouter");
    assert_eq!(
        root.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::YmQuotePrefix)
            .count(),
        4
    );
    assert_eq!(
        root.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::Equals)
            .count(),
        1
    );
    assert!(
        root.descendants()
            .all(|node| !matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Missing))
    );
}

#[test]
fn normalized_binding_preserves_equal_and_shallow_statement_handoffs() {
    let fence = active_fence();
    let source = "> > my x =\n> > y";
    let (green, exit, remainder) =
        run_statement_normalized(source, 4525, LineEntry::PhysicalStart, Some(&fence));
    let NormalizedExit::Complete(Err(Either::Left(mut item)), LineEntry::InLine) = exit else {
        panic!("the equal-indent successor must remain pending")
    };
    let root = SyntaxNode::new_root(green);
    assert_eq!(root.to_string(), "> > my x =");
    assert_eq!(item.payload_view().spelling(), Some("y"));
    assert_eq!(remainder, "");
    assert_eq!(
        emit_pending_leading_tokens(&mut item),
        [
            (SyntaxKind::Newline, "\n".to_owned()),
            (SyntaxKind::YmQuotePrefix, "> > ".to_owned()),
        ]
    );
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );

    let operators = OperatorTable::empty();
    let accepted = "> > f:\n> >   my x =";
    let source = format!("{accepted}\n> > y");
    let (green, exit, remainder) = run_normalized(
        &source,
        &operators,
        4550,
        LineEntry::PhysicalStart,
        Some(&fence),
    );
    let Some(NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::InLine)) = exit else {
        panic!("the shallow successor must remain pending")
    };
    let root = SyntaxNode::new_root(green);
    assert_eq!(root.to_string(), accepted);
    assert_eq!(item.payload_view().spelling(), Some("y"));
    assert_eq!(remainder, "");
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
}

#[test]
fn normalized_binding_preserves_semicolon_and_terminal_frontiers() {
    let fence = active_fence();
    let source = "> > my x = value; next";
    let (green, exit, remainder) =
        run_statement_normalized(source, 4575, LineEntry::PhysicalStart, Some(&fence));
    let NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::InLine) = exit else {
        panic!("the semicolon must remain pending")
    };
    assert_eq!(green.to_string(), "> > my x = value");
    assert_eq!(item.payload_view().token_kind(), Some(TokenKind::Semicolon));
    assert_eq!(remainder, " next");

    let accepted = "> > my x = value";
    for (suffix, expected_remainder) in [
        ("\n> > ```\nouter", "> > ```\nouter"),
        ("\n> ]\nouter", "> ]\nouter"),
    ] {
        let source = format!("{accepted}{suffix}");
        let (green, exit, remainder) =
            run_statement_normalized(&source, 4600, LineEntry::PhysicalStart, Some(&fence));
        assert!(matches!(
            exit,
            NormalizedExit::Complete(Err(Either::Left(_)), LineEntry::PhysicalStart)
        ));
        assert_eq!(green.to_string(), accepted);
        assert_eq!(remainder, expected_remainder);
    }

    let (green, exit, remainder) =
        run_statement_normalized(accepted, 4625, LineEntry::PhysicalStart, Some(&fence));
    assert!(matches!(
        exit,
        NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::InLine)
            if item.payload_view().is_boundary()
    ));
    assert_eq!(green.to_string(), accepted);
    assert_eq!(remainder, "");
}

#[test]
fn normalized_binding_retries_malformed_target_and_rhs_without_crossing_fence() {
    let fence = active_fence();
    for accepted in ["> > my @ x = value", "> > my x = @ value"] {
        let source = format!("{accepted}\n> > ```\nouter");
        let (green, exit, remainder) =
            run_statement_normalized(&source, 4650, LineEntry::PhysicalStart, Some(&fence));
        assert!(matches!(
            exit,
            NormalizedExit::Complete(Err(Either::Left(_)), LineEntry::PhysicalStart)
        ));
        let root = SyntaxNode::new_root(green);
        assert_eq!(root.to_string(), accepted, "{accepted:?}");
        assert_eq!(remainder, "> > ```\nouter", "{accepted:?}");
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            1,
            "{accepted:?}",
        );
        assert!(
            root.descendants()
                .all(|node| node.kind() != SyntaxKind::Missing),
            "{accepted:?}",
        );
    }
}

#[test]
fn normalized_for_streams_labels_and_all_body_forms() {
    let fence = active_fence();
    for (accepted, labels, for_statements, blocks, prefixes, line_break) in [
        ("> > for 'outer x in xs: x", 1, 1, 0, 1, "\n"),
        ("> > for 'x in xs: x", 0, 1, 0, 1, "\n"),
        ("> > for x in xs:\n> >   for y in ys: y", 0, 2, 1, 2, "\n"),
        ("> > for\n> >   x\n> >   in\n> >   xs: x", 0, 1, 0, 4, "\n"),
        ("> > for 'outer x in xs:\r\n> >   x", 1, 1, 1, 2, "\r\n"),
    ] {
        let source = format!("{accepted}{line_break}> > ```{line_break}outer");
        let (green, exit, remainder) =
            run_statement_normalized(&source, 4675, LineEntry::PhysicalStart, Some(&fence));
        let NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart) = exit
        else {
            panic!("the For owner must stream to the exact fence: {accepted:?}")
        };
        let root = SyntaxNode::new_root(green);
        assert!(boundary.payload_view().is_boundary(), "{accepted:?}");
        assert_eq!(root.to_string(), accepted, "{accepted:?}");
        assert_eq!(
            remainder,
            format!("> > ```{line_break}outer"),
            "{accepted:?}"
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::ForLabel)
                .count(),
            labels,
            "{accepted:?}",
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::ForStatement)
                .count(),
            for_statements,
            "{accepted:?}",
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::IndentedStatementBlock)
                .count(),
            blocks,
            "{accepted:?}",
        );
        assert_eq!(
            root.descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .filter(|token| token.kind() == SyntaxKind::YmQuotePrefix)
                .count(),
            prefixes,
            "{accepted:?}",
        );
        assert!(
            root.descendants()
                .all(|node| !matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Missing)),
            "{accepted:?}",
        );
        if labels == 1 {
            let label = root
                .descendants()
                .find(|node| node.kind() == SyntaxKind::ForLabel)
                .expect("accepted label");
            assert_eq!(label.to_string(), "'outer");
        }
        let (leading, pending) = emit_terminal_leading_text(boundary);
        assert_eq!(leading, line_break, "{accepted:?}");
        assert_eq!(
            pending.coordinate(),
            4675 + accepted.len() + line_break.len(),
            "{accepted:?}"
        );
    }
}

#[test]
fn normalized_for_label_probe_rejects_terminal_candidates_without_crossing_them() {
    let fence = active_fence();
    let origin = 4750;
    for (source, accepted, remainder, line_entry, terminal_leading) in [
        (
            "> > for 'x\n> > ```\nouter",
            "> > for 'x",
            "> > ```\nouter",
            LineEntry::PhysicalStart,
            "\n",
        ),
        (
            "> > for 'x\r\n> ]\r\nouter",
            "> > for 'x",
            "> ]\r\nouter",
            LineEntry::PhysicalStart,
            "\r\n",
        ),
        ("> > for 'x", "> > for 'x", "", LineEntry::InLine, ""),
    ] {
        let (green, exit, actual_remainder) =
            run_statement_normalized(source, origin, LineEntry::PhysicalStart, Some(&fence));
        let NormalizedExit::Complete(Err(Either::Left(boundary)), actual_line_entry) = exit else {
            panic!("the rejected label candidate must preserve its terminal boundary")
        };
        let root = SyntaxNode::new_root(green);
        assert_eq!(actual_line_entry, line_entry, "{source:?}");
        assert_eq!(root.to_string(), accepted, "{source:?}");
        assert_eq!(actual_remainder, remainder, "{source:?}");
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::ForLabel)
                .count(),
            0,
            "{source:?}",
        );
        let (leading, pending) = emit_terminal_leading_text(boundary);
        assert_eq!(leading, terminal_leading, "{source:?}");
        assert_eq!(
            pending.coordinate(),
            origin + accepted.len() + terminal_leading.len(),
            "{source:?}",
        );
    }

    let source = "> > for\n> > 'x in xs: x";
    let (green, exit, remainder) =
        run_statement_normalized(source, origin, LineEntry::PhysicalStart, Some(&fence));
    let NormalizedExit::Complete(Err(Either::Left(mut item)), LineEntry::InLine) = exit else {
        panic!("an equal-indent label candidate must remain the pending Pattern item")
    };
    assert_eq!(green.to_string(), "> > for");
    assert_eq!(item.payload_view().spelling(), Some("'x"));
    assert_eq!(remainder, " in xs: x");
    assert_eq!(
        emit_pending_leading_tokens(&mut item),
        [
            (SyntaxKind::Newline, "\n".to_owned()),
            (SyntaxKind::YmQuotePrefix, "> > ".to_owned()),
        ]
    );
}

#[test]
fn normalized_for_phase_boundaries_add_only_the_owned_missing_slot() {
    let fence = active_fence();
    let origin = 4850;
    for (accepted, iterables) in [
        ("> > for", 0),
        ("> > for x", 0),
        ("> > for x in", 1),
        ("> > for x in xs", 1),
    ] {
        let source = format!("{accepted}\r\n> > ```\r\nouter");
        let (green, exit, remainder) =
            run_statement_normalized(&source, origin, LineEntry::PhysicalStart, Some(&fence));
        let NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart) = exit
        else {
            panic!("the For phase must return its exact boundary: {accepted:?}")
        };
        let root = SyntaxNode::new_root(green);
        assert_eq!(root.to_string(), accepted, "{accepted:?}");
        assert_eq!(remainder, "> > ```\r\nouter", "{accepted:?}");
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
            "{accepted:?}",
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::ForIterable)
                .count(),
            iterables,
            "{accepted:?}",
        );
        let (leading, pending) = emit_terminal_leading_text(boundary);
        assert_eq!(leading, "\r\n", "{accepted:?}");
        assert_eq!(
            pending.coordinate(),
            origin + accepted.len() + 2,
            "{accepted:?}"
        );
    }

    let source = "> > for x in xs: body; sibling";
    let (green, exit, remainder) =
        run_statement_normalized(source, origin, LineEntry::PhysicalStart, Some(&fence));
    let NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::InLine) = exit else {
        panic!("the inline For body must leave its semicolon pending")
    };
    assert_eq!(token_kind(&item), Some(TokenKind::Semicolon));
    assert_eq!(green.to_string(), "> > for x in xs: body");
    assert_eq!(remainder, " sibling");
}

#[test]
fn normalized_for_recovery_and_nested_declaration_stop_at_their_exact_frontiers() {
    let fence = active_fence();
    let origin = 4950;
    for accepted in ["> > for @ x in xs @", "> > for x in @ xs @"] {
        let source = format!("{accepted}\n> ]\nouter");
        let (green, exit, remainder) =
            run_statement_normalized(&source, origin, LineEntry::PhysicalStart, Some(&fence));
        let NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart) = exit
        else {
            panic!("malformed For recovery must stop at the transition: {accepted:?}")
        };
        let root = SyntaxNode::new_root(green);
        assert_eq!(root.to_string(), accepted, "{accepted:?}");
        assert_eq!(remainder, "> ]\nouter", "{accepted:?}");
        assert!(
            root.descendants()
                .any(|node| node.kind() == SyntaxKind::Error),
            "{accepted:?}",
        );
        let (leading, _) = emit_terminal_leading_text(boundary);
        assert_eq!(leading, "\n", "{accepted:?}");
    }

    let source = "> > for x in xs:\n> >   type T = U";
    let (green, exit, remainder) =
        run_statement_normalized(source, origin, LineEntry::PhysicalStart, Some(&fence));
    let NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::InLine) = exit else {
        panic!("the For owner must enter its nested Type statement")
    };
    assert!(boundary.payload_view().is_boundary());
    let root = SyntaxNode::new_root(green);
    assert_eq!(root.to_string(), source);
    assert_eq!(remainder, "");
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::TypeDeclaration)
            .count(),
        1
    );
}

#[test]
fn normalized_for_braced_body_owns_only_its_missing_close_at_a_fence() {
    let fence = active_fence();
    let origin = 5050;
    let accepted = "> > for x in xs { y }";
    let source = format!("{accepted}\n> > ```\nouter");
    let (green, exit, remainder) =
        run_statement_normalized(&source, origin, LineEntry::PhysicalStart, Some(&fence));
    assert!(matches!(
        exit,
        NormalizedExit::Complete(Ok(()), LineEntry::InLine)
    ));
    assert_eq!(green.to_string(), accepted);
    assert_eq!(remainder, "\n> > ```\nouter");

    let accepted = "> > for x in xs { y";
    let source = format!("{accepted}\n> > ```\nouter");
    let (green, exit, remainder) =
        run_statement_normalized(&source, origin, LineEntry::PhysicalStart, Some(&fence));
    let NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart) = exit
    else {
        panic!("the unclosed For brace must hand the exact boundary upward")
    };
    let root = SyntaxNode::new_root(green);
    assert_eq!(root.to_string(), accepted);
    assert_eq!(remainder, "> > ```\nouter");
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1,
    );
    let (leading, pending) = emit_terminal_leading_text(boundary);
    assert_eq!(leading, "\n");
    assert_eq!(pending.coordinate(), origin + accepted.len() + 1);
}

#[test]
fn normalized_use_streams_bare_visibility_and_nested_statement_sites() {
    let fence = active_fence();
    let origin = 5125;
    for (accepted, line_break) in [
        ("> > use std::data", "\n"),
        ("> > my use realm/tools::format", "\r\n"),
    ] {
        let source = format!("{accepted}{line_break}> > ```{line_break}outer");
        let (green, exit, remainder) =
            run_statement_normalized(&source, origin, LineEntry::PhysicalStart, Some(&fence));
        let NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart) = exit
        else {
            panic!("the Use owner must stream to the exact fence: {accepted:?}")
        };
        let root = SyntaxNode::new_root(green);
        assert_eq!(root.to_string(), accepted, "{accepted:?}");
        assert_eq!(
            remainder,
            format!("> > ```{line_break}outer"),
            "{accepted:?}"
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::UseDeclaration)
                .count(),
            1,
            "{accepted:?}",
        );
        assert_eq!(
            root.descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .filter(|token| token.kind() == SyntaxKind::YmQuotePrefix)
                .count(),
            1,
            "{accepted:?}",
        );
        assert!(
            root.descendants()
                .all(|node| !matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Missing)),
            "{accepted:?}",
        );
        let (leading, pending) = emit_terminal_leading_text(boundary);
        assert_eq!(leading, line_break, "{accepted:?}");
        assert_eq!(
            pending.coordinate(),
            origin + accepted.len() + line_break.len(),
            "{accepted:?}",
        );
    }

    let source = "case x:\n  n ->\n    use foo";
    let operators = OperatorTable::empty();
    let (green, exit, remainder) = run_normalized(
        source,
        &operators,
        origin,
        LineEntry::PhysicalStart,
        Some(&plain_fence()),
    );
    assert!(matches!(
        exit,
        Some(NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::InLine))
            if item.payload_view().is_boundary()
    ));
    let root = SyntaxNode::new_root(green);
    assert_eq!(root.to_string(), source);
    assert_eq!(remainder, "");
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::UseDeclaration)
            .count(),
        1,
    );

    let accepted = "> > my use = value";
    let source = format!("{accepted}\r\n> > ```\r\nouter");
    let (green, exit, remainder) =
        run_statement_normalized(&source, origin, LineEntry::PhysicalStart, Some(&fence));
    let NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart) = exit
    else {
        panic!("the rejected Use admission must remain a Binding")
    };
    let root = SyntaxNode::new_root(green);
    assert_eq!(root.to_string(), accepted);
    assert_eq!(remainder, "> > ```\r\nouter");
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::BindingStatement)
            .count(),
        1,
    );
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::UseDeclaration)
            .count(),
        0,
    );
    let (leading, pending) = emit_terminal_leading_text(boundary);
    assert_eq!(leading, "\r\n");
    assert_eq!(pending.coordinate(), origin + accepted.len() + 2);
}

#[test]
fn normalized_use_streams_recursive_groups_exclusions_and_qualifiers() {
    let fence = active_fence();
    let origin = 5225;
    let accepted = "> > use std::* as all without {foo,\n> >   (*), nested::{x}} v1-alpha+build.2 with program::ui";
    for (line_break, terminal) in [("\n", "> > ```\nouter"), ("\r\n", "> ]\r\nouter")] {
        let source = format!("{accepted}{line_break}{terminal}");
        let (green, exit, remainder) =
            run_statement_normalized(&source, origin, LineEntry::PhysicalStart, Some(&fence));
        let NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart) = exit
        else {
            panic!("recursive Use tree must stop at its exact boundary: {terminal:?}")
        };
        let root = SyntaxNode::new_root(green);
        assert_eq!(root.to_string(), accepted, "{terminal:?}");
        assert_eq!(remainder, terminal, "{terminal:?}");
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::UseExclusionGroup)
                .count(),
            1,
            "{terminal:?}",
        );
        assert!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::UseGroup)
                .all(|group| group.first_token().is_some_and(|token| {
                    matches!(token.kind(), SyntaxKind::LBrace | SyntaxKind::LParen)
                })),
            "{terminal:?}",
        );
        assert!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::UseExclusionGroup)
                .all(|group| group.first_token().is_some_and(|token| {
                    matches!(token.kind(), SyntaxKind::LBrace | SyntaxKind::LParen)
                })),
            "{terminal:?}",
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::UseAlias)
                .count(),
            1,
            "{terminal:?}",
        );
        assert!(
            root.descendants()
                .all(|node| !matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Missing)),
            "{terminal:?}",
        );
        let (leading, pending) = emit_terminal_leading_text(boundary);
        assert_eq!(leading, line_break, "{terminal:?}");
        assert_eq!(
            pending.coordinate(),
            origin + accepted.len() + line_break.len(),
            "{terminal:?}",
        );
    }
}

#[test]
fn normalized_use_phase_recovery_hands_exact_boundaries_up() {
    let fence = active_fence();
    let origin = 5350;
    for (source, accepted, remainder, line_entry, missing, errors, leading) in [
        (
            "> > use\n> > ```\nouter",
            "> > use",
            "> > ```\nouter",
            LineEntry::PhysicalStart,
            1,
            0,
            "\n",
        ),
        (
            "> > use path::\r\n> ]\r\nouter",
            "> > use path::",
            "> ]\r\nouter",
            LineEntry::PhysicalStart,
            1,
            0,
            "\r\n",
        ),
        (
            "> > use {@ child",
            "> > use {@ child",
            "",
            LineEntry::InLine,
            1,
            1,
            "",
        ),
        (
            "> > use mod ",
            "> > use mod",
            "",
            LineEntry::InLine,
            1,
            0,
            " ",
        ),
        (
            "> > use x::* without ",
            "> > use x::* without",
            "",
            LineEntry::InLine,
            1,
            0,
            " ",
        ),
        (
            "> > use x as ",
            "> > use x as",
            "",
            LineEntry::InLine,
            1,
            0,
            " ",
        ),
        (
            "> > use x with ",
            "> > use x with",
            "",
            LineEntry::InLine,
            1,
            0,
            " ",
        ),
    ] {
        let (green, exit, actual_remainder) =
            run_statement_normalized(source, origin, LineEntry::PhysicalStart, Some(&fence));
        let NormalizedExit::Complete(Err(Either::Left(boundary)), actual_line_entry) = exit else {
            panic!("the required Use slot must return its exact boundary: {source:?}")
        };
        let root = SyntaxNode::new_root(green);
        assert_eq!(actual_line_entry, line_entry, "{source:?}");
        assert_eq!(root.to_string(), accepted, "{source:?}");
        assert_eq!(actual_remainder, remainder, "{source:?}");
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            missing,
            "{source:?}",
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            errors,
            "{source:?}",
        );
        let (actual_leading, pending) = emit_terminal_leading_text(boundary);
        assert_eq!(actual_leading, leading, "{source:?}");
        assert_eq!(
            pending.coordinate(),
            origin + accepted.len() + leading.len(),
            "{source:?}",
        );
    }
}

#[test]
fn normalized_use_path_operator_probe_is_strict_and_transactional() {
    let fence = active_fence();
    let origin = 5425;
    for (accepted, operator_names, errors) in [
        ("> > use a::(", 0, 1),
        ("> > use a::(foo", 0, 1),
        ("> > use a::(+)", 1, 0),
    ] {
        let source = format!("{accepted}\n> > ```\nouter");
        let (green, exit, remainder) =
            run_statement_normalized(&source, origin, LineEntry::PhysicalStart, Some(&fence));
        let NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart) = exit
        else {
            panic!("the strict operator probe must preserve the fence: {accepted:?}")
        };
        let root = SyntaxNode::new_root(green);
        assert_eq!(root.to_string(), accepted, "{accepted:?}");
        assert_eq!(remainder, "> > ```\nouter", "{accepted:?}");
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::OperatorName)
                .count(),
            operator_names,
            "{accepted:?}",
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            errors,
            "{accepted:?}",
        );
        let (leading, pending) = emit_terminal_leading_text(boundary);
        assert_eq!(leading, "\n", "{accepted:?}");
        assert_eq!(
            pending.coordinate(),
            origin + accepted.len() + 1,
            "{accepted:?}",
        );
    }

    let accepted = "> > use x::* without (foo, bar)";
    let source = format!("{accepted}\n> > ```\nouter");
    let (green, exit, _) =
        run_statement_normalized(&source, origin, LineEntry::PhysicalStart, Some(&fence));
    assert!(matches!(
        exit,
        NormalizedExit::Complete(Err(Either::Left(_)), LineEntry::PhysicalStart)
    ));
    let root = SyntaxNode::new_root(green);
    let group = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::UseExclusionGroup)
        .expect("parenthesized exclusion group");
    assert_eq!(
        group.first_token().map(|token| token.kind()),
        Some(SyntaxKind::LParen)
    );
}

#[test]
fn normalized_use_group_missing_close_hands_equal_indent_declarations_up() {
    let fence = plain_fence();
    for (source, spelling, remainder) in [
        ("use {a\nuse b", "use", " b"),
        ("use {a\ntype T = A", "type", " T = A"),
    ] {
        let (green, exit, actual_remainder) =
            run_statement_normalized(source, 5475, LineEntry::PhysicalStart, Some(&fence));
        let NormalizedExit::Complete(Err(Either::Left(mut item)), LineEntry::InLine) = exit else {
            panic!("the unclosed Use group must preserve its successor: {source:?}")
        };
        let root = SyntaxNode::new_root(green);
        assert_eq!(root.to_string(), "use {a", "{source:?}");
        assert_eq!(item.payload_view().spelling(), Some(spelling), "{source:?}");
        assert_eq!(actual_remainder, remainder, "{source:?}");
        assert_eq!(emit_pending_leading_text(&mut item), "\n", "{source:?}");
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
            "{source:?}",
        );
    }
}

#[test]
fn normalized_use_preserves_final_statement_successors() {
    let fence = active_fence();
    let source = "> > use path; sibling";
    let (green, exit, remainder) =
        run_statement_normalized(source, 5550, LineEntry::PhysicalStart, Some(&fence));
    let NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::InLine) = exit else {
        panic!("the Use separator must remain pending")
    };
    assert_eq!(green.to_string(), "> > use path");
    assert_eq!(token_kind(&item), Some(TokenKind::Semicolon));
    assert_eq!(remainder, " sibling");

    for (source, whitespace) in [
        ("> > use path\n> > sibling", ""),
        ("> > use path\n> >   sibling", "  "),
    ] {
        let (green, exit, remainder) =
            run_statement_normalized(source, 5575, LineEntry::PhysicalStart, Some(&fence));
        let NormalizedExit::Complete(Err(Either::Left(mut item)), LineEntry::InLine) = exit else {
            panic!("the newline successor must remain pending: {source:?}")
        };
        assert_eq!(green.to_string(), "> > use path", "{source:?}");
        assert_eq!(
            item.payload_view().spelling(),
            Some("sibling"),
            "{source:?}"
        );
        assert_eq!(remainder, "", "{source:?}");
        let mut expected = vec![
            (SyntaxKind::Newline, "\n".to_owned()),
            (SyntaxKind::YmQuotePrefix, "> > ".to_owned()),
        ];
        if !whitespace.is_empty() {
            expected.push((SyntaxKind::Whitespace, whitespace.to_owned()));
        }
        assert_eq!(
            emit_pending_leading_tokens(&mut item),
            expected,
            "{source:?}"
        );
    }
}

#[test]
fn normalized_type_statement_streams_through_existing_callers() {
    let plain = plain_fence();
    for (source, fence) in [("x:\n  type T = U", &plain)] {
        let operators = OperatorTable::empty();
        let (green, exit, remainder) = run_normalized(
            source,
            &operators,
            4500,
            LineEntry::PhysicalStart,
            Some(fence),
        );
        let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::InLine)) = exit
        else {
            panic!("the normalized caller must enter its Type child: {source:?}")
        };
        assert!(boundary.payload_view().is_boundary(), "{source:?}");
        let root = SyntaxNode::new_root(green);
        assert_eq!(root.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        assert!(
            root.descendants()
                .all(|node| !matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Missing)),
            "{source:?}",
        );
    }
}

#[test]
fn normalized_statement_hands_close_transition_and_eof_boundaries_up() {
    let fence = active_fence();
    for (source, accepted, remainder, line_entry) in [
        (
            "> > x\n> > ```\nouter",
            "> > x",
            "> > ```\nouter",
            LineEntry::PhysicalStart,
        ),
        (
            "> > x\n> ]\nouter",
            "> > x",
            "> ]\nouter",
            LineEntry::PhysicalStart,
        ),
        ("> > x", "> > x", "", LineEntry::InLine),
    ] {
        let (green, exit, actual_remainder) =
            run_statement_normalized(source, 4700, LineEntry::PhysicalStart, Some(&fence));
        let NormalizedExit::Complete(Err(Either::Left(boundary)), actual_line_entry) = exit else {
            panic!("a complete statement must return its exact outer boundary: {source:?}")
        };
        assert!(boundary.payload_view().is_boundary(), "{source:?}");
        assert_eq!(actual_line_entry, line_entry, "{source:?}");
        assert_eq!(green.to_string(), accepted, "{source:?}");
        assert_eq!(actual_remainder, remainder, "{source:?}");
    }

    let source = "> > ```\nouter";
    let (green, exit, remainder) =
        run_statement_normalized(source, 4800, LineEntry::PhysicalStart, Some(&fence));
    let NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart) = exit
    else {
        panic!("a boundary before the first statement must remain pending")
    };
    assert!(boundary.payload_view().is_boundary());
    assert_eq!(green.to_string(), "");
    assert_eq!(remainder, source);
}

#[test]
fn normalized_braced_explicit_separator_enters_the_next_type_statement() {
    let fence = active_fence();

    let source = "> > { x; type T = U";
    let operators = OperatorTable::empty();
    let (green, exit, remainder) = run_normalized(
        source,
        &operators,
        4850,
        LineEntry::PhysicalStart,
        Some(&fence),
    );
    let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::InLine)) = exit
    else {
        panic!("the statement after `;` must enter its Type owner")
    };
    assert!(boundary.payload_view().is_boundary());
    let root = SyntaxNode::new_root(green);
    assert_eq!(root.to_string(), source);
    assert_eq!(remainder, "");
    assert!(
        root.descendants()
            .all(|node| node.kind() != SyntaxKind::Error)
    );
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );

    let source = "> > { x;\n> > ```\nouter";
    let (green, exit, remainder) = run_normalized(
        source,
        &operators,
        4900,
        LineEntry::PhysicalStart,
        Some(&fence),
    );
    let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
        exit
    else {
        panic!("the boundary after `;` must remain pending")
    };
    let root = SyntaxNode::new_root(green);
    assert!(boundary.payload_view().is_boundary());
    assert_eq!(root.to_string(), "> > { x;");
    assert_eq!(remainder, "> > ```\nouter");
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
    assert!(
        root.descendants()
            .all(|node| node.kind() != SyntaxKind::Error)
    );
}

#[test]
fn normalized_braced_initial_boundary_keeps_boundary_leading_pending() {
    let fence = active_fence();
    let operators = OperatorTable::empty();
    for (source, remainder) in [
        ("> > {\n> > ```\nouter", "> > ```\nouter"),
        ("> > {\n> ]\nouter", "> ]\nouter"),
    ] {
        let (green, exit, actual_remainder) = run_normalized(
            source,
            &operators,
            4875,
            LineEntry::PhysicalStart,
            Some(&fence),
        );
        let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
            exit
        else {
            panic!("an initial braced boundary must be handed upward: {source:?}")
        };
        assert!(boundary.payload_view().is_boundary(), "{source:?}");
        let (boundary_leading, _) = emit_terminal_leading_text(boundary);
        let root = SyntaxNode::new_root(green);
        assert_eq!(root.to_string(), "> > {", "{source:?}");
        assert_eq!(actual_remainder, remainder, "{source:?}");
        assert_eq!(boundary_leading, "\n", "{source:?}");
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
            "{source:?}",
        );
        assert!(
            root.descendants()
                .all(|node| node.kind() != SyntaxKind::Error),
            "{source:?}",
        );
    }
}

#[test]
fn normalized_colon_and_with_stream_indented_statement_bodies() {
    let operators = OperatorTable::empty();
    let fence = active_fence();
    for accepted in ["> > x:\n> >   y", "> > x with:\n> >   y"] {
        let source = format!("{accepted}\n> > ```\nouter");
        let (green, exit, remainder) = run_normalized(
            &source,
            &operators,
            4900,
            LineEntry::PhysicalStart,
            Some(&fence),
        );
        let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
            exit
        else {
            panic!("indented tail body must stream to the exact fence: {accepted:?}")
        };
        let root = SyntaxNode::new_root(green);
        assert!(boundary.payload_view().is_boundary(), "{accepted:?}");
        assert_eq!(root.to_string(), accepted, "{accepted:?}");
        assert_eq!(remainder, "> > ```\nouter", "{accepted:?}");
        assert!(
            root.descendants()
                .any(|node| node.kind() == SyntaxKind::IndentedStatementBlock),
            "{accepted:?}",
        );
    }
}

#[test]
fn normalized_pratt_hands_a_fence_boundary_up_without_emitting_it() {
    let operators = OperatorTable::empty();
    let fence = active_fence();
    let source = "> > x\n> > ```\nouter";
    let (green, exit, remainder) = run_normalized(
        source,
        &operators,
        500,
        LineEntry::PhysicalStart,
        Some(&fence),
    );
    let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
        exit
    else {
        panic!("the normalized tail must return the exact boundary Item")
    };

    assert_eq!(remainder, "> > ```\nouter");
    assert!(boundary.payload_view().is_boundary());
    assert_eq!(
        syntax_tokens(green),
        [
            (SyntaxKind::YmQuotePrefix, "> > ".to_owned()),
            (SyntaxKind::Identifier, "x".to_owned()),
        ]
    );
    assert!(boundary.leading_view().has_ordinary_newline());
    assert_eq!(boundary.leading_view().indentation_after_newline(), Some(0));
}

#[test]
fn normalized_pratt_keeps_infix_rhs_inside_the_current_cell() {
    let operators = OperatorTable::from_declarations([OperatorDeclaration::new(
        "+",
        OperatorFixities::new().with_infix(BindingPower::scalar(40), BindingPower::scalar(40)),
    )])
    .expect("one infix declaration");
    let fence = active_fence();
    let source = "> > x + y\n> > ```\nouter";
    let (green, exit, remainder) = run_normalized(
        source,
        &operators,
        700,
        LineEntry::PhysicalStart,
        Some(&fence),
    );

    assert!(matches!(
        exit,
        Some(NormalizedExit::Complete(
            Err(Either::Left(_)),
            LineEntry::PhysicalStart
        ))
    ));
    assert_eq!(remainder, "> > ```\nouter");
    assert_eq!(
        syntax_tokens(green),
        [
            (SyntaxKind::YmQuotePrefix, "> > ".to_owned()),
            (SyntaxKind::Identifier, "x".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::Operator, "+".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::Identifier, "y".to_owned()),
        ]
    );
}

#[test]
fn normalized_infix_rhs_enters_braces_directly_and_after_retry() {
    let operators = OperatorTable::from_declarations([OperatorDeclaration::new(
        "+",
        OperatorFixities::new().with_infix(BindingPower::scalar(40), BindingPower::scalar(40)),
    )])
    .expect("one infix declaration");
    let fence = active_fence();
    for (accepted, expected_errors) in [("> > x + { y }", 0), ("> > x + % { y }", 1)] {
        let source = format!("{accepted}\n> > ```\nouter");
        let (green, exit, remainder) = run_normalized(
            &source,
            &operators,
            750,
            LineEntry::PhysicalStart,
            Some(&fence),
        );
        let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
            exit
        else {
            panic!("the required RHS must enter its braced NUD: {accepted:?}")
        };
        let root = SyntaxNode::new_root(green);
        assert!(boundary.payload_view().is_boundary(), "{accepted:?}");
        assert_eq!(root.to_string(), accepted, "{accepted:?}");
        assert_eq!(remainder, "> > ```\nouter", "{accepted:?}");
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
                .count(),
            1,
            "{accepted:?}",
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            expected_errors,
            "{accepted:?}",
        );
    }
}

#[test]
fn normalized_case_like_streams_case_and_catch_to_the_fence_boundary() {
    let operators = OperatorTable::empty();
    let fence = active_fence();
    for (accepted, kinds) in [
        (
            "> > case x: n if guard -> yes, _ -> no",
            [SyntaxKind::CaseExpression, SyntaxKind::CaseArm],
        ),
        (
            "> > catch action { err, handler -> recover }",
            [SyntaxKind::CatchExpression, SyntaxKind::CatchArm],
        ),
    ] {
        let source = format!("{accepted}\n> > ```\nouter");
        let (green, exit, remainder) = run_normalized(
            &source,
            &operators,
            100,
            LineEntry::PhysicalStart,
            Some(&fence),
        );
        let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
            exit
        else {
            panic!("case-like owner must return the exact fence boundary")
        };
        let root = SyntaxNode::new_root(green);
        assert!(boundary.payload_view().is_boundary());
        assert_eq!(root.to_string(), accepted);
        assert_eq!(remainder, "> > ```\nouter");
        for kind in kinds {
            assert!(root.descendants().any(|node| node.kind() == kind));
        }
        assert!(
            root.descendants()
                .all(|node| !matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Missing))
        );
    }
}

#[test]
fn normalized_if_streams_elsif_else_and_crlf_to_the_fence_boundary() {
    let operators = OperatorTable::empty();
    let fence = active_fence();
    let accepted = "> > if x: yes\r\n> > elsif y: maybe\r\n> > else no";
    let source = format!("{accepted}\r\n> > ```\r\nouter");
    let (green, exit, remainder) = run_normalized(
        &source,
        &operators,
        200,
        LineEntry::PhysicalStart,
        Some(&fence),
    );
    let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
        exit
    else {
        panic!("if owner must return the exact fence boundary")
    };
    let root = SyntaxNode::new_root(green);
    assert!(boundary.payload_view().is_boundary());
    assert_eq!(root.to_string(), accepted);
    assert_eq!(remainder, "> > ```\r\nouter");
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::IfArm)
            .count(),
        2
    );
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::ElseArm)
            .count(),
        1
    );
    assert_eq!(
        root.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::YmQuotePrefix)
            .count(),
        3
    );
}

#[test]
fn normalized_case_if_complete_inline_forms_reach_transition_and_eof() {
    let operators = OperatorTable::empty();
    let fence = active_fence();
    for (source, accepted, remainder, line_entry) in [
        (
            "> > case x: n -> y\n> ]\nouter",
            "> > case x: n -> y",
            "> ]\nouter",
            LineEntry::PhysicalStart,
        ),
        ("> > if x: y", "> > if x: y", "", LineEntry::InLine),
    ] {
        let (green, exit, actual_remainder) = run_normalized(
            source,
            &operators,
            225,
            LineEntry::PhysicalStart,
            Some(&fence),
        );
        let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), actual_line_entry)) = exit
        else {
            panic!("complete owner must reach its exact boundary: {source:?}")
        };
        let root = SyntaxNode::new_root(green);
        assert_eq!(actual_line_entry, line_entry, "{source:?}");
        assert_eq!(root.to_string(), accepted, "{source:?}");
        assert_eq!(actual_remainder, remainder, "{source:?}");
        assert!(boundary.payload_view().is_boundary(), "{source:?}");
        assert!(
            root.descendants()
                .all(|node| !matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Missing)),
            "{source:?}",
        );
    }
}

#[test]
fn normalized_nested_case_like_respects_if_stops_before_fence_boundaries() {
    let operators = OperatorTable::empty();
    let fence = active_fence();
    let origin = 240;
    for (source, accepted, remainder, terminal_leading) in [
        (
            "> > if outer: case x: n -> y\n> > ```\nouter",
            "> > if outer: case x: n -> y",
            "> > ```\nouter",
            "\n",
        ),
        (
            "> > if outer: catch action: err, handler -> recover\r\n> ]\r\nouter",
            "> > if outer: catch action: err, handler -> recover",
            "> ]\r\nouter",
            "\r\n",
        ),
    ] {
        let (green, exit, actual_remainder) = run_normalized(
            source,
            &operators,
            origin,
            LineEntry::PhysicalStart,
            Some(&fence),
        );
        let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
            exit
        else {
            panic!("nested case-like owner must return the inherited boundary: {source:?}")
        };
        let root = SyntaxNode::new_root(green);
        assert_eq!(root.to_string(), accepted, "{source:?}");
        assert_eq!(actual_remainder, remainder, "{source:?}");
        assert!(
            root.descendants()
                .all(|node| !matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Missing)),
            "{source:?}",
        );
        let (leading, pending) = emit_terminal_leading_text(boundary);
        assert_eq!(leading, terminal_leading, "{source:?}");
        assert_eq!(
            pending.coordinate(),
            origin + accepted.len() + terminal_leading.len(),
            "{source:?}",
        );
    }
}

#[test]
fn normalized_catch_handler_boundaries_own_handler_arrow_and_body_missing_slots() {
    let operators = OperatorTable::empty();
    let fence = active_fence();
    let origin = 245;
    for (accepted, boundary_suffix, remainder, terminal_leading, missing) in [
        (
            "> > catch action: err, handler",
            "\n> > ```\nouter",
            "> > ```\nouter",
            "\n",
            1,
        ),
        (
            "> > catch action: err, handler",
            "\r\n> ]\r\nouter",
            "> ]\r\nouter",
            "\r\n",
            1,
        ),
        (
            "> > catch action: err,",
            "\n> > ```\nouter",
            "> > ```\nouter",
            "\n",
            2,
        ),
        (
            "> > catch action: err,",
            "\r\n> ]\r\nouter",
            "> ]\r\nouter",
            "\r\n",
            2,
        ),
        (
            "> > catch action { err, handler",
            "\n> > ```\nouter",
            "> > ```\nouter",
            "\n",
            2,
        ),
        (
            "> > catch action { err, handler",
            "\r\n> ]\r\nouter",
            "> ]\r\nouter",
            "\r\n",
            2,
        ),
        (
            "> > catch action { err,",
            "\n> > ```\nouter",
            "> > ```\nouter",
            "\n",
            3,
        ),
        (
            "> > catch action { err,",
            "\r\n> ]\r\nouter",
            "> ]\r\nouter",
            "\r\n",
            3,
        ),
    ] {
        let source = format!("{accepted}{boundary_suffix}");
        let (green, exit, actual_remainder) = run_normalized(
            &source,
            &operators,
            origin,
            LineEntry::PhysicalStart,
            Some(&fence),
        );
        let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
            exit
        else {
            panic!("Catch handler recovery must return its exact boundary: {source:?}")
        };
        let root = SyntaxNode::new_root(green);
        assert_eq!(root.to_string(), accepted, "{source:?}");
        assert_eq!(actual_remainder, remainder, "{source:?}");
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            missing,
            "{source:?}",
        );
        let (leading, pending) = emit_terminal_leading_text(boundary);
        assert_eq!(leading, terminal_leading, "{source:?}");
        assert_eq!(
            pending.coordinate(),
            origin + accepted.len() + terminal_leading.len(),
            "{source:?}",
        );
    }
}

#[test]
fn normalized_case_if_phase_recovery_stops_at_close_transition_and_eof() {
    let operators = OperatorTable::empty();
    let fence = active_fence();
    for (source, accepted, remainder, line_entry, missing) in [
        (
            "> > case\n> > ```\nouter",
            "> > case",
            "> > ```\nouter",
            LineEntry::PhysicalStart,
            2,
        ),
        (
            "> > case x: n if\n> > ```\nouter",
            "> > case x: n if",
            "> > ```\nouter",
            LineEntry::PhysicalStart,
            2,
        ),
        (
            "> > case x: n\n> ]\nouter",
            "> > case x: n",
            "> ]\nouter",
            LineEntry::PhysicalStart,
            1,
        ),
        (
            "> > case x: n ->",
            "> > case x: n ->",
            "",
            LineEntry::InLine,
            1,
        ),
        (
            "> > if\n> > ```\nouter",
            "> > if",
            "> > ```\nouter",
            LineEntry::PhysicalStart,
            1,
        ),
        (
            "> > if x:\n> ]\nouter",
            "> > if x:",
            "> ]\nouter",
            LineEntry::PhysicalStart,
            1,
        ),
    ] {
        let (green, exit, actual_remainder) = run_normalized(
            source,
            &operators,
            250,
            LineEntry::PhysicalStart,
            Some(&fence),
        );
        let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), actual_line_entry)) = exit
        else {
            panic!("phase recovery must return the exact boundary: {source:?}")
        };
        let root = SyntaxNode::new_root(green);
        assert_eq!(actual_line_entry, line_entry, "{source:?}");
        assert_eq!(root.to_string(), accepted, "{source:?}");
        assert_eq!(actual_remainder, remainder, "{source:?}");
        assert!(boundary.payload_view().is_boundary(), "{source:?}");
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            missing,
            "{source:?}",
        );
    }
}

#[test]
fn normalized_case_if_malformed_body_recovery_stops_before_the_fence() {
    let operators = OperatorTable::empty();
    let fence = active_fence();
    for (accepted, missing) in [("> > case x: n @", 1), ("> > if x: @", 0)] {
        let source = format!("{accepted}\n> > ```\nouter");
        let (green, exit, remainder) = run_normalized(
            &source,
            &operators,
            265,
            LineEntry::PhysicalStart,
            Some(&fence),
        );
        let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
            exit
        else {
            panic!("malformed recovery must return the exact boundary: {accepted:?}")
        };
        let root = SyntaxNode::new_root(green);
        assert!(boundary.payload_view().is_boundary(), "{accepted:?}");
        assert_eq!(root.to_string(), accepted, "{accepted:?}");
        assert_eq!(remainder, "> > ```\nouter", "{accepted:?}");
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            1,
            "{accepted:?}",
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            missing,
            "{accepted:?}",
        );
    }
}

#[test]
fn normalized_catch_braced_missing_close_is_owned_before_boundary_handoff() {
    let operators = OperatorTable::empty();
    let fence = active_fence();
    let accepted = "> > catch action { err -> recover";
    let source = format!("{accepted}\n> > ```\nouter");
    let (green, exit, remainder) = run_normalized(
        &source,
        &operators,
        275,
        LineEntry::PhysicalStart,
        Some(&fence),
    );
    let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
        exit
    else {
        panic!("Catch must return the boundary after owning its missing close")
    };
    let root = SyntaxNode::new_root(green);
    assert!(boundary.payload_view().is_boundary());
    assert_eq!(root.to_string(), accepted);
    assert_eq!(remainder, "> > ```\nouter");
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
}

#[test]
fn normalized_case_and_if_own_the_deeper_statement_body() {
    let operators = OperatorTable::empty();
    let fence = plain_fence();
    for (source, owner) in [
        ("case x:\n  n ->\n    body", SyntaxKind::CaseExpression),
        ("if x:\n  body", SyntaxKind::IfExpression),
    ] {
        let (green, exit, remainder) = run_normalized(
            source,
            &operators,
            300,
            LineEntry::PhysicalStart,
            Some(&fence),
        );
        let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::InLine)) = exit
        else {
            panic!("the deeper canonical statement body must complete: {source:?}")
        };
        let root = SyntaxNode::new_root(green);
        assert!(boundary.payload_view().is_boundary());
        assert_eq!(root.to_string(), source);
        assert_eq!(remainder, "");
        assert!(root.descendants().any(|node| node.kind() == owner));
        assert!(
            root.descendants()
                .any(|node| node.kind() == SyntaxKind::IndentedStatementBlock)
        );
    }
}

#[test]
fn normalized_pratt_owns_braced_statements_to_the_fence_boundary() {
    let operators = OperatorTable::empty();
    let fence = active_fence();
    let accepted = "> > { x }";
    let source = format!("{accepted}\n> > ```\nouter");
    let (green, exit, remainder) = run_normalized(
        &source,
        &operators,
        850,
        LineEntry::PhysicalStart,
        Some(&fence),
    );
    let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
        exit
    else {
        panic!("the braced owner must reach the exact fence boundary")
    };
    assert!(boundary.payload_view().is_boundary());
    assert_eq!(green.to_string(), accepted);
    assert_eq!(remainder, "> > ```\nouter");
}

#[test]
fn normalized_pratt_owns_parenthesized_expression_until_the_fence_boundary() {
    let operators = OperatorTable::empty();
    let fence = active_fence();
    let (green, exit, remainder) = run_normalized(
        "> > (x)\n> > ```\nouter",
        &operators,
        900,
        LineEntry::PhysicalStart,
        Some(&fence),
    );
    let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
        exit
    else {
        panic!("the parenthesized owner must return the exact boundary")
    };
    assert!(boundary.payload_view().is_boundary());
    assert_eq!(remainder, "> > ```\nouter");
    assert_eq!(
        syntax_tokens(green),
        [
            (SyntaxKind::YmQuotePrefix, "> > ".to_owned()),
            (SyntaxKind::LParen, "(".to_owned()),
            (SyntaxKind::Identifier, "x".to_owned()),
            (SyntaxKind::RParen, ")".to_owned()),
        ]
    );
}

#[test]
fn normalized_pratt_owns_nested_fixed_tails_before_handoff() {
    let operators = OperatorTable::empty();
    let fence = active_fence();
    let source = "> > x[a b(c)].field::segment\n> > ```\nouter";
    let (green, exit, remainder) = run_normalized(
        source,
        &operators,
        950,
        LineEntry::PhysicalStart,
        Some(&fence),
    );
    let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
        exit
    else {
        panic!("the fixed-tail chain must return the exact boundary")
    };
    let root = SyntaxNode::new_root(green);
    assert!(boundary.payload_view().is_boundary());
    assert_eq!(remainder, "> > ```\nouter");
    assert_eq!(root.to_string(), "> > x[a b(c)].field::segment");
    for kind in [
        SyntaxKind::IndexTail,
        SyntaxKind::CallTail,
        SyntaxKind::FieldTail,
        SyntaxKind::PathTail,
    ] {
        assert!(root.descendants().any(|node| node.kind() == kind));
    }
}

#[test]
fn normalized_dot_projections_own_tuple_and_record_spread_items() {
    let operators = OperatorTable::empty();
    let fence = active_fence();
    let source = "> > x.(a).{.. b}\n> > ```\nouter";
    let (green, exit, remainder) = run_normalized(
        source,
        &operators,
        975,
        LineEntry::PhysicalStart,
        Some(&fence),
    );
    let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
        exit
    else {
        panic!("the projection chain must return the exact boundary")
    };
    let root = SyntaxNode::new_root(green);
    assert!(boundary.payload_view().is_boundary());
    assert_eq!(remainder, "> > ```\nouter");
    assert_eq!(root.to_string(), "> > x.(a).{.. b}");
    for kind in [
        SyntaxKind::ProjectionTupleTail,
        SyntaxKind::ProjectionRecordTail,
        SyntaxKind::ProjectionRecordSpreadItem,
    ] {
        assert!(root.descendants().any(|node| node.kind() == kind));
    }
    assert!(
        !root
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Missing)
    );
}

#[test]
fn normalized_nested_delimiters_stream_quote_prefixes_line_by_line() {
    let operators = OperatorTable::empty();
    let fence = active_fence();
    let accepted = "> > x[\n> >   a(\n> >     b\n> >   )\n> > ]";
    let source = format!("{accepted}\n> > ```\nouter");
    let (green, exit, remainder) = run_normalized(
        &source,
        &operators,
        1000,
        LineEntry::PhysicalStart,
        Some(&fence),
    );
    let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
        exit
    else {
        panic!("the multiline nested delimiter must return the exact boundary")
    };
    let root = SyntaxNode::new_root(green);
    assert!(boundary.payload_view().is_boundary());
    assert_eq!(remainder, "> > ```\nouter");
    assert_eq!(root.to_string(), accepted);
    assert_eq!(
        root.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::YmQuotePrefix)
            .count(),
        5
    );
}

#[test]
fn normalized_unclosed_delimiter_emits_only_its_mandatory_close() {
    let operators = OperatorTable::empty();
    let fence = active_fence();
    let (green, exit, remainder) = run_normalized(
        "> > x(a\n> > ```\nouter",
        &operators,
        1100,
        LineEntry::PhysicalStart,
        Some(&fence),
    );
    let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
        exit
    else {
        panic!("the unclosed call must return the exact boundary")
    };
    let root = SyntaxNode::new_root(green);
    assert!(boundary.payload_view().is_boundary());
    assert_eq!(remainder, "> > ```\nouter");
    assert_eq!(root.to_string(), "> > x(a");
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
}

#[test]
fn normalized_pratt_prefix_boundary_emits_only_its_mandatory_missing() {
    let operators = OperatorTable::from_declarations([OperatorDeclaration::new(
        "?",
        OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
    )])
    .expect("one prefix declaration");
    let fence = active_fence();
    let (green, exit, remainder) = run_normalized(
        "> > ?\n> > ```\nouter",
        &operators,
        1200,
        LineEntry::PhysicalStart,
        Some(&fence),
    );
    let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
        exit
    else {
        panic!("the prefix operand owner must hand the boundary upward")
    };

    let root = SyntaxNode::new_root(green);
    assert!(boundary.payload_view().is_boundary());
    assert_eq!(remainder, "> > ```\nouter");
    assert_eq!(root.to_string(), "> > ?");
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
}

#[test]
fn normalized_pratt_owns_with_body() {
    let operators = OperatorTable::empty();
    let fence = active_fence();
    let (green, exit, remainder) = run_normalized(
        "> > x with: y",
        &operators,
        1000,
        LineEntry::PhysicalStart,
        Some(&fence),
    );
    let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::InLine)) = exit
    else {
        panic!("the normalized with owner must reach physical EOF")
    };
    assert!(boundary.payload_view().is_boundary());
    assert_eq!(remainder, "");
    assert_eq!(green.to_string(), "> > x with: y");
}

#[test]
fn normalized_pratt_owns_colon_body() {
    let operators = OperatorTable::empty();
    let fence = active_fence();
    let (green, exit, remainder) = run_normalized(
        "> > x: y",
        &operators,
        1100,
        LineEntry::PhysicalStart,
        Some(&fence),
    );
    let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::InLine)) = exit
    else {
        panic!("the normalized colon owner must reach physical EOF")
    };
    assert!(boundary.payload_view().is_boundary());
    assert_eq!(remainder, "");
    assert_eq!(green.to_string(), "> > x: y");
}

#[test]
fn normalized_type_streams_path_application_and_arrow_to_the_boundary() {
    let fence = active_fence();
    let accepted = "> > List::Result Arg -> Out";
    let source = format!("{accepted}\n> > ```\nouter");
    let (green, exit, remainder) =
        run_type_normalized(&source, 1300, LineEntry::PhysicalStart, Some(&fence));
    let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
        exit
    else {
        panic!("the normalized Type tail must return the exact boundary")
    };
    let root = SyntaxNode::new_root(green);

    assert!(boundary.payload_view().is_boundary());
    assert_eq!(remainder, "> > ```\nouter");
    assert_eq!(root.to_string(), accepted);
    for kind in [
        SyntaxKind::TypePathTail,
        SyntaxKind::TypeApplyArgument,
        SyntaxKind::TypeArrowTail,
    ] {
        assert!(root.descendants().any(|node| node.kind() == kind));
    }
}

#[test]
fn normalized_type_arrow_boundary_emits_only_its_mandatory_missing() {
    let fence = active_fence();
    let (green, exit, remainder) = run_type_normalized(
        "> > A ->\n> > ```\nouter",
        1400,
        LineEntry::PhysicalStart,
        Some(&fence),
    );
    let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
        exit
    else {
        panic!("the arrow RHS must return the exact boundary")
    };
    let root = SyntaxNode::new_root(green);

    assert!(boundary.payload_view().is_boundary());
    assert_eq!(remainder, "> > ```\nouter");
    assert_eq!(root.to_string(), "> > A ->");
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
}

#[test]
fn normalized_type_shared_delimiters_own_their_closes_before_boundary_handoff() {
    let fence = active_fence();
    for (accepted, kind) in [
        ("> > (A)", SyntaxKind::ParenthesizedTypeGroup),
        ("> > A(B)", SyntaxKind::TypeCallTail),
        ("> > [e] T", SyntaxKind::BracketRow),
        ("> > T [e] -> U", SyntaxKind::TypeArrowTail),
        ("> > '[e]", SyntaxKind::EffectRowType),
    ] {
        let source = format!("{accepted}\n> > ```\nouter");
        let (green, exit, remainder) =
            run_type_normalized(&source, 1500, LineEntry::PhysicalStart, Some(&fence));
        let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
            exit
        else {
            panic!("the shared Type delimiter owner must return the exact boundary: {accepted:?}")
        };
        let root = SyntaxNode::new_root(green);
        assert!(boundary.payload_view().is_boundary(), "{accepted:?}");
        assert!(
            boundary.leading_view().has_ordinary_newline(),
            "{accepted:?}"
        );
        assert_eq!(
            boundary.leading_view().indentation_after_newline(),
            Some(0),
            "{accepted:?}"
        );
        assert_eq!(remainder, "> > ```\nouter", "{accepted:?}");
        assert_eq!(root.to_string(), accepted, "{accepted:?}");
        assert!(
            root.descendants().any(|node| node.kind() == kind),
            "{accepted:?}"
        );
        assert!(
            root.descendants()
                .all(|node| !matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Missing)),
            "{accepted:?}"
        );
    }
}

#[test]
fn normalized_type_delimiter_streams_quote_prefixes_on_each_physical_line() {
    let fence = active_fence();
    let accepted = "> > (\n> >   A(\n> >     B\n> >   )\n> > )";
    let source = format!("{accepted}\n> > ```\nouter");
    let (green, exit, remainder) =
        run_type_normalized(&source, 1600, LineEntry::PhysicalStart, Some(&fence));
    let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
        exit
    else {
        panic!("the multiline Type delimiter must return the exact boundary")
    };
    let root = SyntaxNode::new_root(green);

    assert!(boundary.payload_view().is_boundary());
    assert_eq!(remainder, "> > ```\nouter");
    assert_eq!(root.to_string(), accepted);
    assert_eq!(
        root.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::YmQuotePrefix)
            .count(),
        5
    );
}

#[test]
fn normalized_type_unclosed_call_emits_only_its_mandatory_close() {
    let fence = active_fence();
    let (green, exit, remainder) = run_type_normalized(
        "> > A(B\n> > ```\nouter",
        1700,
        LineEntry::PhysicalStart,
        Some(&fence),
    );
    let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
        exit
    else {
        panic!("the unclosed Type call must return the exact boundary")
    };
    let root = SyntaxNode::new_root(green);

    assert!(boundary.payload_view().is_boundary());
    assert_eq!(remainder, "> > ```\nouter");
    assert_eq!(root.to_string(), "> > A(B");
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
}

#[test]
fn normalized_type_polymorphic_variant_composes_inside_existing_type_owners() {
    let fence = active_fence();
    let origin = 1800;
    for (accepted, owner) in [
        ("> > (:{A})", SyntaxKind::ParenthesizedTypeGroup),
        ("> > {a: :{A}}", SyntaxKind::NamedRecordType),
        ("> > for 'a: :{A}", SyntaxKind::ForallType),
    ] {
        let source = format!("{accepted}\n> > ```\nouter");
        let (green, exit, remainder) =
            run_type_normalized(&source, origin, LineEntry::PhysicalStart, Some(&fence));
        let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
            exit
        else {
            panic!("the nested polymorphic variant must reach the exact boundary: {accepted:?}")
        };
        let root = SyntaxNode::new_root(green);

        assert!(boundary.payload_view().is_boundary(), "{accepted:?}");
        assert_eq!(remainder, "> > ```\nouter", "{accepted:?}");
        assert_eq!(root.to_string(), accepted, "{accepted:?}");
        assert!(root.descendants().any(|node| node.kind() == owner));
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
                .count(),
            1,
            "{accepted:?}"
        );
        assert!(
            root.descendants()
                .all(|node| !matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Missing)),
            "{accepted:?}"
        );
        let (leading, pending) = emit_terminal_leading_text(boundary);
        assert_eq!(leading, "\n", "{accepted:?}");
        assert_eq!(pending.coordinate(), origin + accepted.len() + 1);
    }
}

#[test]
fn normalized_type_balanced_head_retry_resynchronizes_before_boundary() {
    let fence = active_fence();
    let accepted = "> > [e] [bad] T";
    let source = format!("{accepted}\n> > ```\nouter");
    let origin = 1900;
    let (green, exit, remainder) =
        run_type_normalized(&source, origin, LineEntry::PhysicalStart, Some(&fence));
    let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
        exit
    else {
        panic!("the balanced malformed head retry must reach the exact boundary")
    };
    let root = SyntaxNode::new_root(green);

    assert_eq!(root.to_string(), accepted);
    assert_eq!(remainder, "> > ```\nouter");
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .count(),
        1
    );
    assert!(
        root.descendants()
            .all(|node| node.kind() != SyntaxKind::Missing)
    );
    let error = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::Error)
        .unwrap();
    assert_eq!(error.text(), "[bad]");
    assert_eq!(error.first_token().unwrap().kind(), SyntaxKind::LBracket);
    assert_eq!(error.last_token().unwrap().kind(), SyntaxKind::RBracket);
    let (leading, pending) = emit_terminal_leading_text(boundary);
    assert_eq!(leading, "\n");
    assert_eq!(pending.coordinate(), origin + accepted.len() + 1);
}

#[test]
fn ordinary_type_unmatched_balanced_head_consumes_its_safe_prefix() {
    let operators = OperatorTable::empty();
    let mut input = "[e][bad";
    let mut recover = Recover::new(&operators);
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let exit = type_expr(In::new(&mut input, &mut recover, &mut builder));
    builder.finish_node();
    let Some(Err(Either::Right(_))) = exit else {
        panic!("the unmatched ordinary head must reach EOF")
    };

    let (green, records) = builder.finish_with_recoveries();
    assert_eq!(green.to_string(), "[e][bad");
    assert_eq!(records.len(), 1);
    assert_eq!(records[0].site.range, 3..7);
    assert_eq!(input, "");
}

#[test]
fn normalized_type_unmatched_balanced_head_stops_before_close_and_transition_lines() {
    let fence = active_fence();
    let origin = 2000;
    for (source, accepted, pending_leading, remainder) in [
        (
            "> > [e] [bad\r\n> > ```\nouter]",
            "> > [e] [bad",
            "\r\n",
            "> > ```\nouter]",
        ),
        (
            "> > [e] [bad\n> ]\nafter",
            "> > [e] [bad",
            "\n",
            "> ]\nafter",
        ),
    ] {
        let (green, exit, actual_remainder) =
            run_type_normalized(source, origin, LineEntry::PhysicalStart, Some(&fence));
        let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
            exit
        else {
            panic!("the unmatched head must hand its exact boundary upward: {source:?}")
        };
        let root = SyntaxNode::new_root(green);

        assert_eq!(root.to_string(), accepted, "{source:?}");
        assert_eq!(actual_remainder, remainder, "{source:?}");
        assert!(
            remainder.contains(']'),
            "the outer close control must remain live"
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            1,
            "{source:?}"
        );
        assert!(
            root.descendants()
                .all(|node| node.kind() != SyntaxKind::Missing),
            "{source:?}"
        );
        let (leading, pending) = emit_terminal_leading_text(boundary);
        assert_eq!(leading, pending_leading, "{source:?}");
        assert_eq!(
            pending.coordinate(),
            origin + accepted.len() + pending_leading.len(),
            "{source:?}"
        );
    }
}

#[test]
fn normalized_type_unmatched_balanced_head_keeps_continuation_and_boundary_prefixes_distinct() {
    let fence = active_fence();
    let origin = 2100;
    for (accepted, pending_leading, error_tokens) in [
        (
            "> > [e] [bad\n> >   still",
            "\n",
            vec![
                (SyntaxKind::LBracket, "["),
                (SyntaxKind::Identifier, "bad"),
                (SyntaxKind::Newline, "\n"),
                (SyntaxKind::YmQuotePrefix, "> > "),
                (SyntaxKind::Whitespace, "  "),
                (SyntaxKind::Identifier, "still"),
            ],
        ),
        (
            "> > [e] [bad",
            "/*\n> > still\n",
            vec![(SyntaxKind::LBracket, "["), (SyntaxKind::Identifier, "bad")],
        ),
    ] {
        let source = format!("{accepted}{pending_leading}> > ```\nouter]");
        let (green, exit, remainder) =
            run_type_normalized(&source, origin, LineEntry::PhysicalStart, Some(&fence));
        let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
            exit
        else {
            panic!("the malformed head must precede its exact boundary: {source:?}")
        };
        let root = SyntaxNode::new_root(green);
        let error = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::Error)
            .expect("one malformed bracket-head Error");
        let actual_tokens: Vec<_> = error
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect();

        assert_eq!(root.to_string(), accepted, "{source:?}");
        assert_eq!(remainder, "> > ```\nouter]", "{source:?}");
        assert_eq!(
            actual_tokens,
            error_tokens
                .into_iter()
                .map(|(kind, text)| (kind, text.to_owned()))
                .collect::<Vec<_>>(),
            "{source:?}"
        );
        let (leading, pending) = emit_terminal_leading_text(boundary);
        assert_eq!(leading, pending_leading, "{source:?}");
        assert_eq!(
            pending.coordinate(),
            origin + accepted.len() + pending_leading.len(),
            "{source:?}"
        );
    }
}

#[test]
fn normalized_type_unmatched_head_leaves_equal_indent_foreign_item_pending() {
    let fence = active_fence();
    let source = "> > [e] [bad\n> > still\n> > ```\nouter]";
    let (green, exit, remainder) =
        run_type_normalized(source, 2100, LineEntry::PhysicalStart, Some(&fence));
    let Some(NormalizedExit::Complete(Err(Either::Left(mut item)), LineEntry::InLine)) = exit
    else {
        panic!("equal-indent continuation is a pending ordinary Item")
    };
    assert_eq!(green.to_string(), "> > [e] [bad");
    assert_eq!(item.payload_view().spelling(), Some("still"));
    assert_eq!(remainder, "\n> > ```\nouter]");
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    item.emit_all_remaining_leading(&mut output);
    output.finish_node();
    let leading = SyntaxNode::new_root(output.finish());
    assert_eq!(leading.text(), "\n> > ");
    assert!(
        leading
            .children_with_tokens()
            .any(|child| child.kind() == SyntaxKind::YmQuotePrefix)
    );
}
#[test]
fn normalized_type_parses_named_record_before_boundary() {
    let fence = active_fence();
    let accepted = "> > {a: A}";
    let source = format!("{accepted}\n> > ```\nouter");
    let (green, exit, remainder) =
        run_type_normalized(&source, 2200, LineEntry::PhysicalStart, Some(&fence));
    let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
        exit
    else {
        panic!("the named record must return the exact boundary")
    };
    let root = SyntaxNode::new_root(green);

    assert!(boundary.payload_view().is_boundary());
    assert_eq!(remainder, "> > ```\nouter");
    assert_eq!(root.to_string(), accepted);
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::NamedRecordType)
            .count(),
        1
    );
    assert!(
        root.descendants()
            .all(|node| !matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Missing))
    );
}

#[test]
fn normalized_type_named_record_streams_nested_record_prefixes() {
    let fence = active_fence();
    let accepted = "> > {\n> >   a: {\n> >     b: B\n> >   }\n> > }";
    let source = format!("{accepted}\n> > ```\nouter");
    let (green, exit, remainder) =
        run_type_normalized(&source, 2300, LineEntry::PhysicalStart, Some(&fence));
    let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
        exit
    else {
        panic!("the nested named record must return the exact boundary")
    };
    let root = SyntaxNode::new_root(green);

    assert!(boundary.payload_view().is_boundary());
    assert_eq!(remainder, "> > ```\nouter");
    assert_eq!(root.to_string(), accepted);
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::NamedRecordType)
            .count(),
        2
    );
    assert_eq!(
        root.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::YmQuotePrefix)
            .count(),
        5
    );
    assert!(
        root.descendants()
            .all(|node| !matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Missing))
    );
}

#[test]
fn normalized_type_named_record_recovery_stops_at_exact_boundary() {
    let fence = active_fence();
    let origin = 2400;
    for (accepted, expected_error, expected_missing) in [
        ("> > {", 0, 1),
        ("> > {a:", 0, 2),
        ("> > {a: A,", 0, 2),
        ("> > {@ bad", 1, 1),
        ("> > {@ bad: A", 1, 1),
        ("> > {a @ bad", 1, 1),
        ("> > {a: @ bad", 1, 1),
        ("> > {a: A; @ bad", 1, 2),
    ] {
        let source = format!("{accepted}\n> > ```\nouter");
        let (green, exit, remainder) =
            run_type_normalized(&source, origin, LineEntry::PhysicalStart, Some(&fence));
        let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
            exit
        else {
            panic!("record recovery must return the exact boundary: {accepted:?}")
        };
        let root = SyntaxNode::new_root(green);

        assert_eq!(root.to_string(), accepted, "{accepted:?}");
        assert_eq!(remainder, "> > ```\nouter", "{accepted:?}");
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            expected_error,
            "{accepted:?}"
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            expected_missing,
            "{accepted:?}"
        );
        let (leading, pending) = emit_terminal_leading_text(boundary);
        assert_eq!(leading, "\n", "{accepted:?}");
        assert_eq!(
            pending.coordinate(),
            origin + accepted.len() + 1,
            "{accepted:?}"
        );
    }
}

#[test]
fn normalized_type_named_record_next_field_probe_stops_before_outer_colon() {
    let fence = active_fence();
    let accepted = "> > {a: A b";
    let source = format!("{accepted}\n> > ```\n: outer");
    let (green, exit, remainder) =
        run_type_normalized(&source, 2450, LineEntry::PhysicalStart, Some(&fence));
    let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
        exit
    else {
        panic!("the next-field probe must stop at the exact boundary")
    };
    let root = SyntaxNode::new_root(green);

    assert!(boundary.payload_view().is_boundary());
    assert_eq!(remainder, "> > ```\n: outer");
    assert_eq!(root.to_string(), accepted);
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::TypeRecordField)
            .count(),
        1
    );
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
}

#[test]
fn normalized_type_named_record_resolves_colon_before_rhs_polymorphic_variants() {
    let fence = active_fence();
    for (accepted, expected_error, expected_missing, expected_variants, expected_records) in [
        ("> > {a :{A}}", 0, 1, 0, 2),
        ("> > {a @ :{A}}", 1, 1, 0, 2),
        ("> > {a @ : :{A}}", 1, 0, 1, 1),
        ("> > {a: :{A}}", 0, 0, 1, 1),
        ("> > {a: A :{B}}", 0, 0, 1, 1),
        ("> > {a: @ :{B}}", 1, 0, 1, 1),
    ] {
        let source = format!("{accepted}\n> > ```\nouter");
        let (green, exit, actual_remainder) =
            run_type_normalized(&source, 2500, LineEntry::PhysicalStart, Some(&fence));
        let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
            exit
        else {
            panic!("the record must resolve the colon and nested RHS: {accepted:?}")
        };
        let root = SyntaxNode::new_root(green);

        assert!(boundary.payload_view().is_boundary(), "{accepted:?}");
        assert_eq!(root.to_string(), accepted, "{accepted:?}");
        assert_eq!(actual_remainder, "> > ```\nouter", "{accepted:?}");
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
                .count(),
            expected_variants,
            "{accepted:?}"
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::NamedRecordType)
                .count(),
            expected_records,
            "{accepted:?}"
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            expected_error,
            "{accepted:?}"
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            expected_missing,
            "{accepted:?}"
        );
        assert!(
            root.descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .filter(|token| token.kind() == SyntaxKind::Whitespace)
                .count()
                > 0,
            "the nested primary's leading whitespace must be emitted: {accepted:?}"
        );
    }
}

#[test]
fn normalized_type_malformed_name_probe_stops_before_outer_transition_colon() {
    let fence = active_fence();
    let origin = 2600;
    let accepted = "> > {@ (x)";
    let source = format!("{accepted}\n> ]\n: outer");
    let (green, exit, remainder) =
        run_type_normalized(&source, origin, LineEntry::PhysicalStart, Some(&fence));
    let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
        exit
    else {
        panic!("the malformed-name probe must return the exact transition boundary")
    };
    let root = SyntaxNode::new_root(green);

    assert!(boundary.payload_view().is_boundary());
    assert_eq!(remainder, "> ]\n: outer");
    assert_eq!(root.to_string(), accepted);
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::TypeRecordField)
            .count(),
        0
    );
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .count(),
        1
    );
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
    let (leading, pending) = emit_terminal_leading_text(boundary);
    assert_eq!(leading, "\n");
    assert_eq!(pending.coordinate(), origin + accepted.len() + 1);
}

#[test]
fn normalized_type_forall_streams_valid_and_nested_bodies_until_the_boundary() {
    let fence = active_fence();
    let accepted = "> > for 'a: for 'b: Pair(\n> > 'a,\n> > 'b)";
    let source = format!("{accepted}\n> > ```\nouter");
    let origin = 2700;
    let (green, exit, remainder) =
        run_type_normalized(&source, origin, LineEntry::PhysicalStart, Some(&fence));
    let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
        exit
    else {
        panic!("the nested forall body must return the exact fence boundary")
    };
    let root = SyntaxNode::new_root(green);

    assert!(boundary.payload_view().is_boundary());
    assert_eq!(remainder, "> > ```\nouter");
    assert_eq!(root.to_string(), accepted);
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::ForallType)
            .count(),
        2
    );
    assert_eq!(
        root.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::YmQuotePrefix)
            .count(),
        3
    );
    assert!(
        root.descendants()
            .all(|node| !matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Missing))
    );
    let (leading, pending) = emit_terminal_leading_text(boundary);
    assert_eq!(leading, "\n");
    assert_eq!(pending.coordinate(), origin + accepted.len() + 1);
}

#[test]
fn normalized_type_forall_returns_each_phase_boundary_after_only_owned_recovery() {
    let fence = active_fence();
    let origin = 2800;
    for (accepted, expected_error, expected_missing, expected_binders) in [
        ("> > for", 0, 1, 1),
        ("> > for 'a", 0, 1, 1),
        ("> > for,", 1, 0, 1),
        ("> > for 'a,", 1, 1, 2),
        ("> > for 'a:", 0, 1, 1),
        ("> > for @", 1, 0, 1),
        ("> > for 'a @", 1, 0, 1),
        ("> > for 'a: @", 1, 0, 1),
    ] {
        let source = format!("{accepted}\r\n> > ```\r\nouter");
        let (green, exit, remainder) =
            run_type_normalized(&source, origin, LineEntry::PhysicalStart, Some(&fence));
        let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
            exit
        else {
            panic!("the forall phase must return the exact boundary: {accepted:?}")
        };
        let root = SyntaxNode::new_root(green);

        assert!(boundary.payload_view().is_boundary(), "{accepted:?}");
        assert_eq!(remainder, "> > ```\r\nouter", "{accepted:?}");
        assert_eq!(root.to_string(), accepted, "{accepted:?}");
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            expected_error,
            "{accepted:?}"
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            expected_missing,
            "{accepted:?}"
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::ForallTypeBinder)
                .count(),
            expected_binders,
            "{accepted:?}"
        );
        let (leading, pending) = emit_terminal_leading_text(boundary);
        assert_eq!(leading, "\r\n", "{accepted:?}");
        assert_eq!(
            pending.coordinate(),
            origin + accepted.len() + 2,
            "{accepted:?}"
        );
    }
}

#[test]
fn normalized_type_forall_malformed_run_stops_before_outer_transition() {
    let fence = active_fence();
    let origin = 2900;
    let accepted = "> > for 'a @";
    let source = format!("{accepted}\n> ]\n: outer");
    let (green, exit, remainder) =
        run_type_normalized(&source, origin, LineEntry::PhysicalStart, Some(&fence));
    let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
        exit
    else {
        panic!("the malformed-phase run must return the exact transition boundary")
    };
    let root = SyntaxNode::new_root(green);

    assert!(boundary.payload_view().is_boundary());
    assert_eq!(remainder, "> ]\n: outer");
    assert_eq!(root.to_string(), accepted);
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .count(),
        1
    );
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        0
    );
    let (leading, pending) = emit_terminal_leading_text(boundary);
    assert_eq!(leading, "\n");
    assert_eq!(pending.coordinate(), origin + accepted.len() + 1);
}

#[test]
fn normalized_type_forall_resolves_colon_before_rhs_polymorphic_variants() {
    let fence = active_fence();
    for (accepted, expected_error, expected_missing, variants, records) in [
        ("> > for 'a :{A}", 0, 1, 0, 1),
        ("> > for 'a: :{A}", 0, 0, 1, 0),
        ("> > for 'a @ :{A}", 1, 1, 0, 1),
        ("> > for 'a @ : :{A}", 1, 0, 1, 0),
        ("> > for 'a: @ :{A}", 1, 0, 1, 0),
    ] {
        let source = format!("{accepted}\n> > ```\nouter");
        let (green, exit, remainder) =
            run_type_normalized(&source, 3000, LineEntry::PhysicalStart, Some(&fence));
        let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
            exit
        else {
            panic!("the forall owner must parse its record or variant body: {accepted:?}")
        };
        let root = SyntaxNode::new_root(green);

        assert!(boundary.payload_view().is_boundary(), "{accepted:?}");
        assert_eq!(root.to_string(), accepted, "{accepted:?}");
        assert_eq!(remainder, "> > ```\nouter", "{accepted:?}");
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
                .count(),
            variants,
            "{accepted:?}"
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::NamedRecordType)
                .count(),
            records,
            "{accepted:?}"
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            expected_error,
            "{accepted:?}"
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            expected_missing,
            "{accepted:?}"
        );
    }
}

#[test]
fn normalized_type_polymorphic_variant_streams_nested_tags_and_payloads() {
    let fence = active_fence();
    let accepted = "> > :{A Pair(\n> >   Int),\n> > B :{C D}}";
    let source = format!("{accepted}\n> > ```\nouter");
    let origin = 3100;
    let (green, exit, remainder) =
        run_type_normalized(&source, origin, LineEntry::PhysicalStart, Some(&fence));
    let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
        exit
    else {
        panic!("the nested polymorphic variant must return the exact fence boundary")
    };
    let root = SyntaxNode::new_root(green);

    assert!(boundary.payload_view().is_boundary());
    assert_eq!(remainder, "> > ```\nouter");
    assert_eq!(root.to_string(), accepted);
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
            .count(),
        2
    );
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantTag)
            .count(),
        3
    );
    assert_eq!(
        root.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::YmQuotePrefix)
            .count(),
        3
    );
    assert!(
        root.descendants()
            .all(|node| !matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Missing))
    );
    let (leading, pending) = emit_terminal_leading_text(boundary);
    assert_eq!(leading, "\n");
    assert_eq!(pending.coordinate(), origin + accepted.len() + 1);
}

#[test]
fn normalized_type_polymorphic_variant_stops_each_phase_at_the_exact_fence_boundary() {
    let fence = active_fence();
    let origin = 3200;
    for (
        accepted,
        line_break,
        boundary_line,
        expected_error,
        expected_missing,
        expected_tags,
        expected_payloads,
    ) in [
        ("> > :{", "\n", "> > ```\nouter", 0, 1, 0, 0),
        ("> > :{A", "\n", "> > ```\nouter", 0, 1, 1, 0),
        ("> > :{A,", "\n", "> > ```\nouter", 0, 2, 1, 0),
        ("> > :{A(", "\n", "> > ```\nouter", 0, 3, 1, 1),
        ("> > :{@ bad", "\r\n", "> > ```\r\nouter", 1, 1, 1, 0),
        ("> > :{A @", "\r\n", "> ]\r\n: outer", 1, 1, 1, 1),
    ] {
        let source = format!("{accepted}{line_break}{boundary_line}");
        let (green, exit, remainder) =
            run_type_normalized(&source, origin, LineEntry::PhysicalStart, Some(&fence));
        let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
            exit
        else {
            panic!("the polymorphic-variant phase must return a completed boundary: {accepted:?}")
        };
        let root = SyntaxNode::new_root(green);

        assert!(boundary.payload_view().is_boundary(), "{accepted:?}");
        assert_eq!(remainder, boundary_line, "{accepted:?}");
        assert_eq!(root.to_string(), accepted, "{accepted:?}");
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            expected_error,
            "{accepted:?}"
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            expected_missing,
            "{accepted:?}"
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantTag)
                .count(),
            expected_tags,
            "{accepted:?}"
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantPayload)
                .count(),
            expected_payloads,
            "{accepted:?}"
        );
        let (leading, pending) = emit_terminal_leading_text(boundary);
        assert_eq!(leading, line_break, "{accepted:?}");
        assert_eq!(
            pending.coordinate(),
            origin + accepted.len() + line_break.len(),
            "{accepted:?}"
        );
    }
}

#[test]
fn normalized_pattern_hands_close_transition_and_eof_boundaries_up_exactly() {
    let fence = active_fence();
    let origin = 3400;
    for (source, accepted, remainder, expected_line_entry, expected_terminal_leading) in [
        (
            "> > A\n> > ```\nouter",
            "> > A",
            "> > ```\nouter",
            LineEntry::PhysicalStart,
            "\n",
        ),
        (
            "> > A\r\n> ]\r\nouter",
            "> > A",
            "> ]\r\nouter",
            LineEntry::PhysicalStart,
            "\r\n",
        ),
        ("> > A", "> > A", "", LineEntry::InLine, ""),
    ] {
        let (green, exit, actual_remainder) = run_pattern_normalized(
            source,
            origin,
            LineEntry::PhysicalStart,
            Some(&fence),
            PATTERN_DEFAULT_STOPS,
        );
        let NormalizedExit::Complete(Err(Either::Left(boundary)), line_entry) = exit else {
            panic!("Pattern must return its exact boundary: {source:?}")
        };

        assert_eq!(line_entry, expected_line_entry, "{source:?}");
        assert_eq!(green.to_string(), accepted, "{source:?}");
        assert_eq!(actual_remainder, remainder, "{source:?}");
        assert!(boundary.payload_view().is_boundary(), "{source:?}");
        let (leading, pending) = emit_terminal_leading_text(boundary);
        assert_eq!(leading, expected_terminal_leading, "{source:?}");
        assert_eq!(
            pending.coordinate(),
            origin + accepted.len() + expected_terminal_leading.len(),
            "{source:?}"
        );
    }
}

#[test]
fn normalized_pattern_stops_recovery_tails_and_annotations_at_the_fence() {
    let fence = active_fence();
    let origin = 3500;
    for (accepted, expected_error, expected_missing) in [
        ("> > @ bad", 1, 0),
        ("> > A as", 0, 1),
        ("> > A |", 0, 1),
        ("> > A:", 0, 1),
    ] {
        for (suffix, expected_remainder, expected_line_entry) in [
            (
                "\n> > ```\nouter",
                "> > ```\nouter",
                LineEntry::PhysicalStart,
            ),
            ("\r\n> ]\r\nouter", "> ]\r\nouter", LineEntry::PhysicalStart),
            ("", "", LineEntry::InLine),
        ] {
            let source = format!("{accepted}{suffix}");
            let (green, exit, remainder) = run_pattern_normalized(
                &source,
                origin,
                LineEntry::PhysicalStart,
                Some(&fence),
                PATTERN_DEFAULT_STOPS,
            );
            let NormalizedExit::Complete(Err(Either::Left(boundary)), line_entry) = exit else {
                panic!("Pattern recovery must hand the boundary upward: {source:?}")
            };
            let root = SyntaxNode::new_root(green);

            assert_eq!(line_entry, expected_line_entry, "{source:?}");
            assert!(boundary.payload_view().is_boundary(), "{source:?}");
            assert_eq!(remainder, expected_remainder, "{source:?}");
            assert_eq!(root.to_string(), accepted, "{source:?}");
            assert_eq!(
                root.descendants()
                    .filter(|node| node.kind() == SyntaxKind::Error)
                    .count(),
                expected_error,
                "{source:?}"
            );
            assert_eq!(
                root.descendants()
                    .filter(|node| node.kind() == SyntaxKind::Missing)
                    .count(),
                expected_missing,
                "{source:?}: {root:#?}"
            );
        }
    }
}

#[test]
fn normalized_pattern_closes_each_nested_owner_before_handing_off_a_boundary() {
    let fence = active_fence();
    for (accepted, owner, expected_missing) in [
        ("> > (A", SyntaxKind::ParenthesizedPattern, 1),
        ("> > [A", SyntaxKind::ListPattern, 1),
        ("> > [..", SyntaxKind::ListPattern, 2),
        ("> > {a:", SyntaxKind::RecordPattern, 2),
        ("> > {..", SyntaxKind::RecordPattern, 2),
        ("> > {a =", SyntaxKind::RecordPattern, 2),
    ] {
        for (suffix, expected_remainder, expected_line_entry) in [
            (
                "\n> > ```\nouter",
                "> > ```\nouter",
                LineEntry::PhysicalStart,
            ),
            ("\r\n> ]\r\nouter", "> ]\r\nouter", LineEntry::PhysicalStart),
            ("", "", LineEntry::InLine),
        ] {
            let source = format!("{accepted}{suffix}");
            let (green, exit, remainder) = run_pattern_normalized(
                &source,
                3600,
                LineEntry::PhysicalStart,
                Some(&fence),
                PATTERN_DEFAULT_STOPS,
            );
            let NormalizedExit::Complete(Err(Either::Left(boundary)), line_entry) = exit else {
                panic!("nested Pattern must hand the boundary upward: {source:?}")
            };
            let root = SyntaxNode::new_root(green);

            assert_eq!(line_entry, expected_line_entry, "{source:?}");
            assert!(boundary.payload_view().is_boundary(), "{source:?}");
            assert_eq!(remainder, expected_remainder, "{source:?}");
            assert_eq!(root.to_string(), accepted, "{source:?}");
            assert_eq!(
                root.descendants()
                    .filter(|node| node.kind() == owner)
                    .count(),
                1,
                "{source:?}"
            );
            assert_eq!(
                root.descendants()
                    .filter(|node| node.kind() == SyntaxKind::Missing)
                    .count(),
                expected_missing,
                "{source:?}: {root:#?}"
            );
        }
    }
}

#[test]
fn normalized_pattern_streams_quote_prefixes_and_advances_past_symbol_names() {
    let fence = active_fence();
    let accepted = "> > [:symbol,\n> > next]";
    let source = format!("{accepted}\n> > ```\nouter");
    let origin = 3700;
    let (green, exit, remainder) = run_pattern_normalized(
        &source,
        origin,
        LineEntry::PhysicalStart,
        Some(&fence),
        PATTERN_DEFAULT_STOPS,
    );
    let NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart) = exit
    else {
        panic!("the list Pattern must return the following fence boundary")
    };
    let root = SyntaxNode::new_root(green);

    assert_eq!(root.to_string(), accepted);
    assert_eq!(remainder, "> > ```\nouter");
    assert_eq!(
        root.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::YmQuotePrefix)
            .count(),
        2
    );
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::SymbolPattern)
            .count(),
        1
    );
    let (leading, pending) = emit_terminal_leading_text(boundary);
    assert_eq!(leading, "\n");
    assert_eq!(pending.coordinate(), origin + accepted.len() + 1);
}

#[test]
fn normalized_pattern_annotation_enters_the_mandatory_type_body() {
    let fence = active_fence();
    let accepted = "> > value: Pair Int";
    let source = format!("{accepted}\n> > ```\nouter");
    let (green, exit, remainder) = run_pattern_normalized(
        &source,
        3750,
        LineEntry::PhysicalStart,
        Some(&fence),
        PATTERN_DEFAULT_STOPS,
    );
    let line_entry = match exit {
        NormalizedExit::Complete(Err(Either::Left(_)), line_entry) => line_entry,
        NormalizedExit::Complete(Ok(()), line_entry) => {
            panic!("annotation returned Ok at {line_entry:?}")
        }
        NormalizedExit::Complete(Err(Either::Right(_)), line_entry) => {
            panic!("annotation returned End at {line_entry:?}")
        }
        NormalizedExit::Deferred(_, line_entry) => {
            panic!("annotation deferred at {line_entry:?}")
        }
    };
    let root = SyntaxNode::new_root(green);

    assert_eq!(root.to_string(), accepted);
    assert_eq!(remainder, "> > ```\nouter");
    assert_eq!(line_entry, LineEntry::PhysicalStart);
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::PatternTypeAnnotation)
            .count(),
        1
    );
    assert!(
        root.descendants()
            .any(|node| node.kind() == SyntaxKind::TypeExpression)
    );
    assert!(
        root.descendants()
            .all(|node| !matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Missing))
    );
}

#[test]
fn normalized_pattern_record_defaults_parse_all_expression_owners() {
    let fence = active_fence();
    let accepted = "> > {a = 1}";
    let source = format!("{accepted}\n> > ```\nouter");
    let (green, exit, remainder) = run_pattern_normalized(
        &source,
        3800,
        LineEntry::PhysicalStart,
        Some(&fence),
        PATTERN_DEFAULT_STOPS,
    );
    assert!(matches!(
        exit,
        NormalizedExit::Complete(Err(Either::Left(_)), LineEntry::PhysicalStart)
    ));
    let root = SyntaxNode::new_root(green);
    assert_eq!(root.to_string(), accepted);
    assert_eq!(remainder, "> > ```\nouter");
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::OperatorChain)
            .count(),
        1
    );
    assert!(
        root.descendants()
            .all(|node| !matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Missing))
    );

    for (expression, owner) in [
        ("case x: n -> y", SyntaxKind::CaseExpression),
        ("if x: y", SyntaxKind::IfExpression),
    ] {
        let accepted = format!("> > {{a = {expression}}}");
        let source = format!("{accepted}\n> > ```\nouter");
        let (green, exit, remainder) = run_pattern_normalized(
            &source,
            3900,
            LineEntry::PhysicalStart,
            Some(&fence),
            PATTERN_DEFAULT_STOPS,
        );
        assert!(matches!(
            exit,
            NormalizedExit::Complete(Err(Either::Left(_)), LineEntry::PhysicalStart)
        ));
        let root = SyntaxNode::new_root(green);
        assert_eq!(root.to_string(), accepted);
        assert_eq!(remainder, "> > ```\nouter");
        assert!(root.descendants().any(|node| node.kind() == owner));
        assert!(
            root.descendants()
                .all(|node| !matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Missing)),
            "{expression:?}"
        );
    }

    let source = "> > {a = { tail";
    let (green, exit, remainder) = run_pattern_normalized(
        source,
        4000,
        LineEntry::PhysicalStart,
        Some(&fence),
        PATTERN_DEFAULT_STOPS,
    );
    let NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::InLine) = exit else {
        panic!("record default must enter the braced statement owner")
    };
    let root = SyntaxNode::new_root(green);
    assert!(boundary.payload_view().is_boundary());
    assert_eq!(remainder, "");
    assert_eq!(root.to_string(), source);
    assert!(
        root.descendants()
            .any(|node| node.kind() == SyntaxKind::Missing)
    );
}
