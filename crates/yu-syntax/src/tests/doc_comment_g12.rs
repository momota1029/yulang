use std::sync::Arc;

use crate::{SourceText, SyntaxEnvironment, SyntaxNode};

#[test]
fn undeclared_marker_after_operator_preserves_baseline_cst() {
    let source: Arc<SourceText> = Arc::from("infix (+) 5.0.0 5.0.1 = add\nmy a = 1 + -- c\n    2");
    let parsed = crate::parse_file(
        source.clone(),
        Arc::new(crate::scan_header(source.clone())),
        Arc::new(SyntaxEnvironment::empty()),
    );
    assert_eq!(parsed.green().to_string(), source.to_string());
    let tree = SyntaxNode::new_root(parsed.green().clone());
    assert_eq!(
        format!("{tree:#?}"),
        r#"Root@0..49
  OperatorHeader@0..23
    InfixKw@0..5 "infix"
    Whitespace@5..6 " "
    OperatorName@6..9
      LParen@6..7 "("
      Operator@7..8 "+"
      RParen@8..9 ")"
    Whitespace@9..10 " "
    BindingPower@10..15
      Integer@10..11 "5"
      Dot@11..12 "."
      Integer@12..13 "0"
      Dot@13..14 "."
      Integer@14..15 "0"
    Whitespace@15..16 " "
    BindingPower@16..21
      Integer@16..17 "5"
      Dot@17..18 "."
      Integer@18..19 "0"
      Dot@19..20 "."
      Integer@20..21 "1"
    Whitespace@21..22 " "
    Equals@22..23 "="
  Whitespace@23..24 " "
  OperatorChain@24..27
    IdentifierExpression@24..27
      Identifier@24..27 "add"
  Newline@27..28 "\n"
  BindingStatement@28..49
    BindingHeader@28..34
      MyKw@28..30 "my"
      Whitespace@30..31 " "
      Pattern@31..32
        IdentifierPattern@31..32
          Identifier@31..32 "a"
      Whitespace@32..33 " "
      Equals@33..34 "="
    BindingBody@34..49
      Whitespace@34..35 " "
      OperatorChain@35..49
        IntegerLiteral@35..36
          Integer@35..36 "1"
        InfixOperatorUse@36..38
          Whitespace@36..37 " "
          Operator@37..38 "+"
        Whitespace@38..39 " "
        Error@39..40 "-"
        Error@40..41 "-"
        IdentifierExpression@41..43
          Whitespace@41..42 " "
          Identifier@42..43 "c"
        Newline@43..44 "\n"
        Whitespace@44..48 "    "
        MlArgument@48..49
          OperatorChain@48..49
            IntegerLiteral@48..49
              Integer@48..49 "2"
"#
    );
}

fn parse(source: &str) -> crate::ParsedFile {
    let source: Arc<SourceText> = Arc::from(source);
    crate::parse_file(
        source.clone(),
        Arc::new(crate::scan_header(source)),
        Arc::new(SyntaxEnvironment::empty()),
    )
}

fn clean(source: &str) -> SyntaxNode {
    let parsed = parse(source);
    assert_eq!(parsed.green().to_string(), source);
    assert!(
        parsed.structural_recoveries().is_empty(),
        "{source:?}: {:#?}\n{:#?}",
        parsed.structural_recoveries(),
        SyntaxNode::new_root(parsed.green().clone())
    );
    SyntaxNode::new_root(parsed.green().clone())
}

#[test]
fn binding_line_docs_are_direct_children_in_source_order() {
    use crate::SyntaxKind::*;
    for source in [
        "my g x = x   -- doc",
        "infix (+) 5.0.0 5.0.1 = add\nmy h x = -- doc\n    x + 1",
        "my a = f x  -- doc\n",
        "our a = 1 -- doc\n",
        "pub a = 1 -- doc\r\n",
        "my a = 1; my b = 2 -- doc\n",
        "infix (-) 5.0.0 5.0.1 = sub\nmy a = 1 -- doc\n",
    ] {
        let tree = clean(source);
        let docs: Vec<_> = tree
            .descendants()
            .filter(|n| n.kind() == DocCommentDeclaration)
            .collect();
        assert_eq!(docs.len(), 1, "{source:?}");
        let doc = &docs[0];
        let owner = doc.parent().unwrap();
        assert_eq!(owner.kind(), BindingStatement, "{tree:#?}");
        let owner_start: usize = owner.text_range().start().into();
        let doc_start: usize = doc.text_range().start().into();
        assert!(!source[owner_start..doc_start].contains('\n'), "{source:?}");
        assert!(
            owner
                .text()
                .to_string()
                .starts_with(if source.contains("my b") {
                    "my b"
                } else if source.starts_with("our") {
                    "our a"
                } else if source.starts_with("pub") {
                    "pub a"
                } else if source.contains("my h") {
                    "my h"
                } else if source.contains("my g") {
                    "my g"
                } else {
                    "my a"
                })
        );
    }
}

#[test]
fn binding_keeps_leading_and_trailing_docs_in_order() {
    use crate::SyntaxKind::*;
    let tree = clean("-- leading\nmy a = 1 -- trailing\n");
    let docs: Vec<_> = tree
        .descendants()
        .filter(|n| n.kind() == DocCommentDeclaration)
        .collect();
    assert_eq!(docs.len(), 2);
    assert_eq!(docs[0].parent().unwrap().kind(), Root);
    assert_eq!(docs[1].parent().unwrap().kind(), BindingStatement);
    assert!(docs[0].text().to_string().contains("leading"));
    assert!(docs[1].text().to_string().contains("trailing"));
}

#[test]
fn continuation_and_nested_argument_markers_are_not_attached() {
    use crate::SyntaxKind::*;
    for source in [
        "my a = f\n    x -- doc\n",
        "my a = f(x -- doc)\n",
        "my a = f\n    -- doc\n    x\n",
        "my a = 1 --- doc\n",
    ] {
        let parsed = parse(source);
        assert_eq!(parsed.green().to_string(), source);
        let tree = SyntaxNode::new_root(parsed.green().clone());
        assert_eq!(
            tree.descendants()
                .filter(|n| n.kind() == DocCommentDeclaration)
                .count(),
            0,
            "{source:?}\n{tree:#?}"
        );
    }
}

#[test]
fn struct_field_docs_keep_their_owners_across_commas() {
    use crate::SyntaxKind::*;
    let source = "struct point {\n    x: int,   -- x\n    -- y\n    y: int,\n}";
    let tree = clean(source);
    let docs: Vec<_> = tree
        .descendants()
        .filter(|n| n.kind() == DocCommentDeclaration)
        .collect();
    assert_eq!(docs.len(), 2);
    assert_eq!(docs[0].parent().unwrap().kind(), StructField);
    assert!(
        docs[0]
            .parent()
            .unwrap()
            .text()
            .to_string()
            .starts_with("x:")
    );
    assert_eq!(docs[1].next_sibling().unwrap().kind(), StructField);
    assert!(
        docs[1]
            .next_sibling()
            .unwrap()
            .text()
            .to_string()
            .starts_with("y:")
    );
}

#[test]
fn enum_role_and_act_member_line_docs_have_the_member_as_owner() {
    use crate::SyntaxKind::*;
    for (source, kind, name) in [
        (
            "enum shape:\n    circle(float)\n    square(float)   -- doc\n",
            EnumVariant,
            "square",
        ),
        (
            "enum E {\n    -- leading\n    A -- trailing\n}",
            EnumVariant,
            "A",
        ),
        (
            "role R:\n    -- leading\n    pub show: T -- trailing\n",
            BindingStatement,
            "pub show",
        ),
        (
            "act A:\n    -- leading\n    pub run: T -- trailing\n",
            BindingStatement,
            "pub run",
        ),
        (
            "role R {\n    pub show: T -- trailing\n}",
            BindingStatement,
            "pub show",
        ),
        (
            "act A {\n    pub run: T -- trailing\n}",
            BindingStatement,
            "pub run",
        ),
        (
            "role R:\n    pub show x = -- doc\n        x\n",
            BindingStatement,
            "pub show",
        ),
        (
            "act A:\n    pub run x = -- doc\n        x\n",
            BindingStatement,
            "pub run",
        ),
    ] {
        let tree = clean(source);
        let docs: Vec<_> = tree
            .descendants()
            .filter(|n| n.kind() == DocCommentDeclaration)
            .collect();
        let doc = docs.last().unwrap();
        let member = doc.parent().unwrap();
        assert_eq!(member.kind(), kind, "{tree:#?}");
        assert!(
            member.text().to_string().trim_start().starts_with(name),
            "{tree:#?}"
        );
        if source.contains("leading") {
            assert_eq!(docs.len(), 2);
            assert!(docs[0].text_range().end() <= docs[1].text_range().start());
            let leading = if docs[0].parent().unwrap().kind() == Statement {
                docs[0].parent().unwrap()
            } else {
                docs[0].clone()
            };
            let mut next = leading.next_sibling().unwrap();
            while next.kind() == BlockStatementSeparator {
                next = next.next_sibling().unwrap();
            }
            assert!(
                next == member || next.descendants().any(|n| n == member),
                "{tree:#?}"
            );
        }
    }
}

#[test]
fn field_defaults_take_after_equals_and_trailing_docs() {
    use crate::SyntaxKind::*;
    for source in [
        "struct S {\n    x: int = -- doc\n        1\n}",
        "struct S {\n    x: int = 1, -- doc\n    y: int = 2,\n}",
    ] {
        let tree = clean(source);
        let doc = tree
            .descendants()
            .find(|n| n.kind() == DocCommentDeclaration)
            .unwrap();
        assert_eq!(doc.parent().unwrap().kind(), StructField, "{tree:#?}");
        assert!(doc.parent().unwrap().text().to_string().starts_with("x:"));
    }
}

#[test]
fn documented_examples_keep_later_declarations_and_members() {
    use crate::SyntaxKind::*;
    let reference_example = concat!(
        "-- leading\n",
        "my g x = x -- trailing\n",
        "my h x = -- after equals\n",
        "    x\n",
        "struct point {\n",
        "    x: int, -- x\n",
        "    -- y\n",
        "    y: int,\n",
        "}\n",
    );
    let tree = clean(reference_example);
    assert_eq!(
        tree.descendants()
            .filter(|n| n.kind() == DocCommentDeclaration)
            .count(),
        5
    );
    assert_eq!(
        tree.descendants()
            .filter(|n| n.kind() == BindingStatement)
            .count(),
        2
    );
    assert_eq!(
        tree.descendants()
            .filter(|n| n.kind() == StructField)
            .count(),
        2
    );

    for source in [
        "role R:\n    -- first\n    -- second\n    pub one: T -- one\n    -- next\n    pub two x = x -- two\n",
        "act A {\n    -- first\n    -- second\n    pub one: T -- one\n    -- next\n    pub two x = x -- two\n}\n",
    ] {
        let tree = clean(source);
        assert_eq!(
            tree.descendants()
                .filter(|n| n.kind() == BindingStatement)
                .count(),
            2
        );
        let docs: Vec<_> = tree
            .descendants()
            .filter(|n| n.kind() == DocCommentDeclaration)
            .collect();
        assert_eq!(docs.len(), 5);
        for (doc, name) in [(&docs[2], "pub one"), (&docs[4], "pub two")] {
            assert_eq!(doc.parent().unwrap().kind(), BindingStatement);
            assert!(doc.parent().unwrap().text().to_string().starts_with(name));
            let start: usize = doc.parent().unwrap().text_range().start().into();
            let end: usize = doc.text_range().start().into();
            assert!(!source[start..end].contains('\n'));
        }
    }
}
