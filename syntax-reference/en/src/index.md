# yu-syntax reference

This is a working reference for people who implement and maintain Yulang3's `yu-syntax` parser.

Each page summarizes the grammar, CST, AST, and typed recovery contract from an Authoritative design section, then links that contract to implementation functions and regression fixtures. This reference does not define new grammar rules or recovery policy.

The authoritative source is `notes/design/2026-08-20-yu-syntax-chasa-architecture.md`. If this reference disagrees with that document or with the implementation, do not normalize the disagreement here: check the design document, implementation, and fixtures first.
