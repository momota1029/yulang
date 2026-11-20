"""Check the source-level reason not to equate a diagnostic ID with ownership."""
from pathlib import Path
import subprocess

repo = Path(__file__).resolve().parents[3]
rust = repo / "crates/yu-syntax/src"


def pinned_file(n, want):
    path = rust / n
    b = path.read_bytes()
    oid = subprocess.check_output(["git", "hash-object", path], text=True).strip()
    assert oid == want, (path, oid)
    return b.decode()


full = pinned_file("full_parse.rs", "e6573b9469b45c38c7d802d012520ec8bbf9c90b")
assert "pub fn green(&self) -> &GreenNode" in full
assert "pub fn syntax_diagnostics(&self) -> Result<Vec<SyntaxDiagnostic>, SyntaxDiagnosticError>" in full
assert "let root = crate::SyntaxNode::new_root(parsed.green.clone());" in full
assert "conflicting_local_operators(&parsed.operators, parsed.header.operators())" in full

structural = pinned_file("structural_diagnostic.rs", "a125d90461f9b9e2f5b8227787bc75d234fc7649")
depth = structural.split("if kind == SyntaxKind::NestingTooDeep {", 1)[1].split("continue;", 1)[0]
assert "let range = byte_range(child.text_range());" in depth
assert "occurrence_path.push(index as u32);" in depth
assert "occurrence_path,\n                            0," in depth
flush = structural.split("fn flush(", 1)[1].split("fn push(", 1)[0]
assert "if let Some((range, index)) = run.take()" in flush
assert "occurrence_path,\n                index," in flush
emit = structural.split("fn push(", 1)[1]
assert "let mut occurrence_path = parent_occurrence_path.to_vec();" in emit
assert "u32::try_from(child_index)" in emit

print("Retained ParsedFile has fallible syntax diagnostics and green wire; diagnostics use operator environment.")
print("Plain token run identity appends the first raw token ordinal.")
print("NestingTooDeep identity appends literal 0 after the opaque node path; its range belongs to the node.")
print("Exact source anchors, not a Rust execution or proof of every diagnostic ownership shape.")
