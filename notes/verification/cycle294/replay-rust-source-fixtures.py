"""Recover three checked-in CST fixtures verbatim; never launches Rust."""
import importlib.util
import json
import re
import subprocess
import sys
from pathlib import Path

here = Path(__file__).resolve().parent
repo = here.parents[2]
saved = here.parent / "cycle293"
reader = importlib.util.spec_from_file_location("gold", saved / "rowan-debug-to-wire.py")
helper = importlib.util.module_from_spec(reader)
reader.loader.exec_module(helper)
baseline = next(ref for ref in ("adf9fae11d8e29273a28751089db2499bcf205d2",
                                  "6972cc6221bb238ee79a96d3f868e25cda6b931c")
                if subprocess.run(["git", "cat-file", "-e", ref + "^{commit}"], cwd=repo,
                                  stderr=subprocess.DEVNULL).returncode == 0)


def checked_source(name):
    rel = "crates/yu-syntax/src/tests/" + name
    local = (repo / rel).read_bytes()
    upstream = subprocess.check_output(["git", "show", baseline + ":" + rel], cwd=repo)
    assert local == upstream
    oid = subprocess.check_output(["git", "rev-parse", baseline + ":" + rel], cwd=repo, text=True).strip()
    print(f"{rel} blob {oid}")
    return local.decode()


def test_section(text, name):
    return text.split("fn " + name + "() {", 1)[1].split("\n}\n", 1)[0]


role = "declaration/act_decl/operation_where.rs"
checked_source(role)
source, cst = helper.recorded(repo / "crates/yu-syntax/src/tests" / role)
converted = helper.convert(source, cst)
assert converted == json.loads((saved / "recorded-rust-cst.json").read_text())
print("Role fixture: exactly the prior independently recorded Rust CST JSON.")

case = test_section(checked_source("case_like.rs"), "case_head_unchanged_recovery_fixtures")
quoted, case_dump = re.search(r'("(?:[^"\\]|\\.)*")\s*,\s*r#"(Root@.*?)"#', case, re.S).groups()
assert quoted == '"case"'
assert "assert!(!parsed.structural_recoveries().is_empty())" in case
case_wire = helper.convert(json.loads(quoted).encode(), case_dump)
assert case_dump.count("Missing@4..4") == 2

for_stmt = test_section(checked_source("expression_recovery.rs"),
                        "actual_for_inline_body_missing_and_error_preserve_cst_and_handoff")
assert re.search(r'"for x in xs: @"\s*,\s*StructuralKind::ErrorGroup,\s*13\.\.14,', for_stmt)
assert 'assert_eq!(facts, [(kind, range.clone())]);' in for_stmt
nested_source = b"for x in xs: @"
text = for_stmt.split("concat!(", 1)[1].split("),", 1)[0]
literals = re.findall(r'"(?:[^"\\]|\\.)*"', text)
template = "".join(json.loads(s) for s in literals)
assert re.search(r'StructuralKind::ErrorGroup => ("(?:[^"\\]|\\.)*")', for_stmt)
error_line = json.loads(re.search(r'StructuralKind::ErrorGroup => ("(?:[^"\\]|\\.)*")', for_stmt)[1])
nested = template.format(end=14, expected_body=error_line)
nested_wire = helper.convert(nested_source, nested)

assert len(sys.argv) == 2
out = Path(sys.argv[1])
out.mkdir(parents=True, exist_ok=True)
for name, wire in [("recorded-case-missing", case_wire), ("recorded-for-error", nested_wire)]:
    (out / f"{name}.json").write_text(json.dumps(wire, ensure_ascii=False, separators=(",", ":")) + "\n")
print("Rust tests record two equal-range Missing nodes and a nested raw Error token at 13..14.")
print("Exact dump extraction and byte partition checks completed, with no Rust runtime involved.")
