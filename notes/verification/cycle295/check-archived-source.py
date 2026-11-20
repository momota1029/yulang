"""Independently read exact source ranges and original archived family tags."""
import importlib.util
import json
from pathlib import Path

repo = Path(__file__).resolve().parents[3]
older = repo / "notes/verification/cycle293"
spec = importlib.util.spec_from_file_location("rowan", older / "rowan-debug-to-wire.py")
reader = importlib.util.module_from_spec(spec)
spec.loader.exec_module(reader)
rust = repo / "crates/yu-syntax/src/tests/declaration/act_decl/operation_where.rs"
source, dump = reader.recorded(rust)
wire = json.loads((older / "recorded-rust-cst.json").read_text())
assert reader.convert(source, dump) == wire


def width(w):
    return len(w[2].encode("utf-8")) if w[0] == "token" else sum(map(width, w[2]))


def locate(w, path):
    offset = 0
    for child in path:
        assert w[0] == "node"
        offset += sum(map(width, w[2][:child]))
        w = w[2][child]
    return w, (offset, offset + width(w))


for path, kind, span in [
    ([0], "RoleDeclaration", (0, 49)),
    ([0, 2], "TypeExpression", (5, 9)),
    ([0, 4, 2, 0], "BindingStatement", (15, 49)),
    ([1], "Error", (49, 50)),
    ([2], "Error", (50, 51)),
    ([3], "Error", (51, 58)),
]:
    w, expected = locate(wire, path)
    assert (w[1], expected) == (kind, span)
    print(f"{path}: {kind} {span[0]}..{span[1]}")

assert source[5:9] == b"a 'x"
assert source[49:58] == b": Display"
role_body, _ = locate(wire, [0, 4])
children = [c for c in role_body[2] if c[0] == "node"]
assert [c[1] for c in children] == ["Statement"]
actual_members = [c[1] for c in children[0][2] if c[0] == "node"]
assert actual_members == ["BindingStatement"]
print("One direct method and no associated type; nothing here assigns a semantic role ID.")
print("Archived Rust source replay only; raw offsets independently confirmed.")
