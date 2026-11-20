"""Versioned golden-to-wire converter controls; no Rust execution."""
import importlib.util
from pathlib import Path

here=Path(__file__).resolve().parent
root=here.parents[2]
loader=importlib.util.spec_from_file_location("gold",here/"rowan-debug-to-wire.py")
module=importlib.util.module_from_spec(loader)
loader.loader.exec_module(module)
convert=module.convert
source,golden=module.recorded(root/"crates/yu-syntax/src/tests/declaration/act_decl/operation_where.rs")
wire=convert(source,golden)
assert len(source)==59 and source[15:49].startswith(b"our log:")
role=wire[2][0]
argument=role[2][2][2][1]
assert role[1]=="RoleDeclaration" and argument[1]=="TypeApplyArgument"
assert argument[2][-1][1]=="TypeExpression"
print("exact checked-in 59-byte Rowan snapshot, actual wrapped binder confirmed")

def reject(dump, expected):
    try:
        convert(source,dump)
    except ValueError as e:
        assert expected in str(e),e
    else:
        raise AssertionError("unexpectedly accepted corrupt dump")

reject(golden.replace('RoleKw@0..4 "role"','RoleKw@0..4 "nope"'),"spelling disagrees")
reject(golden.replace('Root@0..59','Root@0..60',1),"out-of-bounds")
line=next(l for l in golden.splitlines() if 'Whitespace@11..15' in l)
reject(golden.replace(line+'\n','',1),"partition")
reject(golden.replace('  RoleDeclaration@','    RoleDeclaration@',1),"skipped nesting")
print("forged token text, oversized range, dropped trivia, and invalid nesting rejected")
assert convert("型".encode(),'Root@0..3\n  Identifier@0..3 "型"\n')[2]==[["token","Identifier","型"]]
assert convert(b'','Root@0..0\n  Missing@0..0\n')[2]==[["node","Missing",[]]]
print("UTF-8 byte token and zero-width recovery controls preserved")
