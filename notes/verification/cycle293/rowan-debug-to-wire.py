"""Read the project's versioned Rowan golden fixture (or compatible exact dump).

This debug format is not asserted to be a stable Rust API. Token bytes come
from validated ranges in a separate source file, not from unescaping Debug.
"""
import argparse
import json
from pathlib import Path
import re

LINE = re.compile(r'( *)([A-Za-z][A-Za-z0-9]*)@(\d+)\.\.(\d+)(?: (".*"))?')
TEST = "role_method_signature_where_keeps_its_pre_wp17_recovery_cst"

def convert(source: bytes, lines: str):
    nodes = []
    root = None
    for nr, line in enumerate(lines.splitlines(),1):
        if not line:
            raise ValueError(f"empty line {nr}")
        m = LINE.fullmatch(line)
        if not m or len(m[1]) % 2:
            raise ValueError(f"unsupported debug format at line {nr}")
        depth = len(m[1])//2
        label, low, high, quoted = m[2], int(m[3]), int(m[4]), m[5]
        if low > high or high > len(source):
            raise ValueError(f"out-of-bounds range at line {nr}")
        # Validate that range boundaries are UTF-8 boundaries even for nodes.
        sample = source[low:high].decode("utf-8")
        if quoted is not None:
            try:
                if json.loads(quoted) != sample:
                    raise ValueError(f"token spelling disagrees with bytes at line {nr}")
            except json.JSONDecodeError as exc:
                raise ValueError(f"unsupported token escape at line {nr}") from exc
            wire=["token",label,sample]
        else:
            wire=["node",label,[]]
        if not depth:
            if root is not None or label != "Root" or quoted is not None or (low,high)!=(0,len(source)):
                raise ValueError("expected exactly one Root covering the supplied source")
            root=(wire,low,high,[])
        else:
            if depth > len(nodes):
                raise ValueError(f"skipped nesting at line {nr}")
            parent=nodes[depth-1]
            if parent[0][0]!="node":
                raise ValueError(f"token cannot own a child at line {nr}")
            parent[3].append((wire,low,high,[]))
            parent[0][2].append(wire)
        item=root if not depth else nodes[depth-1][3][-1]
        nodes[depth:]=[item]
    if root is None:
        raise ValueError("missing root")
    agenda=[root]
    while agenda:
        wire,lo,hi,children=agenda.pop()
        if wire[0]=="token":
            continue
        position=lo
        for child in children:
            if child[1]!=position or child[2]>hi:
                raise ValueError(f"child ranges do not partition {wire[1]}@{lo}..{hi}")
            position=child[2]
        if position!=hi:
            raise ValueError(f"uncovered bytes in {wire[1]}@{lo}..{hi}")
        agenda.extend(children)
    return root[0]

def recorded(test_file: Path):
    text=test_file.read_text()
    target=text.split("fn "+TEST+"() {",1)[1]
    # The committed source literal in this one fixture uses JSON-compatible escapes.
    captured=re.search(r'let source = (".*?");',target)
    if not captured:
        raise ValueError("golden source not found")
    source=json.loads(captured[1]).encode("utf-8")
    gold=target.split('r#"Root@',1)[1].split('"#',1)[0]
    return source,"Root@"+gold

if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    mode=p.add_mutually_exclusive_group(required=True)
    mode.add_argument("--golden",type=Path)
    mode.add_argument("--debug",type=Path)
    p.add_argument("--source",type=Path)
    a=p.parse_args()
    if a.golden:
        data,dump=recorded(a.golden)
    else:
        if a.source is None:
            p.error("--debug needs --source")
        data,dump=a.source.read_bytes(),a.debug.read_text()
    print(json.dumps(convert(data,dump),ensure_ascii=False,separators=(",",":")))
