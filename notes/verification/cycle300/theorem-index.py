"""Emit exact signatures or standalone audit commands for cycle 300."""
from pathlib import Path
import re
import sys

repo = Path(__file__).resolve().parents[3]

def declarations(path):
    source = path.read_text()
    # Every proof body here is indented; top-level namespaces may be nested.
    stack = []
    # The declarations below use ":= by", ":= rfl", or a newline before
    # their proof terms. Do not mistake a let binding in the type for the
    # proof delimiter.
    sem = r"^namespace (\S+)|^end (\S+)|^theorem (\w+)(.*?)(?=\s*:=[ \t]*(?:by\b|rfl\b|\n))"
    for opened, ended, name, signature in re.findall(sem, source, re.M | re.S):
        if opened:
            stack.append(opened)
        elif ended:
            assert stack and stack.pop() == ended, (path, ended)
        else:
            yield ".".join([*stack, name]), signature.strip()

def main():
    if len(sys.argv) > 1:
        files = [repo / "lean/Yulang" / f"{name}.lean" for name in sys.argv[1:]]
        for p in files:
            print(f"import Yulang.{p.stem}")
        print()
        for p in files:
            for name, _ in declarations(p):
                print(f"#print axioms {name}")
        return
    index = {}
    for p in sorted((repo / "lean/Yulang").glob("*300.lean")):
        index[p] = list(declarations(p))
        assert index[p], p
    audited = []
    for p in sorted((repo / "lean/Audit").glob("Cycle300*.lean")):
        text = p.read_text()
        assert not re.search(r"(?m)^import (?!Yulang\.)", text), p
        audited.extend(re.findall(r"(?m)^#print axioms (\S+)", text))
    expected = [name for ds in index.values() for name, _ in ds]
    assert len(audited) == len(set(audited))
    assert set(expected) == set(audited), (set(expected) - set(audited), set(audited) - set(expected))
    print("# Cycle 300: exact theorem signatures")
    for p, ds in index.items():
        print(f"\n## {p.relative_to(repo)}\n")
        for name, signature in ds:
            print(f"```lean\ntheorem {name} {signature}\n```\n")
    print(f"Indexed {len(audited)} theorem declarations. Each has one standalone audit.")

if __name__ == "__main__":
    main()
