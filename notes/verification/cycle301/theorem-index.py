"""Emit exact signatures or standalone audit commands for cycle 301."""
from pathlib import Path
import re
import sys

repo = Path(__file__).resolve().parents[3]

def signature_end(tail):
    # Ignore assignments in record literals, named arguments, and explicit
    # local let binders in a theorem type. The first top-level proof delimiter
    # can introduce a tactic block or any same-line Lean proof term.
    stack = []
    closing = {"(": ")", "[": "]", "{": "}", "⟨": "⟩", "⦃": "⦄"}
    for i, c in enumerate(tail):
        if c in closing:
            stack.append(closing[c])
        elif stack and c == stack[-1]:
            stack.pop()
        elif not stack and tail.startswith(":=", i):
            before = tail[:i].rsplit("\n", 1)[-1].lstrip()
            if not before.startswith("let "):
                return i
    raise ValueError("Could not find the proof delimiter")

def declarations(path):
    source = path.read_text()
    stack = []
    sem = r"^namespace (\S+)|^end (\S+)|^theorem (\w+)"
    for match in re.finditer(sem, source, re.M):
        opened, ended, name = match.groups()
        if opened:
            stack.append(opened)
        elif ended:
            assert stack and stack.pop() == ended, (path, ended)
        else:
            tail = source[match.end():]
            yield ".".join([*stack, name]), tail[:signature_end(tail)].strip()

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
    for p in sorted((repo / "lean/Yulang").glob("*301.lean")):
        index[p] = list(declarations(p))
        assert index[p], p
    audited = []
    for p in sorted((repo / "lean/Audit").glob("Cycle301*.lean")):
        text = p.read_text()
        assert not re.search(r"(?m)^import (?!Yulang\.)", text), p
        audited.extend(re.findall(r"(?m)^#print axioms (\S+)", text))
    expected = [name for ds in index.values() for name, _ in ds]
    assert len(audited) == len(set(audited))
    assert set(expected) == set(audited), (set(expected) - set(audited), set(audited) - set(expected))
    print("# Cycle 301: exact theorem signatures")
    for p, ds in index.items():
        print(f"\n## {p.relative_to(repo)}\n")
        for name, signature in ds:
            print(f"```lean\ntheorem {name} {signature}\n```\n")
    print(f"Indexed {len(audited)} theorem declarations. Each has one standalone audit.")

if __name__ == "__main__":
    main()
