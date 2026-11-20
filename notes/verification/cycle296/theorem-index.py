"""Emit the exact source signatures audited in cycle 296."""
from pathlib import Path
import re

repo = Path(__file__).resolve().parents[3]
audits = sorted((repo / "lean/Audit").glob("Cycle296*.lean"))
names = []
for p in audits:
    source = p.read_text()
    assert not re.search(r"(?m)^import (?!Yulang\.)", source), p
    names.extend(re.findall(r"(?m)^#print axioms (\S+)", source))
assert len(set(names)) == len(names)
all_theorems = set()
print("# Cycle 296: complete theorem / audit index")
print("\nExact Lean source signatures; Japanese summaries are in the cycle report.\n")
for p in sorted((repo / "lean/Yulang").glob("GeneralSourceRoleCst*296.lean")):
    source = p.read_text()
    namespace = re.search(r"(?m)^namespace (\S+)", source)[1]
    declarations = re.findall(r"(?ms)^theorem (\w+)(.*?)(?=\s*:=)", source)
    assert declarations, p
    print(f"## `{p.relative_to(repo)}`\n")
    for name, signature in declarations:
        all_theorems.add(namespace + "." + name)
        print(f"```lean\ntheorem {name}{signature.rstrip()}\n```\n")
assert all_theorems == set(names), (all_theorems - set(names), set(names) - all_theorems)
print(f"Indexed {len(all_theorems)} theorem declarations; every one appears in exactly one standalone audit.")
